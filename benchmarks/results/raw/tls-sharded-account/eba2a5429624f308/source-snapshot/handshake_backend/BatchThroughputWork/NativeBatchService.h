#pragma once
#include "NativeWorker.h"
#include "../../signal_backend/VariableServiceWork/VariableShape.h"
namespace tls_mpc_worker {
// Public shape; independent same-profile instances only. Missing pinned closure
// fails closed. No store/state import or default provider is introduced here.
class VariableBatchShape {
 signal_mpc::VariableShape single_;size_t count_;
public:
 VariableBatchShape(signal_mpc::VariableShape single,size_t count):single_(single),count_(count){
  if(count<1||count>4)throw std::runtime_error("unsupported conversation batch count");
 }
 size_t count()const{return count_;}const auto& single()const{return single_;}
 size_t input_bits()const{return single_.input_bytes()*8*count_;}
 size_t output_bits()const{return single_.output_bytes()*8*count_;}
 std::string name()const{return "signal_private_variable_batch_"+std::to_string(count_)+"_"+single_.name();}
 std::string descriptor()const{return name()+"-sbv:["+std::to_string(input_bits())+"x1]-sbv:["+std::to_string(output_bits())+"x1]";}
};
class NativeBatchService {
 Machine<tls_mpc_worker::Share>& machine_;Worker& allocation_;const PinnedPrograms& pinned_;
public:
 NativeBatchService(Machine<tls_mpc_worker::Share>& machine,Worker& allocation,const PinnedPrograms& pinned):machine_(machine),allocation_(allocation),pinned_(pinned){}
 std::vector<Bits> evaluate(const std::vector<signal_mpc::VariableShape>& shapes,std::vector<Bits> inputs){
  if(shapes.empty()||shapes.size()!=inputs.size())throw std::runtime_error("invalid conversation batch dimensions");
  VariableBatchShape shape(shapes.front(),shapes.size());
  for(size_t i=0;i<inputs.size();++i)
   if(shapes[i].descriptor()!=shape.single().descriptor()||inputs[i].size()!=shape.single().input_bytes()*8)
    throw std::runtime_error("conversation batch shape mismatch");
  auto joined=allocation_.allocate(0);
  for(auto& input:inputs){joined.insert(joined.end(),input.begin(),input.end());input.clear();}
  auto output=allocation_.allocate(shape.output_bits());
  std::vector<FunctionArgument> args={{1,joined.function_argument()},{1,output.function_argument()}};
  pinned_.verify_function(shape.name(),args);FunctionArgument ignored;machine_.run_function(shape.name(),ignored,args);
  std::vector<Bits> result;result.reserve(shape.count());auto width=shape.single().output_bytes()*8;
  for(size_t i=0;i<shape.count();++i)result.emplace_back(output.begin()+i*width,output.begin()+(i+1)*width);
  return result; // Quarantined: caller must atomically commit ALL state first.
 }
};
}
