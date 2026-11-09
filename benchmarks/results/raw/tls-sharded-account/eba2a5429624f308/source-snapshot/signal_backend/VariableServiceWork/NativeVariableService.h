#pragma once
#include "NativeWorker.h"
#include "VariableShape.h"
namespace signal_mpc {
class NativeVariableService {
 Machine<tls_mpc_worker::Share>& machine_;tls_mpc_worker::Worker& allocation_;
 const tls_mpc_worker::PinnedPrograms& pinned_;
public:
 NativeVariableService(Machine<tls_mpc_worker::Share>& machine,tls_mpc_worker::Worker& allocation,
   const tls_mpc_worker::PinnedPrograms& pinned):machine_(machine),allocation_(allocation),pinned_(pinned){}
 tls_mpc_worker::Bits evaluate(const VariableShape& shape,tls_mpc_worker::Bits input){
  if(input.size()!=shape.input_bytes()*8)throw std::runtime_error("private conversation input size mismatch");
  auto output=allocation_.allocate(shape.output_bytes()*8);
  std::vector<FunctionArgument> args={{1,input.function_argument()},{1,output.function_argument()}};
  pinned_.verify_function(shape.name(),args);FunctionArgument ignored;machine_.run_function(shape.name(),ignored,args);return output;
 }
};
}
