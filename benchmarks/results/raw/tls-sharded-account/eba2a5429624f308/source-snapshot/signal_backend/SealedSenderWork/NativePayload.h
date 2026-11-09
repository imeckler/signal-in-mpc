#pragma once
#include "NativeWorker.h"
#include "ServiceShape.h"
namespace signal_mpc {
// Pure typed representation adapter. It cannot turn non255 status into valid.
// For core+service composition, preserve the earlier computed status too.
class NativePayload {
 Machine<tls_mpc_worker::Share>& machine_;
 tls_mpc_worker::Worker& allocation_;
 const tls_mpc_worker::PinnedPrograms& pinned_;
public:
 NativePayload(Machine<tls_mpc_worker::Share>& machine,tls_mpc_worker::Worker& allocation,
  const tls_mpc_worker::PinnedPrograms& pinned):machine_(machine),allocation_(allocation),pinned_(pinned){}
 tls_mpc_worker::Bits wrap(const ServiceShape& shape,tls_mpc_worker::Bits service){
  const auto capacity=shape.output_bytes()-1;
  if(service.size()!=(capacity+1)*8)throw std::runtime_error("service result size mismatch");
  auto result=allocation_.allocate((capacity+3)*8);
  std::vector<FunctionArgument> args={{1,service.function_argument()},{1,result.function_argument()}};
  auto name="signal_service_payload_"+std::to_string(capacity);
  pinned_.verify_function(name,args);FunctionArgument ignored;machine_.run_function(name,ignored,args);return result;
 }
 // The complete output of the pinned inner-send stage, including its computed
 // status, is accepted here. Never replace it with a supplied "correct" flag.
 tls_mpc_worker::Bits after_inner(const ServiceShape& shape,tls_mpc_worker::Bits inner_result,
   tls_mpc_worker::Bits service){
  const auto capacity=shape.output_bytes()-1;
  if(inner_result.size()!=(73+shape.inner_bytes())*8 || service.size()!=(capacity+1)*8)
   throw std::runtime_error("computed inner/service result size mismatch");
  tls_mpc_worker::Bits input(inner_result.begin(),inner_result.begin()+8);
  inner_result.clear();input.insert(input.end(),service.begin(),service.end());
  auto result=allocation_.allocate((capacity+3)*8);
  std::vector<FunctionArgument> args={{1,input.function_argument()},{1,result.function_argument()}};
  auto name="signal_service_payload_after_"+std::to_string(capacity);
  pinned_.verify_function(name,args);FunctionArgument ignored;machine_.run_function(name,ignored,args);return result;
 }

};
}
