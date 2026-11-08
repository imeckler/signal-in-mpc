#pragma once
#include "NativeWorker.h"
namespace signal_mpc {
// Internal composition only. This returns candidate receiving state and key;
// it MUST remain unopened and uncommitted until actual Signal MAC/decrypt
// succeeds. There is no RPC input, persistence commit or validity override.
class NativeActiveSpqrReceive {
 Machine<tls_mpc_worker::Share>& machine_;tls_mpc_worker::Worker& allocation_;
 const tls_mpc_worker::PinnedPrograms& pinned_;
public:
 NativeActiveSpqrReceive(Machine<tls_mpc_worker::Share>& machine,tls_mpc_worker::Worker& allocation,
  const tls_mpc_worker::PinnedPrograms& pinned):machine_(machine),allocation_(allocation),pinned_(pinned){}
 tls_mpc_worker::Bits prepare(tls_mpc_worker::Bits input){
  if(input.size()!=632)throw std::runtime_error("active SPQR receiving dimensions");
  auto output=allocation_.allocate(616);
  std::vector<FunctionArgument> args={{1,input.function_argument()},{1,output.function_argument()}};
  const std::string name="signal_active_spqr_receive_next_32";
  pinned_.verify_function(name,args);FunctionArgument ignored;machine_.run_function(name,ignored,args);return output;
 }
};
}
