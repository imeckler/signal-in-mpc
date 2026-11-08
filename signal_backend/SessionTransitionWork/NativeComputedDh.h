#pragma once
#include "NativeWorker.h"
namespace signal_mpc {
// Internal stage: old own-DH private32 || actual-parsed remote32 -> fresh own
// private32 || actual computed public32 || receiveAgreement32 || sendAgreement32.
// No supplied agreements, raw-DH RPC, openings or commit. The outer authenticated
// receive transaction must select state and retire all old runtime traces.
class NativeComputedDh {
 Machine<tls_mpc_worker::Share>& machine_;tls_mpc_worker::Worker& allocation_;
 const tls_mpc_worker::PinnedPrograms& pinned_;
public:
 NativeComputedDh(Machine<tls_mpc_worker::Share>& machine,tls_mpc_worker::Worker& allocation,
  const tls_mpc_worker::PinnedPrograms& pinned):machine_(machine),allocation_(allocation),pinned_(pinned){}
 tls_mpc_worker::Bits prepare(tls_mpc_worker::Bits input){
  if(input.size()!=512)throw std::runtime_error("private DH receive dimensions");
  auto output=allocation_.allocate(1024);
  std::vector<FunctionArgument> args={{1,input.function_argument()},{1,output.function_argument()}};
  const std::string name="signal_private_dh_receive_candidate";
  pinned_.verify_function(name,args);FunctionArgument ignored;machine_.run_function(name,ignored,args);return output;
 }
};
}
