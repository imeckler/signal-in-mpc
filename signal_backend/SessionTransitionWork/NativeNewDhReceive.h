#pragma once
#include "NativeWorker.h"
namespace signal_mpc {
// Internal candidate: retained state525 || incoming identity32 || local identity32
// || validity/BE16-length/wire-cap256. Output computed validity1 || selected
// state525 || private plaintext BE16-length/cap80. All arrays remain shared.
// The embedding must persist the selected state, retire old computation traces,
// and keep the application result gated. This is not a full SessionRecord store.
class NativeNewDhReceive {
 Machine<tls_mpc_worker::Share>& machine_;
 tls_mpc_worker::Worker& allocation_;
 const tls_mpc_worker::PinnedPrograms& pinned_;
public:
 NativeNewDhReceive(Machine<tls_mpc_worker::Share>& machine,
  tls_mpc_worker::Worker& allocation,const tls_mpc_worker::PinnedPrograms& pinned)
  :machine_(machine),allocation_(allocation),pinned_(pinned){}
 tls_mpc_worker::Bits evaluate(tls_mpc_worker::Bits input){
  if(input.size()!=6784)throw std::runtime_error("private new-DH receive dimensions");
  auto output=allocation_.allocate(4864);
  std::vector<FunctionArgument> args={{1,input.function_argument()},{1,output.function_argument()}};
  const std::string name="signal_private_new_dh_receive_256_5";
  pinned_.verify_function(name,args);
  FunctionArgument ignored;machine_.run_function(name,ignored,args);return output;
 }
};
}
