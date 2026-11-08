#pragma once
#include "NativeWorker.h"
namespace signal_mpc {
// Internal key/identities/private-wire stage. Output is ACTUALLY computed MAC
// mask, not a correctness flag supplied by a caller. Parser/decryption/DH/PQ
// acceptance must also gate state selection; no opening/RPC/commit here.
class NativePrivateMessageMac {
 Machine<tls_mpc_worker::Share>& machine_;tls_mpc_worker::Worker& allocation_;
 const tls_mpc_worker::PinnedPrograms& pinned_;
public:
 NativePrivateMessageMac(Machine<tls_mpc_worker::Share>& machine,tls_mpc_worker::Worker& allocation,
  const tls_mpc_worker::PinnedPrograms& pinned):machine_(machine),allocation_(allocation),pinned_(pinned){}
 tls_mpc_worker::Bits verify(tls_mpc_worker::Bits input){
  if(input.size()!=2840)throw std::runtime_error("private Signal MAC dimensions");
  auto output=allocation_.allocate(8);
  std::vector<FunctionArgument> args={{1,input.function_argument()},{1,output.function_argument()}};
  const std::string name="signal_private_message_mac_256";
  pinned_.verify_function(name,args);FunctionArgument ignored;machine_.run_function(name,ignored,args);return output;
 }
};
}
