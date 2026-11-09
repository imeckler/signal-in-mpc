#pragma once
#include "../../handshake_backend/NativeWorker.h"
namespace signal_mpc::bootstrap {
// Internal fixed one-time-prekey profile; no supplied agreements or entropy.
// Input ownIKprivate32||peerIK32||SPK32||OPK32. Output basePublic32||fresh
// ratchetPrivate32||ratchetPublic32||computedOwnIKPublic32||five agreements32.
// Whole bootstrap must check actual signatures/trust, identity binding, all
// nonzero agreements and KEM success before producing/committing a session.
class NativeBootstrapDh {
 Machine<tls_mpc_worker::Share>& machine_;tls_mpc_worker::Worker& worker_;
 const tls_mpc_worker::PinnedPrograms& pinned_;
public:
 NativeBootstrapDh(Machine<tls_mpc_worker::Share>& machine,tls_mpc_worker::Worker& worker,
  const tls_mpc_worker::PinnedPrograms& pinned):machine_(machine),worker_(worker),pinned_(pinned){}
 tls_mpc_worker::Bits prepare(tls_mpc_worker::Bits input){
  if(input.size()!=128*8)throw std::runtime_error("bootstrap DH input dimensions");
  auto result=worker_.allocate(288*8);
  std::vector<FunctionArgument>args={{1,input.function_argument()},{1,result.function_argument()}};
  const std::string name="signal_private_bootstrap_dh_with_one_time";
  pinned_.verify_function(name,args);FunctionArgument ignored;machine_.run_function(name,ignored,args);
  return result;
 }
};
}
