#pragma once
#include "../../handshake_backend/NativeWorker.h"
namespace signal_mpc::bootstrap {
// Embedding-only all-present private bundle profile; no caller verification
// flags. Tuple binds actual private trusted identity, typed recipient bundle,
// two signatures, one-time key and private metadata. See prekey_profile.py.
// Trusted identity must originate from the account's actual private lookup for
// this recipient; this component is not that lookup or a TOFU policy.
class NativePreKeyValidation {
 Machine<tls_mpc_worker::Share>& machine_;tls_mpc_worker::Worker& worker_;
 const tls_mpc_worker::PinnedPrograms& pinned_;
public:
 NativePreKeyValidation(Machine<tls_mpc_worker::Share>& machine,tls_mpc_worker::Worker& worker,
  const tls_mpc_worker::PinnedPrograms& pinned):machine_(machine),worker_(worker),pinned_(pinned){}
 tls_mpc_worker::Bits validate(tls_mpc_worker::Bits input){
  if(input.size()!=1857*8)throw std::runtime_error("bootstrap private bundle dimensions");
  auto result=worker_.allocate(8);
  std::vector<FunctionArgument>args={{1,input.function_argument()},{1,result.function_argument()}};
  const std::string name="signal_private_bootstrap_prekey_all_present";
  pinned_.verify_function(name,args);FunctionArgument ignored;machine_.run_function(name,ignored,args);
  return result;
 }
};
}
