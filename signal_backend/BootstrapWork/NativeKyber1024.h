#pragma once
#include "../../handshake_backend/NativeWorker.h"
namespace signal_mpc::bootstrap {
// Internal fixed pinned bootstrap stage. Recipient key, ciphertext and KEM
// agreement remain owned shares. No RPC, entropy input, open or commit method.
// Current component domain requires a valid generated Kyber public key.
// Outer bootstrap must establish that private key-domain/typed boundary and bind
// trust/signatures, actual DHs and computed validity before releasing anything.
class NativeKyber1024 {
 Machine<tls_mpc_worker::Share>& machine_;tls_mpc_worker::Worker& worker_;
 const tls_mpc_worker::PinnedPrograms& pinned_;
public:
 NativeKyber1024(Machine<tls_mpc_worker::Share>& machine,tls_mpc_worker::Worker& worker,
  const tls_mpc_worker::PinnedPrograms& pinned):machine_(machine),worker_(worker),pinned_(pinned){}
 tls_mpc_worker::Bits encapsulate(tls_mpc_worker::Bits tagged_key){
  if(tagged_key.size()!=1569*8)throw std::runtime_error("bootstrap Kyber public-key dimensions");
  auto output=worker_.allocate(1602*8);
  std::vector<FunctionArgument>args={{1,tagged_key.function_argument()},{1,output.function_argument()}};
  const std::string name="signal_private_bootstrap_kyber1024";
  pinned_.verify_function(name,args);FunctionArgument ignored;machine_.run_function(name,ignored,args);
  return output;
 }
};
}
