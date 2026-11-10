#pragma once
#include "../../handshake_backend/NativeWorker.h"
namespace signal_mpc::bootstrap {
// Internal initial SPQR generator. Joint seed is never supplied/opened; result
// is status||sk2400||pk1184, exactly the typed input of PrivateInitialSpqrV1.
class NativeMlKem768 {
 Machine<tls_mpc_worker::Share>& machine_;tls_mpc_worker::Worker& worker_;
 const tls_mpc_worker::PinnedPrograms& pinned_;
public:
 NativeMlKem768(Machine<tls_mpc_worker::Share>& machine,tls_mpc_worker::Worker& worker,
  const tls_mpc_worker::PinnedPrograms& pinned):machine_(machine),worker_(worker),pinned_(pinned){}
 tls_mpc_worker::Bits generate(){
  auto reserved=worker_.allocate(8);auto result=worker_.allocate(3585*8);
  std::vector<FunctionArgument>args={{1,reserved.function_argument()},{1,result.function_argument()}};
  const std::string name="signal_private_bootstrap_mlkem768_keygen";
  pinned_.verify_function(name,args);FunctionArgument ignored;machine_.run_function(name,ignored,args);
  return result;
 }
};
}
