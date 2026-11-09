#pragma once
#include "AccountLayoutV2.h"
namespace signal_mpc::recovery {
// Structural coherence only. Actual certified head/provenance, full-field import
// and completed helper/epoch barriers remain separate admission prerequisites.
class NativeAccountAdmission {
 Machine<tls_mpc_worker::Share>& machine_;tls_mpc_worker::Worker& worker_;const tls_mpc_worker::PinnedPrograms& pinned_;
public:
 NativeAccountAdmission(Machine<tls_mpc_worker::Share>& machine,tls_mpc_worker::Worker& worker,const tls_mpc_worker::PinnedPrograms& pinned):machine_(machine),worker_(worker),pinned_(pinned){}
 tls_mpc_worker::Bits evaluate(const OwnedAccountV2& account){
  auto state=account.flatten();NativeOwnShareArchive::require_cells(state);auto valid=worker_.allocate(8);
  std::vector<FunctionArgument> args={{1,state.function_argument()},{1,valid.function_argument()}};
  auto name="signal_private_account_admit_v2_c"+std::to_string(account.layout().conversations());
  pinned_.verify_function(name,args);FunctionArgument ignored;machine_.run_function(name,ignored,args);return valid;
 }
};
}
