#pragma once
#include "Evidence.h"
#include "SessionWork/ErasedHostCall.h"
#include "../../handshake_backend/WebSocketWork/MuxProviderCoordinator.h"
#include <functional>
#include <memory>
namespace signal_mpc::recovery {
class AccountRecoveryEngineV1;
namespace sharded {class Engine;}
// An embedding-only one-shot capability, not a public/share-import RPC.
// Only the concrete account engines may construct it after actual checks.
// Presence of a resolver or hook is not authorization.
class AuthorizedRestoredAccount {
 friend class AccountRecoveryEngineV1;
 friend class sharded::Engine;
 using Build=std::function<tls_mpc_worker::MuxProviderAdmission(tls_mpc_worker::Session&,tls_mpc_worker::Collective&,unsigned)>;
 Build build_;unsigned party_;Digest head_,boot_;uint64_t import_host_,retirement_host_;bool consumed_=false;
 AuthorizedRestoredAccount(Build build,unsigned party,Digest head,Digest boot,uint64_t imported,uint64_t retired)
 :build_(std::move(build)),party_(party),head_(head),boot_(boot),import_host_(imported),retirement_host_(retired){
  require(bool(build_)&&party<5&&head!=Digest{}&&boot!=Digest{}&&imported>0&&retired>imported&&
   tls_mpc_worker::ErasedHostCall::completed(imported)&&tls_mpc_worker::ErasedHostCall::completed(retired),"account authorization completion prerequisites");
 }
public:
 AuthorizedRestoredAccount(const AuthorizedRestoredAccount&)=delete;AuthorizedRestoredAccount&operator=(const AuthorizedRestoredAccount&)=delete;
 tls_mpc_worker::MuxProviderAdmission consume(tls_mpc_worker::Session& session,tls_mpc_worker::Collective& collective,unsigned party){
  require(!consumed_&&party==party_&&bool(build_)&&tls_mpc_worker::ErasedHostCall::active()&&
   tls_mpc_worker::ErasedHostCall::completed(import_host_)&&tls_mpc_worker::ErasedHostCall::completed(retirement_host_),"account authorization consumed or incomplete");
  consumed_=true;auto build=std::move(build_);auto admission=build(session,collective,party);
  require(admission.restored_account&&admission.restored_request_cursor.size()==64&&admission.computed_cursor_validity.size()==8,"authorized account factory returned nonrestored admission");
  return admission;
 }
 const Digest& certified_head()const noexcept{return head_;}
 const Digest& boot_context()const noexcept{return boot_;}
};
// Called outside ErasedHostCall; the engine performs its own actual host calls.
// It may return a capability only after certificate/current-head/full-schema
// import/coherence validation, helper teardown and both completion barriers.
using AccountRecoveryResolver=std::function<std::unique_ptr<AuthorizedRestoredAccount>(
 Machine<tls_mpc_worker::Share>&,tls_mpc_worker::Worker&,tls_mpc_worker::PinnedPrograms&,
 tls_mpc_worker::Collective&,unsigned)>;
}
