#pragma once
#include "OwnShareBox.h"
#include <optional>
namespace signal_mpc::recovery {
// Embedding-only ordering adapter. It deliberately has no provider/Session API.
// Load must perform actual certificate/domain/AEAD checks; import must own and
// destroy its protocol helper before returning. Concrete adapters remain gated.
class BootstrapOrder {
 enum class Phase {Fresh,Loading,Importing,Retiring,Complete,Failed};
 Phase phase_=Phase::Fresh;
public:
 BootstrapOrder()=default;BootstrapOrder(const BootstrapOrder&)=delete;
 template<class Load,class Collective,class Import,class Retire>
 auto resolve(Load&& load,Collective&& all_ready,Import&& import,Retire&& retire)
 -> decltype(import(std::declval<QuarantinedEvaluations>())) {
  require(phase_==Phase::Fresh,"recovery bootstrap already consumed");
  try{
   phase_=Phase::Loading;std::optional<QuarantinedEvaluations> local;
   // All members must reach the readiness collective even on local disk,
   // signature, domain or AEAD failure. No import helper exists yet.
   try{local.emplace(load());}catch(...){local.reset();}
   bool collective_ready=all_ready(bool(local));
   require(collective_ready&&bool(local),"recovery bootstrap collective readiness failed");
   phase_=Phase::Importing;
   auto fresh=import(std::move(*local));local.reset();
   // Import's call frame (including helper/protocol owners) has returned;
   // local archive ownership is gone before runtime retirement. Retirement
   // must include ErasedHostCall completion, not just request an epoch change.
   phase_=Phase::Retiring;retire();phase_=Phase::Complete;
   return fresh;
  }catch(...){phase_=Phase::Failed;throw;}
 }
 bool complete()const{return phase_==Phase::Complete;}
};
}
