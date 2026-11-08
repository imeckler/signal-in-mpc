#pragma once
#include "VariableSendStore.h"

namespace signal_mpc {
class UpgradeShape;
// Embedding-only admission of move-owned same-worker shares. There is no
// plaintext constructor, fixture key material, RPC importer, default factory
// or share opening. The embedding must supply authenticated established state
// from its shared computation/bootstrap and stable authoritative per-party slot.
// Recoverable authenticated bootstrap/persistence are NOT supplied by this API.
// Registry must establish collective public admission readiness before any eval.
// Registry must preserve upstream computed validity and AND it into every TLS
// output status; this does not replace the kernels' actual validity checks.
// Include NativeUpgrade.h before instantiating the default native profile.
template<class SharedBits,class UpgradeProfile=UpgradeShape> class PrivateProvider {
 enum class Phase {needs_upgrade,upgrading,upgrade_pending,active,producing,response_pending,closed};
 UpgradeProfile upgrade_shape_;VariableShape shape_;SharedBits credentials_;
 VariableSendStore<SharedBits> store_;Phase phase_=Phase::needs_upgrade;
 static void require(bool ok,const char* message){if(!ok)throw std::runtime_error(message);}
public:
 PrivateProvider(UpgradeProfile upgrade_shape,SharedBits credentials,VariableShape shape,
                 SharedBits initial,const std::string& per_party_fence_slot)
  :upgrade_shape_(std::move(upgrade_shape)),shape_(std::move(shape)),credentials_(std::move(credentials)),
   store_(shape_,std::move(initial),per_party_fence_slot){
  require(upgrade_shape_.input_bytes()>=32&&credentials_.size()==8*(upgrade_shape_.input_bytes()-16),
          "private provider credential dimensions");
 }
 ~PrivateProvider(){close();}
 PrivateProvider(const PrivateProvider&)=delete;PrivateProvider& operator=(const PrivateProvider&)=delete;
 const UpgradeProfile& upgrade_shape()const noexcept{return upgrade_shape_;}
 const VariableShape& shape()const noexcept{return shape_;}
 // Credential layout UUID16||passwordN. Nonce is separately generated fresh
 // public16bytes by the trusted worker, encoded as same-worker public shares.
 // Retain output, checkpoint private computation, then send through TLS.
 template<class Evaluate>SharedBits upgrade(SharedBits nonce,Evaluate&& evaluate){
  try{
   require(phase_==Phase::needs_upgrade,"private provider upgrade phase");
   require(nonce.size()==128,"private provider nonce dimensions");
   phase_=Phase::upgrading;
   auto input=std::move(credentials_);credentials_.clear();
   input.insert(input.end(),nonce.begin(),nonce.end());
   auto output=evaluate(upgrade_shape_,std::move(input));
   require(output.size()==8*upgrade_shape_.output_bytes(),"private provider upgrade result dimensions");
   require(phase_==Phase::upgrading,"private provider upgrade interrupted");
   phase_=Phase::upgrade_pending;
   return output;
  }catch(...){close();throw;}
 }
 // Trusted registry only: call after authenticated HTTP101/accept validation.
 // A TLS send completion alone is insufficient to activate this provider.
 void upgrade_complete(){
  try{require(phase_==Phase::upgrade_pending,"private provider upgrade completion phase");phase_=Phase::active;}
  catch(...){close();throw;}
 }
 template<class Evaluate>typename VariableSendStore<SharedBits>::Produced produce(
     SharedBits payload,SharedBits timestamp,Evaluate&& evaluate){
  try{
   require(phase_==Phase::active,"private provider send phase");
   phase_=Phase::producing;
   auto output=store_.produce(std::move(payload),std::move(timestamp),std::forward<Evaluate>(evaluate));
   require(phase_==Phase::producing,"private provider send interrupted");
   phase_=Phase::response_pending;
   return output;
  }catch(...){close();throw;}
 }
 // Embedding-only globally allocated ID; upstream registry owns uniqueness and
 // burns reservations on every failure. Same lifecycle as ordinary produce.
 template<class Evaluate>typename VariableSendStore<SharedBits>::Produced produce_with_request_id(
     SharedBits payload,SharedBits timestamp,SharedBits request_id,Evaluate&& evaluate){
  try{
   require(phase_==Phase::active,"private provider send phase");
   phase_=Phase::producing;
   auto output=store_.produce_with_request_id(std::move(payload),std::move(timestamp),
     std::move(request_id),std::forward<Evaluate>(evaluate));
   require(phase_==Phase::producing,"private provider send interrupted");
   phase_=Phase::response_pending;
   return output;
  }catch(...){close();throw;}
 }
 // Trusted registry only: authenticated complete response, expected privateID,
 // actual2xx status. Non2xx/uncertain send/rejection/timeout must call close().
 void response_complete(uint64_t ticket){
  try{
   require(phase_==Phase::response_pending,"private provider response phase");
   store_.response_complete(ticket);phase_=Phase::active;
  }catch(...){close();throw;}
 }
 void close()noexcept{phase_=Phase::closed;credentials_.clear();store_.close();}
};
}
