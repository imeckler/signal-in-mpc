#pragma once
// Public phase/domain authorization only. Does not create Bits or admit providers.
#include "OwnShareBox.h"
namespace signal_mpc::recovery {
struct CertifiedPhase {Proposal proposal;std::vector<Vote> votes;};
class CertifiedArchiveGate {
 Epoch epoch_;Digest context_,manifest_,schema_,sharing_epoch_;
 static void same_attempt(const Proposal& a,const Proposal& b){
  require(a.slot==b.slot&&a.context==b.context&&a.attempt==b.attempt&&a.manifest==b.manifest,"recovery attempt mismatch");
 }
public:
 CertifiedArchiveGate(Epoch epoch,Digest context,Digest manifest,Digest schema,Digest sharing_epoch)
 :epoch_(epoch),context_(context),manifest_(manifest),schema_(schema),sharing_epoch_(sharing_epoch){epoch_.digest();}
 ShareDomain authorize(unsigned party,uint64_t bit_count,const Digest& previous_ack,
   const CertifiedPhase& reserve,const CertifiedPhase& commit,const CertifiedPhase& ack,
   const Digest& challenge,const std::vector<Status>& statuses,const Digest& own_ciphertext)const{
  require(party<5,"invalid archive party");
  for(auto* p:{&reserve,&commit,&ack}){
   require(p->proposal.context==context_&&p->proposal.manifest==manifest_,"archive context/manifest mismatch");
   require(certificate(epoch_,p->proposal,p->votes),"archive phase certificate rejected");
  }
  const auto& r=reserve.proposal;const auto& c=commit.proposal;const auto& a=ack.proposal;
  require(r.phase==Phase::Reserve&&c.phase==Phase::Commit&&a.phase==Phase::Acknowledge,"archive phase order rejected");
  same_attempt(r,c);same_attempt(c,a);
  require(r.parent==previous_ack&&c.parent==r.digest(epoch_)&&a.parent==c.digest(epoch_),"archive phase parent rejected");
  require(a.bundles==c.bundles&&c.bundles[party]==own_ciphertext,"archive committed ciphertext mismatch");
  require(statuses.size()>=4&&statuses.size()<=5,"archive freshness quorum missing");unsigned mask=0;
  for(const auto& s:statuses){
   require(verify_status(epoch_,context_,challenge,s)&&!(mask&(1u<<s.party)),"archive freshness signature rejected");
   mask|=1u<<s.party;
   // Any observed later reservation, even without a known certificate, burns
   // this candidate. Caller must recover that attempt or abort, never roll back.
   require(s.highest_slot<=c.slot,"archive later attempt unresolved");
  }
  ShareDomain domain{party,epoch_.number,c.slot,bit_count,context_,epoch_.digest(),manifest_,schema_,sharing_epoch_};
  domain.header();return domain;
 }
};
}
