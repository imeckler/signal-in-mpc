#pragma once
// Public phase/domain authorization only. Does not create Bits or admit providers.
#include "OwnShareBox.h"
namespace signal_mpc::recovery {
struct CertifiedPhase {Proposal proposal;std::vector<Vote> votes;};
class CertifiedArchiveGate {
 Epoch epoch_;Digest context_,manifest_,schema_,sharing_epoch_;
 static void same_attempt(const Proposal& a,const Proposal& b){require(a.slot==b.slot&&a.context==b.context&&a.attempt==b.attempt&&a.manifest==b.manifest,"recovery attempt mismatch");}
public:
 CertifiedArchiveGate(Epoch epoch,Digest context,Digest manifest,Digest schema,Digest sharing_epoch)
 :epoch_(epoch),context_(context),manifest_(manifest),schema_(schema),sharing_epoch_(sharing_epoch){epoch_.digest();}
 // State COMMIT, not remote delivery acknowledgement, is the recoverable head.
 ShareDomain authorize_committed(unsigned party,uint64_t bit_count,const Digest& previous_commit,
   const CertifiedPhase& reserve,const CertifiedPhase& commit,const Digest& challenge,
   const std::vector<Status>& statuses,const Digest& own_ciphertext)const{
  require(party<5,"invalid archive party");
  for(auto* p:{&reserve,&commit}){require(p->proposal.context==context_&&p->proposal.manifest==manifest_,"archive context/manifest mismatch");require(certificate(epoch_,p->proposal,p->votes),"archive phase certificate rejected");}
  const auto& r=reserve.proposal;const auto& c=commit.proposal;
  require(r.phase==Phase::Reserve&&c.phase==Phase::Commit,"archive phase order rejected");same_attempt(r,c);
  require(r.parent==previous_commit&&c.parent==r.digest(epoch_),"archive phase parent rejected");
  require(c.bundles[party]==own_ciphertext,"archive committed ciphertext mismatch");
  require(statuses.size()>=4&&statuses.size()<=5,"archive freshness quorum missing");unsigned mask=0;
  for(const auto& s:statuses){require(verify_status(epoch_,context_,challenge,s)&&!(mask&(1u<<s.party)),"archive freshness signature rejected");mask|=1u<<s.party;
   // Later unresolved reservations burn this candidate even without a known cert.
   require(s.highest_slot<=c.slot,"archive later attempt unresolved");}
  ShareDomain domain{party,epoch_.number,c.slot,bit_count,context_,epoch_.digest(),manifest_,schema_,sharing_epoch_};domain.header();return domain;
 }
 // Historical stricter publication-certificate profile. It is not evidence of
 // server delivery and is not required by the active account commit-head path.
 ShareDomain authorize(unsigned party,uint64_t bit_count,const Digest& previous_head,
   const CertifiedPhase& reserve,const CertifiedPhase& commit,const CertifiedPhase& publication,
   const Digest& challenge,const std::vector<Status>& statuses,const Digest& own_ciphertext)const{
  auto domain=authorize_committed(party,bit_count,previous_head,reserve,commit,challenge,statuses,own_ciphertext);
  const auto& a=publication.proposal;require(a.phase==Phase::Acknowledge&&certificate(epoch_,a,publication.votes),"archive publication certificate rejected");same_attempt(commit.proposal,a);
  require(a.parent==commit.proposal.digest(epoch_)&&a.bundles==commit.proposal.bundles,"archive publication linkage rejected");return domain;
 }
};
}
