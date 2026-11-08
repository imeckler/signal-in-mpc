#pragma once
#include "AccountSchemaV1.h"
#include "CiphertextStore.h"
#include "EvidenceCodec.h"
namespace signal_mpc::recovery {
// A concrete local archive+vote adapter. Full private semantic validation and
// collective runtime retirement are separate, closed admission prerequisites.
class LocalAccountCheckpoint {
 Epoch epoch_;AccountSchemaV1 schema_;Digest context_,manifest_,sharing_;unsigned party_;const OwnShareBox& box_;CiphertextStore& files_;VoteJournal& journal_;
 Digest phase_schema(const AccountSchemaV1& schema,Phase phase)const{auto b=label("SIGNAL-ACCOUNT-PHASE-SCHEMA-1");b.push_back(unsigned(phase));append(b,schema.digest());return hash(b);}
 void own(const Proposal& p)const{require(p.context==context_&&p.manifest==manifest_,"account checkpoint context/manifest");}
 void predecessor(const Proposal& p,const CertifiedPhase& previous,Phase phase,bool same_slot)const{
  require(previous.proposal.phase==phase&&certificate(epoch_,previous.proposal,previous.votes),"account checkpoint predecessor certificate");own(previous.proposal);
  require(p.parent==previous.proposal.digest(epoch_),"account checkpoint predecessor link");
  if(same_slot)require(p.slot==previous.proposal.slot&&p.attempt==previous.proposal.attempt,"account checkpoint attempt link");
  else require(previous.proposal.slot!=UINT64_MAX&&p.slot==previous.proposal.slot+1,"account checkpoint slot sequence");
 }
public:
 class Prepared {
  friend class LocalAccountCheckpoint;ShareDomain domain_;Digest ciphertext_;Phase phase_;
  Prepared(ShareDomain domain,Digest ciphertext,Phase phase):domain_(domain),ciphertext_(ciphertext),phase_(phase){}
 public:
  const ShareDomain& domain()const{return domain_;}const Digest& ciphertext()const{return ciphertext_;}
 };
 LocalAccountCheckpoint(Epoch epoch,AccountSchemaV1 schema,Digest context,Digest manifest,Digest sharing,unsigned party,const OwnShareBox& box,CiphertextStore& files,VoteJournal& journal)
 :epoch_(epoch),schema_(std::move(schema)),context_(context),manifest_(manifest),sharing_(sharing),party_(party),box_(box),files_(files),journal_(journal){require(party<5,"account checkpoint member");epoch_.digest();
  auto bind=hash(label("local-account-journal-identity-binding"));auto status=journal_.status(bind);
  require(status.party==party_&&verify_status(epoch_,context_,bind,status),"account checkpoint journal identity/context mismatch");}
 Prepared persist(Phase phase,uint64_t slot,std::vector<QuarantinedEvaluations> local){
  require(phase==Phase::Reserve||phase==Phase::Commit,"account snapshot phase");
  ShareDomain domain{party_,epoch_.number,slot,schema_.bits(),context_,epoch_.digest(),manifest_,phase_schema(schema_,phase),sharing_};
  auto shares=schema_.pack(std::move(local));auto ciphertext=box_.seal(domain,shares);
  // Immutable file+directory fsync completes before Prepared can authorize vote.
  return Prepared(domain,files_.put(ciphertext),phase);
 }
 Vote vote(const Prepared& prepared,const Proposal& proposal,const CertifiedPhase* previous=nullptr){
  own(proposal);const auto& d=prepared.domain_;
  require(d.party==party_&&d.epoch==epoch_.number&&d.membership==epoch_.digest()&&d.context==context_&&d.manifest==manifest_&&d.sharing_epoch==sharing_&&d.bit_count==schema_.bits()&&d.schema==phase_schema(schema_,prepared.phase_),"prepared account owner/domain");
  require(proposal.phase==prepared.phase_&&proposal.slot==d.slot&&proposal.bundles[party_]==prepared.ciphertext_,"prepared account proposal mismatch");
  if(proposal.phase==Phase::Reserve){
   if(proposal.slot==1)require(!previous&&proposal.parent==epoch_.genesis,"account genesis link");
   else{require(previous,"account preceding acknowledgement missing");predecessor(proposal,*previous,Phase::Acknowledge,false);}
  }else{require(previous,"account reservation missing");predecessor(proposal,*previous,Phase::Reserve,true);}
  // Re-read the installed file before durable vote. No private plaintext escapes.
  files_.get(prepared.ciphertext_,d.header().size()+16+d.bit_count*16);
  return journal_.vote(proposal);
 }
 Vote acknowledge(const Prepared& prepared,const Proposal& proposal,const CertifiedPhase& committed){
  own(proposal);const auto& d=prepared.domain_;require(d.party==party_&&d.epoch==epoch_.number&&d.membership==epoch_.digest()&&d.context==context_&&d.manifest==manifest_&&d.sharing_epoch==sharing_&&d.bit_count==schema_.bits()&&d.schema==phase_schema(schema_,Phase::Commit),"account acknowledgement owner/schema");require(prepared.phase_==Phase::Commit&&proposal.phase==Phase::Acknowledge,"account acknowledgement phase");
  predecessor(proposal,committed,Phase::Commit,true);
  require(proposal.bundles==committed.proposal.bundles&&proposal.bundles[party_]==prepared.ciphertext_&&prepared.domain_.slot==proposal.slot,"account acknowledgement outbox binding");
  files_.get(prepared.ciphertext_,prepared.domain_.header().size()+16+prepared.domain_.bit_count*16);return journal_.vote(proposal);
 }
 QuarantinedEvaluations load_committed(unsigned party,uint64_t bits,const Digest& previous_ack,
   const CertifiedPhase& reserve,const CertifiedPhase& commit,const CertifiedPhase& ack,const Digest& challenge,const std::vector<Status>& statuses)const{
  require(party==party_&&bits==schema_.bits(),"account reload schema dimensions");
  CertifiedArchiveGate gate(epoch_,context_,manifest_,phase_schema(schema_,Phase::Commit),sharing_);
  auto domain=gate.authorize(party,bits,previous_ack,reserve,commit,ack,challenge,statuses,commit.proposal.bundles[party]);
  auto ciphertext=files_.get(commit.proposal.bundles[party],domain.header().size()+16+bits*16);
  return box_.open_quarantined(domain,ciphertext);
 }
};
}
