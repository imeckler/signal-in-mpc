#pragma once
#include "ShardDirectory.h"
#include "../EvidenceCodec.h"
namespace signal_mpc::recovery::sharded {
// Local adapter for AccountCheckpointCoordinator. No capability/admission API.
// A changed shard validator must consume actual private computed validity before
// returning its pinned program identity. Tests use explicitly PUBLIC validators.
class Checkpoint {
 Directory& directory_;CiphertextStore& shards_;VoteJournal& journal_;Epoch epoch_;Digest context_,manifest_;unsigned party_;
 Digest root_,prepared_root_{},base_{};uint64_t prepared_slot_=0;Phase prepared_phase_=Phase::Reserve;bool prepared_=false,failed_=false;
 std::vector<Leaf> changes_;Directory::Validate validator_;
public:
 uint64_t changed_ciphertext_bytes=0;
 Checkpoint(Directory& directory,CiphertextStore& shards,VoteJournal& journal,Epoch epoch,Digest context,Digest manifest,unsigned party)
 :directory_(directory),shards_(shards),journal_(journal),epoch_(epoch),context_(context),manifest_(manifest),party_(party),root_(directory.genesis()){require(party<5,"shard checkpoint party");}
 void restore_root(const CertifiedPhase& commit){require(!prepared_&&!failed_&&changes_.empty(),"shard restore phase");require(commit.proposal.phase==Phase::Commit&&commit.proposal.context==context_&&commit.proposal.manifest==manifest_&&certificate(epoch_,commit.proposal,commit.votes),"shard restore certificate");root_=commit.proposal.bundles[party_];}
 void stage(std::vector<Leaf> changes,Directory::Validate validator){require(!failed_&&!prepared_&&changes_.empty()&&!changes.empty()&&changes.size()<=5&&bool(validator),"shard stage bounds/phase");for(size_t i=0;i<changes.size();++i)for(size_t j=0;j<i;++j)require(changes[i].key!=changes[j].key,"shard duplicate changed slot");changes_=std::move(changes);validator_=std::move(validator);}
 Digest persist(Phase phase,uint64_t slot){require(!failed_&&!prepared_&&!changes_.empty()&&(phase==Phase::Reserve||phase==Phase::Commit),"shard prepare phase");try{
  base_=root_;auto next=root_;
  for(auto& change:changes_){shards_.get(change.ciphertext,change.ciphertext_bytes);changed_ciphertext_bytes+=change.ciphertext_bytes;next=directory_.replace(next,change,validator_);}
  prepared_root_=next;prepared_slot_=slot;prepared_phase_=phase;prepared_=true;changes_.clear();validator_={};return next;
 }catch(...){failed_=true;throw;}}
 Vote vote(const Proposal& p,const CertifiedPhase* previous){require(!failed_&&prepared_,"shard vote phase");try{
  require(p.context==context_&&p.manifest==manifest_&&p.slot==prepared_slot_&&p.phase==prepared_phase_&&p.bundles[party_]==prepared_root_,"shard prepared proposal binding");
  if(p.phase==Phase::Reserve&&p.slot==1)require(!previous&&p.parent==epoch_.genesis&&base_==directory_.genesis(),"shard new genesis only");
  else{require(previous&&certificate(epoch_,previous->proposal,previous->votes)&&previous->proposal.context==context_&&previous->proposal.manifest==manifest_&&p.parent==previous->proposal.digest(epoch_)&&base_==previous->proposal.bundles[party_],"shard certified inheritance");
   if(p.phase==Phase::Commit)require(previous->proposal.phase==Phase::Reserve&&p.slot==previous->proposal.slot&&p.attempt==previous->proposal.attempt,"shard commit reservation");
   else require(previous->proposal.phase==Phase::Commit&&previous->proposal.slot!=UINT64_MAX&&p.slot==previous->proposal.slot+1,"shard reserve sequence");}
  auto vote=journal_.vote(p);root_=prepared_root_;prepared_=false;return vote;
 }catch(...){failed_=true;throw;}}
 Digest root()const{return root_;}bool failed()const{return failed_;}
};
}
