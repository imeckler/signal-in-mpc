#pragma once
#include "NativeAccountCapture.h"
#include "PublicCheckpointStore.h"
#include "NativeCollective.h"
#include <optional>
namespace signal_mpc::recovery {
// Actual same-five-node public certificate/current-head protocol. It does not
// make private account sections semantically valid or activate a provider.
// Static epoch keys must be bound to authenticated MPC peer slots externally.
class AccountCheckpointCoordinator {
 Epoch epoch_;Digest context_,manifest_;unsigned party_;
 std::function<Digest(Phase,uint64_t,const std::vector<const tls_mpc_worker::Bits*>&)> persist_;
 std::function<Vote(const Proposal&,const CertifiedPhase*)> vote_;
 std::optional<LocalAccountCheckpoint::Prepared> local_prepared_;
 VoteJournal& journal_;PublicCheckpointStore& public_;
 tls_mpc_worker::Collective& collective_;std::function<Player&()> player_;
 std::optional<CertifiedPhase> current_,reserved_;bool failed_=false,recovered_=false;
 std::vector<Bytes> broadcast(const Bytes& mine){auto& player=player_();require(player.num_players()==5&&unsigned(player.my_num())==party_,"account coordinator peer domain");require(mine.size()<=4096,"account coordinator frame bounds");std::vector<octetStream> streams(5);streams[party_]=octetStream(std::string(mine.begin(),mine.end()));player.Broadcast_Receive(streams);player.Check_Broadcast();std::vector<Bytes> out;for(auto& stream:streams){require(stream.get_length()<=4096,"account coordinator received frame bounds");if(stream.get_length())out.emplace_back(stream.get_data(),stream.get_data()+stream.get_length());else out.emplace_back();}return out;}
 void domain(const CertifiedPhase& phase)const{require(certificate(epoch_,phase.proposal,phase.votes)&&phase.proposal.context==context_&&phase.proposal.manifest==manifest_,"account coordinator certificate domain");}
 CertifiedPhase fetch(const Digest& id){Bytes local;bool ready=false;try{local=public_.get(id);ready=true;}catch(...){}collective_.require_local_success(ready);require(ready,"account coordinator certificate read failed");auto all=broadcast(local);std::optional<CertifiedPhase> found;
  for(auto& bytes:all)if(!bytes.empty()){auto phase=decode_phase(epoch_,bytes);domain(phase);require(phase.proposal.digest(epoch_)==id,"account coordinator fetched digest");found=std::move(phase);}
  require(bool(found),"account coordinator required certificate unavailable");return std::move(*found);
 }
 CertifiedPhase certify(Phase phase,uint64_t slot,const Digest& parent,const Digest& attempt,const std::vector<const tls_mpc_worker::Bits*>& sections,const CertifiedPhase* previous){
  std::optional<Digest> prepared;try{prepared.emplace(persist_(phase,slot,sections));}catch(...){prepared.reset();}
  // No private producer may run before ALL five local reservations persist.
  collective_.require_local_success(bool(prepared));require(bool(prepared),"account coordinator local prepare failed");
  auto bundles=broadcast(Bytes(prepared->begin(),prepared->end()));Proposal proposal{phase,slot,context_,parent,attempt,manifest_,{}};
  for(size_t i=0;i<5;++i){require(bundles[i].size()==32,"account coordinator bundle digest width");std::copy_n(bundles[i].begin(),32,proposal.bundles[i].begin());}
  std::optional<Vote> vote;try{vote.emplace(vote_(proposal,previous));}catch(...){vote.reset();}
  collective_.require_local_success(bool(vote));require(bool(vote),"account coordinator local durable vote failed");
  Bytes own{static_cast<unsigned char>(vote->party)};own.insert(own.end(),vote->signature.begin(),vote->signature.end());auto replies=broadcast(own);std::vector<Vote> votes;
  for(size_t i=0;i<5;++i){require(replies[i].size()==65&&replies[i][0]==i,"account coordinator vote identity");Vote item{unsigned(i),{}};std::copy_n(replies[i].begin()+1,64,item.signature.begin());votes.push_back(item);}
  CertifiedPhase certificate{proposal,std::move(votes)};domain(certificate);bool saved=false;try{public_.put(epoch_,certificate);saved=true;}catch(...){}
  collective_.require_local_success(saved);require(saved,"account coordinator certificate publication failed");return certificate;
 }
public:
 struct CurrentHead {std::optional<CertifiedPhase> commit,reservation;Digest challenge;std::vector<Status> statuses;};
 AccountCheckpointCoordinator(Epoch epoch,Digest context,Digest manifest,unsigned party,NativeAccountCapture& capture,LocalAccountCheckpoint& checkpoint,VoteJournal& journal,PublicCheckpointStore& public_store,tls_mpc_worker::Collective& collective,std::function<Player&()> player)
 :epoch_(epoch),context_(context),manifest_(manifest),party_(party),journal_(journal),public_(public_store),collective_(collective),player_(std::move(player)){require(party<5&&bool(player_),"account coordinator configuration");epoch_.digest();
  persist_=[this,&capture](Phase phase,uint64_t slot,const auto& sections){local_prepared_=capture.persist(phase,slot,sections);return local_prepared_->ciphertext();};
  vote_=[this,&checkpoint](const Proposal& proposal,const CertifiedPhase* previous){require(bool(local_prepared_),"account prepared persistence missing");auto vote=checkpoint.vote(*local_prepared_,proposal,previous);local_prepared_.reset();return vote;};
 }
 // Alternate durable local representation; same five-node agreement, journal,
 // certificates and current-head protocol. Callbacks must validate root lineage
 // and changed private shards before returning a digest or durable vote.
 AccountCheckpointCoordinator(Epoch epoch,Digest context,Digest manifest,unsigned party,
  std::function<Digest(Phase,uint64_t,const std::vector<const tls_mpc_worker::Bits*>&)> persist,
  std::function<Vote(const Proposal&,const CertifiedPhase*)> vote,
  VoteJournal& journal,PublicCheckpointStore& public_store,tls_mpc_worker::Collective& collective,std::function<Player&()> player)
 :epoch_(epoch),context_(context),manifest_(manifest),party_(party),persist_(std::move(persist)),vote_(std::move(vote)),journal_(journal),public_(public_store),collective_(collective),player_(std::move(player)){
  require(party<5&&bool(player_)&&bool(persist_)&&bool(vote_),"account coordinator local adapter configuration");epoch_.digest();
 }
 AccountCheckpointCoordinator(const AccountCheckpointCoordinator&)=delete;AccountCheckpointCoordinator&operator=(const AccountCheckpointCoordinator&)=delete;
 CurrentHead recover_current(){require(tls_mpc_worker::ErasedHostCall::active(),"account coordinator requires erased host call");require(!failed_&&!recovered_,"account coordinator current-head consumed");try{
  auto random=collective_.public_random();Digest challenge;std::copy_n(random.begin(),32,challenge.begin());std::optional<Status> own_status;try{own_status.emplace(journal_.status(challenge));}catch(...){}collective_.require_local_success(bool(own_status));require(bool(own_status),"account coordinator local status failed");auto status=*own_status;Bytes encoded{static_cast<unsigned char>(status.party)};u64(encoded,status.highest_slot);append(encoded,status.context);append(encoded,status.challenge);append(encoded,status.journal);encoded.insert(encoded.end(),status.signature.begin(),status.signature.end());auto replies=broadcast(encoded);std::vector<Status> statuses;uint64_t high=0;
  for(size_t i=0;i<5;++i){auto& raw=replies[i];require(raw.size()==169&&raw[0]==i,"account coordinator status shape");Status item{};item.party=i;item.highest_slot=read64(raw.data()+1);std::copy_n(raw.begin()+9,32,item.context.begin());std::copy_n(raw.begin()+41,32,item.challenge.begin());std::copy_n(raw.begin()+73,32,item.journal.begin());std::copy_n(raw.begin()+105,64,item.signature.begin());require(verify_status(epoch_,context_,challenge,item),"account coordinator fresh status signature");high=std::max(high,item.highest_slot);statuses.push_back(item);}
  Bytes local_head;bool readable=false;try{local_head=public_.highest_commit(epoch_,context_,manifest_);readable=true;}catch(...){}collective_.require_local_success(readable);require(readable,"account coordinator local head scan failed");auto candidates=broadcast(local_head);std::optional<CertifiedPhase> head;
  for(auto& bytes:candidates)if(!bytes.empty()){auto phase=decode_phase(epoch_,bytes);domain(phase);require(phase.proposal.phase==Phase::Commit&&phase.proposal.slot<=high,"account coordinator head/status mismatch");if(!head||phase.proposal.slot>head->proposal.slot)head=std::move(phase);else if(phase.proposal.slot==head->proposal.slot)require(phase.proposal.digest(epoch_)==head->proposal.digest(epoch_),"account coordinator conflicting heads");}
  require((high==0&&!head)||(head&&head->proposal.slot==high),"account coordinator unresolved higher reservation/head");
  std::optional<CertifiedPhase> head_reservation;if(head){auto next=*head;size_t count=0;while(true){require(++count<=1000000,"account coordinator ancestry bound");domain(next);require(next.proposal.phase==Phase::Commit,"account coordinator ancestry commit phase");auto reserve=fetch(next.proposal.parent);if(!head_reservation)head_reservation=reserve;require(reserve.proposal.phase==Phase::Reserve&&reserve.proposal.slot==next.proposal.slot&&reserve.proposal.attempt==next.proposal.attempt,"account coordinator reserve/commit ancestry");
    if(next.proposal.slot==1){require(reserve.proposal.parent==epoch_.genesis,"account coordinator genesis ancestry");break;}
    auto previous=fetch(reserve.proposal.parent);require(previous.proposal.phase==Phase::Commit&&previous.proposal.slot!=UINT64_MAX&&previous.proposal.slot+1==next.proposal.slot,"account coordinator sequential ancestry");next=std::move(previous);
   }}current_=head;recovered_=true;return{std::move(head),std::move(head_reservation),challenge,std::move(statuses)};
 }catch(...){failed_=true;throw;}}
 CertifiedPhase reserve(const std::vector<const tls_mpc_worker::Bits*>& sections){require(tls_mpc_worker::ErasedHostCall::active(),"account coordinator requires erased host call");require(!failed_&&recovered_&&!reserved_,"account coordinator reserve phase");try{
  uint64_t slot=current_?current_->proposal.slot+1:1;require(!current_||current_->proposal.slot!=UINT64_MAX,"account coordinator slot exhaustion");auto parent=current_?current_->proposal.digest(epoch_):epoch_.genesis;auto bytes=collective_.public_random();Digest attempt;std::copy_n(bytes.begin(),32,attempt.begin());reserved_=certify(Phase::Reserve,slot,parent,attempt,sections,current_?&*current_:nullptr);return *reserved_;
 }catch(...){failed_=true;throw;}}
 CertifiedPhase commit(const std::vector<const tls_mpc_worker::Bits*>& sections){require(tls_mpc_worker::ErasedHostCall::active(),"account coordinator requires erased host call");require(!failed_&&reserved_,"account coordinator commit phase");try{
  auto result=certify(Phase::Commit,reserved_->proposal.slot,reserved_->proposal.digest(epoch_),reserved_->proposal.attempt,sections,&*reserved_);current_=result;reserved_.reset();return result;
 }catch(...){failed_=true;throw;}}
 void poison()noexcept{failed_=true;}bool failed()const noexcept{return failed_;}
};
}
