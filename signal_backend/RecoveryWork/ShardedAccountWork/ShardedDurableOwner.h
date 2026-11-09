#pragma once
#include "NativeShardCapture.h"
#include "ResponseLeases.h"
#include <iostream>
#include <set>
#include "../AccountCheckpointCoordinator.h"
#include "../../../handshake_backend/WebSocketWork/NativeConversation.h"
namespace signal_mpc::recovery::sharded {
// Fresh-account candidate owner. Restored root/readmission admission is separate.
// At most four active conversations; inactive directory shards are never copied.
class Engine;
class DurableOwner final:public tls_mpc_worker::DurableConversationHooks {
 friend class Engine;
 using Bits=tls_mpc_worker::Bits;using Session=tls_mpc_worker::Session;using Store=VariableSendStore<Bits>;
 std::shared_ptr<void> persistence_;AccountCheckpointCoordinator& coordinator_;Checkpoint& checkpoint_;Directory& directory_;NativeShardCapture& capture_;
 Session& session_;ResponseLeases responses_;uint64_t sequence_=0;bool closed_=false,reserved_=false;
 Bits global_,accepted_;std::map<size_t,Bits> active_;
 std::set<size_t> dirty_;std::vector<size_t> slots_;std::vector<uint64_t> tickets_;std::vector<Bits> calls_,records_,selected_;
 static Bits copy(const Bits& x){return{x.begin(),x.end()};}
 static Bits slice(const Bits& x,size_t at,size_t size){require((at+size)*8<=x.size(),"shard owner slice");return{x.begin()+at*8,x.begin()+(at+size)*8};}
 static void replace(Bits& x,size_t at,const Bits& values){require(at*8+values.size()<=x.size(),"shard owner replace");NativeOwnShareArchive::require_cells(values);std::copy(values.begin(),values.end(),x.begin()+at*8);}
 static void append(Bits& x,const Bits& y){x.insert(x.end(),y.begin(),y.end());}
 Bits constant(unsigned n){return session_.share_public_constants({static_cast<unsigned char>(n)});}
 Bits generation(uint64_t n){std::vector<unsigned char> bytes(8);for(int i=7;i>=0;--i){bytes[i]=n&255;n>>=8;}return session_.share_public_constants(bytes);}
 void live()const{require(!closed_,"shard owner closed");}
 void same(const std::vector<size_t>& slots,const std::vector<VariableShape>& shapes)const{require(slots==slots_&&slots.size()==shapes.size(),"shard owner staged group");for(auto& shape:shapes)require(shape.certificate_bytes()==260&&shape.plaintext_bytes()==80&&shape.chunk_bytes()==0&&shape.address_bytes()==0,"shard owner profile");}
 uint64_t version(uint64_t key){auto old=directory_.lookup(checkpoint_.root(),key);require(!old||old->generation!=UINT64_MAX,"shard version exhausted");return old?old->generation+1:1;}
 void persist(bool global,const Bits& next_global,const std::map<size_t,Bits>& changed){std::vector<NativeShardCapture::Verified> tokens;
  if(global)tokens.push_back(capture_.seal(session_,false,0,version(0),{},copy(next_global)));
  for(auto& [slot,body]:changed){require(slot<UINT64_MAX,"shard slot overflow");tokens.push_back(capture_.seal(session_,true,slot+1,version(slot+1),next_global,copy(body)));}
  NativeShardCapture::stage(checkpoint_,std::move(tokens));
 }
 struct RestoreTag {};
 DurableOwner(RestoreTag,std::shared_ptr<void> persistence,AccountCheckpointCoordinator& coordinator,Checkpoint& checkpoint,Directory& directory,NativeShardCapture& capture,
  Session& session,Epoch epoch,Digest context,Digest manifest,Digest boot,Bits global,std::map<size_t,Bits> active,
  const AccountCheckpointCoordinator::CurrentHead& current,unsigned party)
 :persistence_(std::move(persistence)),coordinator_(coordinator),checkpoint_(checkpoint),directory_(directory),capture_(capture),session_(session),responses_(epoch,context,manifest,boot),
 sequence_(current.commit?current.commit->proposal.slot:0),global_(std::move(global)),active_(std::move(active)){
  require(party<5&&persistence_&&current.commit&&current.reservation&&checkpoint_.root()==current.commit->proposal.bundles[party]&&global_.size()==8306*8&&!active_.empty()&&active_.size()<=4,"authorized sharded owner domain");
  NativeOwnShareArchive::require_cells(global_);for(auto& [slot,body]:active_){require(slot<UINT64_MAX&&body.size()==12611*8,"restored shard width");NativeOwnShareArchive::require_cells(body);}accepted_=constant(3);
 }
 void register_authorized_resume(size_t slot,uint64_t lease,unsigned ordinal,const CertifiedPhase& send){live();require(active_.count(slot),"resume shard absent");responses_.install(slot,lease,ordinal,send);}

public:
 // Only an explicit fresh embedding may supply this initial material. It must
 // create a NEW account/domain; this constructor cannot activate restored roots.
 DurableOwner(std::shared_ptr<void> persistence,AccountCheckpointCoordinator& coordinator,Checkpoint& checkpoint,Directory& directory,NativeShardCapture& capture,
  Session& session,Epoch epoch,Digest context,Digest manifest,Digest boot,Bits initial_global,std::map<size_t,Bits> initial_active,const AccountCheckpointCoordinator::CurrentHead& current)
 :persistence_(std::move(persistence)),coordinator_(coordinator),checkpoint_(checkpoint),directory_(directory),capture_(capture),session_(session),responses_(epoch,context,manifest,boot),global_(std::move(initial_global)),active_(std::move(initial_active)){
  require(persistence_&&!current.commit&&!current.reservation&&checkpoint_.root()==directory_.genesis()&&boot!=Digest{}&&global_.size()==8306*8&&!active_.empty()&&active_.size()<=4,"fresh sharded owner domain");NativeOwnShareArchive::require_cells(global_);
  for(auto& [slot,body]:active_){require(slot<UINT64_MAX&&body.size()==12611*8,"fresh sharded owner dimensions");NativeOwnShareArchive::require_cells(body);}
  accepted_=constant(3);
 }
 ~DurableOwner()override{close();}
 const Bits& global()const{live();return global_;}const Bits& conversation(size_t slot)const{live();return active_.at(slot);}
 void reserve(const std::vector<size_t>& slots,const std::vector<VariableShape>& shapes,const std::vector<Store::Staged>& staged,const Bits& current,const Bits& final,uint64_t lease)override{
  try{live();require(!reserved_&&sequence_!=UINT64_MAX&&lease&&!slots.empty()&&slots.size()<=4&&slots.size()==staged.size()&&current.size()==64&&final.size()==64,"shard reserve phase");slots_=slots;same(slots,shapes);calls_.clear();tickets_.clear();auto next_global=copy(global_);replace(next_global,8298,final);std::map<size_t,Bits> changed;if(sequence_==0)for(auto& [slot,body]:active_)changed.emplace(slot,copy(body));
   for(size_t i=0;i<slots.size();++i){require(active_.count(slots[i]),"shard reserve selected slot");for(size_t j=0;j<i;++j)require(slots[j]!=slots[i],"shard duplicate selected slot");responses_.require_idle(slots[i]);auto body=copy(active_.at(slots[i]));calls_.push_back(copy(staged[i].input()));tickets_.push_back(staged[i].ticket());auto intent=constant(255);append(intent,calls_.back());require(intent.size()==612*8,"shard intent width");replace(body,6755,intent);changed.insert_or_assign(slots[i],std::move(body));}
   auto reads=directory_.read_bytes,writes=directory_.written_bytes,ciphertext=checkpoint_.changed_ciphertext_bytes;persist(true,next_global,changed);auto certificate=coordinator_.reserve({});require(certificate.proposal.slot==sequence_+1,"shard reserve certificate sequence");std::cerr<<"SHARDED_CHECKPOINT phase=reserve sequence="<<certificate.proposal.slot<<" changed_shards="<<changed.size()+1<<" directory_read_bytes="<<directory_.read_bytes-reads<<" directory_write_bytes="<<directory_.written_bytes-writes<<" changed_ciphertext_bytes="<<checkpoint_.changed_ciphertext_bytes-ciphertext<<"\n";global_=std::move(next_global);for(auto& [slot,body]:changed)active_.at(slot)=std::move(body);reserved_=true;
  }catch(...){close();throw;}
 }
 std::vector<Bits> bind(const std::vector<size_t>& slots,const std::vector<VariableShape>& shapes,std::vector<Bits> outputs)override{
  try{live();same(slots,shapes);require(reserved_&&outputs.size()==slots.size(),"shard bind phase");records_.clear();selected_.clear();for(size_t i=0;i<slots.size();++i){auto bound=session_.bind_canonical_record(slice(active_.at(slots[i]),69,5550),shapes[i],copy(calls_[i]),std::move(outputs[i]));session_.require_private_status(slice(bound.service_result,0,1));records_.push_back(std::move(bound.snapshot));selected_.push_back(std::move(bound.selected_state));outputs[i]=std::move(bound.service_result);}return outputs;
  }catch(...){close();throw;}
 }
 void commit(const std::vector<size_t>& slots,const std::vector<VariableShape>& shapes,const std::vector<Store::Candidate>& candidates)override{
  try{live();same(slots,shapes);require(reserved_&&candidates.size()==slots.size()&&records_.size()==slots.size()&&selected_.size()==slots.size(),"shard commit phase");uint64_t next=sequence_+1;unsigned ordinal=(next-1)%4;auto expected=generation(next);std::map<size_t,Bits> changed;
   for(size_t i=0;i<slots.size();++i){require(candidates[i].ticket()==tickets_[i],"shard candidate ticket");auto body=copy(active_.at(slots[i]));replace(body,69,records_[i]);replace(body,5619,candidates[i].next_state());replace(body,6230,selected_[i]);auto entry=constant(255);append(entry,candidates[i].payload());append(entry,candidates[i].request_id());append(entry,expected);
    auto out=session_.replace_reusable_outbox(ordinal,constant(255),slice(body,7367,5240),slice(body,12607,4),std::move(entry),expected);replace(body,7367,out.queue);replace(body,12607,out.dispositions);changed.emplace(slots[i],std::move(body));}
   auto reads=directory_.read_bytes,writes=directory_.written_bytes,ciphertext=checkpoint_.changed_ciphertext_bytes;persist(false,global_,changed);auto certificate=coordinator_.commit({});require(certificate.proposal.slot==next,"shard commit certificate sequence");
   std::cerr<<"SHARDED_CHECKPOINT phase=commit sequence="<<next<<" changed_shards="<<changed.size()<<" directory_read_bytes="<<directory_.read_bytes-reads<<" directory_write_bytes="<<directory_.written_bytes-writes<<" changed_ciphertext_bytes="<<checkpoint_.changed_ciphertext_bytes-ciphertext<<"\n";
   for(size_t i=0;i<slots.size();++i){responses_.install(slots[i],tickets_[i],ordinal,certificate);active_.at(slots[i])=std::move(changed.at(slots[i]));dirty_.erase(slots[i]);}
   sequence_=next;reserved_=false;calls_.clear();records_.clear();selected_.clear();tickets_.clear();slots_.clear();
  }catch(...){close();throw;}
 }
 void response_complete(size_t slot,uint64_t ticket)override{
  try{live();auto ordinal=responses_.complete(slot,ticket);replace(active_.at(slot),12607+ordinal,accepted_);dirty_.insert(slot);
   // Coalesce observed acceptance into the next certificate. Earlier restart
   // retains immutable uncertain bytes;2xx never proves recipient delivery.
  }catch(...){close();throw;}
 }
 bool checkpoint_outcomes()override{
  try{live();require(!reserved_&&sequence_!=UINT64_MAX,"outcome checkpoint phase");if(dirty_.empty())return false;
   std::map<size_t,Bits> changed;for(auto slot:dirty_)changed.emplace(slot,copy(active_.at(slot)));
   // ACK-only conversation changes are certified in Reserve. Commit inherits
   // every conversation reference and versions only the identical global body.
   // Thus this transition cannot be mistaken for a new wire generation.
   persist(false,global_,changed);auto reserved=coordinator_.reserve({});require(reserved.proposal.slot==sequence_+1,"outcome reserve sequence");
   persist(true,global_,{});auto committed=coordinator_.commit({});require(committed.proposal.slot==sequence_+1,"outcome commit sequence");sequence_=committed.proposal.slot;dirty_.clear();
   std::cerr<<"SHARDED_OUTCOME sequence="<<sequence_<<" cursor_advanced=0 producer_evaluated=0 conversation_commit_changes=0\n";return true;
  }catch(...){close();throw;}
 }
 void close()noexcept override{closed_=true;coordinator_.poison();global_.clear();active_.clear();accepted_.clear();calls_.clear();records_.clear();selected_.clear();tickets_.clear();slots_.clear();responses_.clear();dirty_.clear();}
};
}
