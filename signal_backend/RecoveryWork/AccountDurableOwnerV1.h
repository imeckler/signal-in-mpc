#pragma once
#include "AccountCheckpointCoordinator.h"
#include "AccountLayoutV2.h"
#include "../../handshake_backend/WebSocketWork/NativeConversation.h"
#include <map>
namespace signal_mpc::recovery {
// Candidate concrete whole-layout owner for the existing bounded established
// no-chunk profile. Public certificate slots1..4 select immutable outbox cells;
// compaction/frozen-reservation resume/full session transitions remain required.
class AccountDurableOwnerV1 final : public tls_mpc_worker::DurableConversationHooks {
 using Bits=tls_mpc_worker::Bits;using Session=tls_mpc_worker::Session;
 using Store=VariableSendStore<Bits>;
 std::shared_ptr<void> persistence_;AccountCheckpointCoordinator& coordinator_;
 std::optional<OwnedAccountV2> account_;Session* session_=nullptr;uint64_t slot_;bool closed_=false,reserved_=false;
 std::vector<size_t> slots_;std::vector<Bits> calls_,records_,selected_;
 std::vector<uint64_t> tickets_;std::map<std::pair<size_t,uint64_t>,size_t> responses_;
 static Bits copy(const Bits& value){return {value.begin(),value.end()};}
 static Bits slice(const Bits& value,size_t offset,size_t count){require(offset+count<=value.size()/8,"account owner slice");return {value.begin()+8*offset,value.begin()+8*(offset+count)};}
 static void append(Bits& a,const Bits& b){a.insert(a.end(),b.begin(),b.end());}
 Bits constant(unsigned byte){require(session_,"account owner fresh session absent");return session_->share_public_constants({static_cast<unsigned char>(byte)});}
 void live(){require(!closed_&&account_&&session_,"account owner unavailable");}
 void same(const std::vector<size_t>& slots,const std::vector<VariableShape>& shapes)const{
  require(slots==slots_&&shapes.size()==slots.size(),"account staged group mismatch");
  for(auto& shape:shapes)require(shape.certificate_bytes()==260&&shape.plaintext_bytes()==80&&shape.chunk_bytes()==0&&shape.address_bytes()==0,"account owner unsupported profile");
 }
public:
 AccountDurableOwnerV1(std::shared_ptr<void> persistence,AccountCheckpointCoordinator& coordinator,OwnedAccountV2 account,uint64_t current_slot)
 :persistence_(std::move(persistence)),coordinator_(coordinator),account_(std::move(account)),slot_(current_slot){require(persistence_&&current_slot>0&&current_slot<=4,"account owner certified slot/profile");}
 void attach_fresh_session(Session& session){require(!closed_&&!session_,"account owner session already attached");session_=&session;}
 const OwnedAccountV2& snapshot()const{require(!closed_&&bool(account_),"account owner snapshot unavailable");return *account_;}
 void register_resume(size_t slot,uint64_t lease,size_t ordinal){live();require(slot<account_->layout().conversations()&&lease&&ordinal<4,"account resume lease domain");require(responses_.emplace(std::make_pair(slot,lease),ordinal).second,"account duplicate resume lease");}
 void reserve(const std::vector<size_t>& slots,const std::vector<VariableShape>& shapes,const std::vector<Store::Staged>& staged,const Bits& current,const Bits& final,uint64_t lease)override{
  try{live();require(!reserved_&&slot_<4&&lease&&slots.size()==staged.size()&&slots.size()==shapes.size()&&!slots.empty()&&slots.size()<=4&&current.size()==64&&final.size()==64,"account reserve phase/capacity");
   slots_=slots;same(slots,shapes);auto next=account_->clone();next.replace_global(4,copy(final));calls_.clear();tickets_.clear();
   for(size_t i=0;i<slots.size();++i){require(slots[i]<next.layout().conversations(),"account reserve slot");for(size_t j=0;j<i;++j)require(slots[j]!=slots[i],"account duplicate slot");
    calls_.push_back(copy(staged[i].input()));tickets_.push_back(staged[i].ticket());Bits intent=constant(255);append(intent,calls_.back());next.replace_conversation(slots[i],14,std::move(intent));}
   // Session's restored cursor owns current, and only invokes this once for the
   // exact frozen staged group. One certificate burns the entire final range.
   auto certificate=coordinator_.reserve(next.references());require(certificate.proposal.slot==slot_+1,"account reserve certificate slot");account_=std::move(next);reserved_=true;
  }catch(...){close();throw;}
 }
 std::vector<Bits> bind(const std::vector<size_t>& slots,const std::vector<VariableShape>& shapes,std::vector<Bits> outputs)override{
  try{live();same(slots,shapes);require(reserved_&&outputs.size()==slots.size(),"account bind phase");records_.clear();selected_.clear();
   for(size_t i=0;i<slots.size();++i){auto bound=session_->bind_canonical_record(copy(account_->conversation(slots[i],11)),shapes[i],copy(calls_[i]),std::move(outputs[i]));
    session_->require_private_status(slice(bound.service_result,0,1));records_.push_back(std::move(bound.snapshot));selected_.push_back(std::move(bound.selected_state));outputs[i]=std::move(bound.service_result);}
   return outputs;
  }catch(...){close();throw;}
 }
 void commit(const std::vector<size_t>& slots,const std::vector<VariableShape>& shapes,const std::vector<Store::Candidate>& candidates)override{
  try{live();same(slots,shapes);require(reserved_&&candidates.size()==slots.size()&&records_.size()==slots.size()&&selected_.size()==slots.size(),"account commit phase");auto next=account_->clone();
   for(size_t i=0;i<slots.size();++i){require(candidates[i].ticket()==tickets_[i],"account candidate ticket mismatch");next.replace_conversation(slots[i],11,std::move(records_[i]));next.replace_conversation(slots[i],13,std::move(selected_[i]));next.replace_conversation(slots[i],12,copy(candidates[i].next_state()));
    Bits entry=constant(255);append(entry,candidates[i].payload());append(entry,candidates[i].request_id());require(entry.size()==1302*8,"account actual outbox dimensions");
    auto queue=copy(next.conversation(slots[i],15));std::copy(entry.begin(),entry.end(),queue.begin()+slot_*1302*8);next.replace_conversation(slots[i],15,std::move(queue));
    auto disposition=copy(next.conversation(slots[i],16));auto unsent=constant(1);std::copy(unsent.begin(),unsent.end(),disposition.begin()+slot_*8);next.replace_conversation(slots[i],16,std::move(disposition));
   }
   auto certificate=coordinator_.commit(next.references());require(certificate.proposal.slot==slot_+1,"account commit certificate slot");
   for(size_t i=0;i<slots.size();++i)require(responses_.emplace(std::make_pair(slots[i],tickets_[i]),slot_).second,"account response ticket collision");
   ++slot_;account_=std::move(next);reserved_=false;calls_.clear();records_.clear();selected_.clear();slots_.clear();tickets_.clear();
  }catch(...){close();throw;}
 }
 void response_complete(size_t slot,uint64_t ticket)override{
  try{live();auto found=responses_.find({slot,ticket});require(found!=responses_.end(),"account response lease unavailable");auto values=copy(account_->conversation(slot,16));auto accepted=constant(3);std::copy(accepted.begin(),accepted.end(),values.begin()+found->second*8);account_->replace_conversation(slot,16,std::move(values));responses_.erase(found);
   // This observed disposition is coalesced into the next certified snapshot.
   // A crash before it leaves the old immutable uncertain outbox resumable.
  }catch(...){close();throw;}
 }
 void close()noexcept override{closed_=true;coordinator_.poison();account_.reset();calls_.clear();records_.clear();selected_.clear();tickets_.clear();slots_.clear();responses_.clear();session_=nullptr;}
};
}
