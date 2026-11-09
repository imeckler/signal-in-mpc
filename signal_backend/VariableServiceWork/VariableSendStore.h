#pragma once
#include "VariableShape.h"
#include "../PersistentSendFence.h"
#include <algorithm>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
namespace signal_mpc {
// Same-worker shares only. Default persistence remains a burn-on-restart fence.
// Staging/preview/install permits one atomic checkpoint for independent stores;
// it does not itself implement authenticated recoverable account persistence.
template<class SharedBits> class VariableSendStore {
 static_assert(std::is_nothrow_move_assignable_v<SharedBits>&&std::is_nothrow_move_constructible_v<SharedBits>);
 struct Lease {};
 enum class Phase {Idle,Staged,Prepared,AwaitResponse,Closed};
 VariableShape shape_;SharedBits input_;PersistentSendFence fence_;uint64_t ticket_=0;Phase phase_=Phase::Idle;
 std::shared_ptr<const Lease> lease_=std::make_shared<Lease>();
 static void require(bool condition,const char* message){if(!condition)throw std::runtime_error(message);}
 static SharedBits bytes(const SharedBits& b,size_t offset,size_t count){
  require(b.size()%8==0&&offset<=b.size()/8&&count<=b.size()/8-offset,"private conversation slice bounds");
  return SharedBits(b.begin()+offset*8,b.begin()+(offset+count)*8);
 }
 static void append(SharedBits& out,const SharedBits& b){out.insert(out.end(),b.begin(),b.end());}
 void live()const{require(phase_!=Phase::Closed,"private conversation store closed");}
public:
 using Bits=SharedBits;
 struct Produced{uint64_t ticket;SharedBits payload;SharedBits request_id;};
 class Staged {
  friend class VariableSendStore;
  std::weak_ptr<const Lease> lease_;uint64_t ticket_;SharedBits input_,id_;bool taken_=false;
  Staged(std::weak_ptr<const Lease> lease,uint64_t ticket,SharedBits input,SharedBits id)
   :lease_(std::move(lease)),ticket_(ticket),input_(std::move(input)),id_(std::move(id)){}
 public:
  Staged(const Staged&)=delete;Staged& operator=(const Staged&)=delete;
  Staged(Staged&&)noexcept=default;Staged& operator=(Staged&&)noexcept=default;
  uint64_t ticket()const{return ticket_;}
  const SharedBits& input()const{require(!taken_&&!lease_.expired(),"private staged input consumed");return input_;}
  const SharedBits& request_id()const{require(!lease_.expired(),"private staged owner unavailable");return id_;}
  SharedBits take_input(){require(!taken_&&!lease_.expired(),"private staged input consumed");taken_=true;return std::move(input_);}
  // Dropping a token leaves its store Staged, hence unable to send/ack again.
  // Weak identity never dereferences a destroyed owner or admits a reused address.
 };
 class Candidate {
  friend class VariableSendStore;
  std::weak_ptr<const Lease> lease_;uint64_t ticket_;SharedBits next_,payload_,id_;
  Candidate(std::weak_ptr<const Lease> lease,uint64_t ticket,SharedBits next,SharedBits payload,SharedBits id)
   :lease_(std::move(lease)),ticket_(ticket),next_(std::move(next)),payload_(std::move(payload)),id_(std::move(id)){}
 public:
  Candidate(const Candidate&)=delete;Candidate&operator=(const Candidate&)=delete;
  Candidate(Candidate&&)noexcept=default;Candidate&operator=(Candidate&&)noexcept=default;
  uint64_t ticket()const{return ticket_;}
  const SharedBits& next_state()const{return next_;}const SharedBits& payload()const{return payload_;}
  const SharedBits& request_id()const{return id_;}
 };
 VariableSendStore(VariableShape shape,SharedBits initial,const std::string& fence_slot)
  :shape_(shape),input_(std::move(initial)),fence_(fence_slot){require(input_.size()==8*shape_.input_bytes(),"private conversation initial dimensions");}
 ~VariableSendStore(){close();}
 VariableSendStore(const VariableSendStore&)=delete;VariableSendStore&operator=(const VariableSendStore&)=delete;
 const VariableShape& shape()const{return shape_;}
 Staged stage(SharedBits payload,SharedBits timestamp,SharedBits request_id){
  live();require(phase_==Phase::Idle,"private conversation response/stage pending");require(ticket_!=UINT64_MAX,"private conversation ticket exhausted");
  require(payload.size()==8*(1+shape_.chunk_bytes()+shape_.plaintext_bytes())&&timestamp.size()==64&&request_id.size()==64,"private conversation payload dimensions");
  phase_=Phase::Staged;++ticket_;
  try{fence_.reserve();auto call=bytes(input_,0,shape_.input_bytes());const auto base=shape_.spqr_offset(),meta=shape_.metadata_offset();
   std::copy(payload.begin(),payload.begin()+8*(1+shape_.chunk_bytes()),call.begin()+8*(base+117));
   std::copy(payload.begin()+8*(1+shape_.chunk_bytes()),payload.end(),call.begin()+8*(base+182+shape_.chunk_bytes()));
   std::copy(timestamp.begin(),timestamp.end(),call.begin()+8*(meta+32));std::copy(request_id.begin(),request_id.end(),call.begin()+8*(meta+40));
   return Staged(lease_,ticket_,std::move(call),std::move(request_id));
  }catch(...){close();throw;}
 }
 Candidate preview(Staged&& staged,SharedBits output){
  try{live();require(phase_==Phase::Staged&&staged.lease_.lock()==lease_&&staged.ticket_==ticket_&&staged.taken_,"private staged ownership/phase mismatch");
   require(output.size()==8*shape_.output_bytes(),"private conversation result dimensions");const auto base=shape_.spqr_offset(),meta=shape_.metadata_offset();
   auto next=bytes(input_,0,base+1);append(next,bytes(output,33,4));append(next,bytes(input_,base+5,36));
   append(next,bytes(output,1,32));append(next,bytes(output,37,32));append(next,bytes(output,69,4));
   append(next,bytes(input_,base+109,meta+40-(base+109)));append(next,bytes(output,73,8));append(next,bytes(input_,meta+48,9));
   auto payload=bytes(output,0,1);append(payload,bytes(output,81,2+shape_.frame_capacity()));require(next.size()==input_.size(),"private conversation next-state dimensions");
   phase_=Phase::Prepared;auto candidate=Candidate(lease_,ticket_,std::move(next),std::move(payload),std::move(staged.id_));staged.lease_.reset();return candidate;
  }catch(...){close();throw;}
 }
 void validate_candidate(const Candidate& candidate)const{
  live();require(phase_==Phase::Prepared&&candidate.lease_.lock()==lease_&&candidate.ticket_==ticket_&&candidate.next_.size()==input_.size(),"private candidate ownership/phase mismatch");
 }
 Produced install(Candidate&& candidate){
  try{validate_candidate(candidate);input_=std::move(candidate.next_);phase_=Phase::AwaitResponse;candidate.lease_.reset();
   return{ticket_,std::move(candidate.payload_),std::move(candidate.id_)};
  }catch(...){close();throw;}
 }
 template<class Evaluate>Produced produce(SharedBits payload,SharedBits timestamp,Evaluate&& evaluate){
  return produce_with_request_id(std::move(payload),std::move(timestamp),bytes(input_,shape_.metadata_offset()+40,8),std::forward<Evaluate>(evaluate));
 }
 template<class Evaluate>Produced produce_with_request_id(SharedBits payload,SharedBits timestamp,SharedBits request_id,Evaluate&& evaluate){
  return produce_with_checkpoint(std::move(payload),std::move(timestamp),std::move(request_id),std::forward<Evaluate>(evaluate),[](uint64_t,const SharedBits&){},[](uint64_t,const SharedBits&,const SharedBits&,const SharedBits&){});
 }
 template<class Evaluate,class Reserve,class Commit>Produced produce_with_checkpoint(SharedBits payload,SharedBits timestamp,SharedBits request_id,Evaluate&& evaluate,Reserve&& reserve,Commit&& commit){
  auto staged=stage(std::move(payload),std::move(timestamp),std::move(request_id));
  try{reserve(staged.ticket(),staged.input());auto output=evaluate(shape_,staged.take_input());auto candidate=preview(std::move(staged),std::move(output));
   commit(candidate.ticket(),candidate.next_state(),candidate.payload(),candidate.request_id());return install(std::move(candidate));
  }catch(...){close();throw;}
 }
 void response_complete(uint64_t ticket){live();require(phase_==Phase::AwaitResponse&&ticket==ticket_,"stale private conversation response ticket");phase_=Phase::Idle;}
 void close()noexcept{phase_=Phase::Closed;lease_.reset();input_.clear();}
};
}
