#pragma once
#include "VariableShape.h"
#include "../PersistentSendFence.h"
#include <algorithm>
#include <cstdint>
#include <type_traits>
#include <utility>
namespace signal_mpc {
// Owns opaque same-worker shares. No branch or open on shared data. Temporary
// tombstone persistence refuses ALL restart/recovery; authenticated recoverable
// snapshots and globally consistent rollback/commit protection remain open.
template<class SharedBits> class VariableSendStore {
 static_assert(std::is_nothrow_move_assignable_v<SharedBits>&&std::is_nothrow_move_constructible_v<SharedBits>);
 VariableShape shape_;SharedBits input_;PersistentSendFence fence_;uint64_t ticket_=0;bool pending_=false,closed_=false;
 static void require(bool condition,const char* message){if(!condition)throw std::runtime_error(message);}
 static SharedBits bytes(const SharedBits& b,size_t offset,size_t count){
  require(b.size()%8==0&&offset<=b.size()/8&&count<=b.size()/8-offset,"private conversation slice bounds");
  return SharedBits(b.begin()+offset*8,b.begin()+(offset+count)*8);
 }
 static void append(SharedBits& out,const SharedBits& b){out.insert(out.end(),b.begin(),b.end());}
 void live()const{require(!closed_,"private conversation store closed");}
public:
 VariableSendStore(VariableShape shape,SharedBits initial,const std::string& fence_slot)
  :shape_(shape),input_(std::move(initial)),fence_(fence_slot){require(input_.size()==8*shape_.input_bytes(),"private conversation initial dimensions");}
 ~VariableSendStore(){close();}
 VariableSendStore(const VariableSendStore&)=delete;VariableSendStore& operator=(const VariableSendStore&)=delete;
 struct Produced{uint64_t ticket;SharedBits payload;SharedBits request_id;};
 // payload: kind1 || optional chunkIndex2+chunk32 || plaintext; timestampBE8.
 // Recipient/UAK/device/keys/request-ID remain retained, rather than supplied
 // afresh. Initial payload slots are unused storage; each call overlays them.
 template<class Evaluate>Produced produce(SharedBits payload,SharedBits timestamp,Evaluate&& evaluate){
  return produce_with_request_id(std::move(payload),std::move(timestamp),
    bytes(input_,shape_.metadata_offset()+40,8),std::forward<Evaluate>(evaluate));
 }
 // Embedding-only connection allocator ID. Reserve/commit it globally before
 // invoking this call; failures must never return that ID to the allocator.
 // No opening, RPC import, or equality test on these same-worker shares.
 template<class Evaluate>Produced produce_with_request_id(SharedBits payload,SharedBits timestamp,
     SharedBits request_id,Evaluate&& evaluate){
  return produce_with_checkpoint(std::move(payload),std::move(timestamp),std::move(request_id),
    std::forward<Evaluate>(evaluate),[](uint64_t,const SharedBits&){},
    [](uint64_t,const SharedBits&,const SharedBits&,const SharedBits&){});
 }
 // Internal embedding-only transaction boundary. A real recovery adapter must
 // durably reserve the complete account/intent before eval, then commit the
 // coherent canonical account + immutable outbox before any result escapes.
 // Existing produce paths deliberately remain tombstone-only, not durable.
 template<class Evaluate,class Reserve,class Commit>Produced produce_with_checkpoint(
     SharedBits payload,SharedBits timestamp,SharedBits request_id,Evaluate&& evaluate,
     Reserve&& reserve,Commit&& commit){
  live();require(!pending_,"private conversation response pending");require(ticket_!=UINT64_MAX,"private conversation ticket exhausted");
  require(payload.size()==8*(1+shape_.chunk_bytes()+shape_.plaintext_bytes())&&timestamp.size()==64&&request_id.size()==64,
    "private conversation payload dimensions");
  pending_=true;++ticket_;
  try{
   fence_.reserve();auto call_input=bytes(input_,0,shape_.input_bytes());
   const auto base=shape_.spqr_offset(),meta=shape_.metadata_offset();
   std::copy(payload.begin(),payload.begin()+8*(1+shape_.chunk_bytes()),call_input.begin()+8*(base+117));
   std::copy(payload.begin()+8*(1+shape_.chunk_bytes()),payload.end(),call_input.begin()+8*(base+182+shape_.chunk_bytes()));
   std::copy(timestamp.begin(),timestamp.end(),call_input.begin()+8*(meta+32));
   std::copy(request_id.begin(),request_id.end(),call_input.begin()+8*(meta+40));
   reserve(ticket_,call_input); // Actual private overlaid input, not a validity flag.
   auto output=evaluate(shape_,std::move(call_input));
   require(output.size()==8*shape_.output_bytes(),"private conversation result dimensions");
   auto current_id=std::move(request_id);
   auto next=bytes(input_,0,base+1);append(next,bytes(output,33,4));append(next,bytes(input_,base+5,36));
   append(next,bytes(output,1,32));append(next,bytes(output,37,32));append(next,bytes(output,69,4));
   append(next,bytes(input_,base+109,meta+40-(base+109)));append(next,bytes(output,73,8));append(next,bytes(input_,meta+48,9));
   auto payload=bytes(output,0,1);append(payload,bytes(output,81,2+shape_.frame_capacity()));
   require(next.size()==input_.size(),"private conversation next-state dimensions");
   commit(ticket_,next,payload,current_id); // Failure closes store; no output release.
   input_=std::move(next); // Commit selected state BEFORE payload becomes eligible for TLS.
   return{ticket_,std::move(payload),std::move(current_id)};
  }catch(...){close();throw;}
 }
 // Caller must validate the authenticated private response/correlation policy
 // before completing this ticket. Any failed/uncertain handoff closes the store;
 // no retry or rollback with a possibly consumed chain/key is permitted.
 void response_complete(uint64_t ticket){live();require(pending_&&ticket==ticket_,"stale private conversation response ticket");pending_=false;}
 void close()noexcept{closed_=true;pending_=false;input_.clear();}
};
}
