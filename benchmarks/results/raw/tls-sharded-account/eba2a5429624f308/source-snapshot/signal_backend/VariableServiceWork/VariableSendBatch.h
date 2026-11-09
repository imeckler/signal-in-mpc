#pragma once
#include "VariableSendStore.h"
#include <vector>
namespace signal_mpc {
template<class SharedBits>struct BatchSendRequest {
 VariableSendStore<SharedBits>* store;SharedBits payload,timestamp,request_id;
};
// Internal single-owner host coordinator. No concurrent Machine calls, opens or
// private-ID comparison. Connection allocator must reserve distinct IDs first.
// Reserve and Commit are EACH invoked once for the entire batch, enabling one
// durable account slot/fsync/certificate group and one retirement boundary.
template<class SharedBits,class Reserve,class Evaluate,class Commit>
std::vector<typename VariableSendStore<SharedBits>::Produced> produce_batch_with_checkpoint(
 std::vector<BatchSendRequest<SharedBits>> requests,Reserve&& reserve,Evaluate&& evaluate,Commit&& commit){
 using Store=VariableSendStore<SharedBits>;using Staged=typename Store::Staged;using Candidate=typename Store::Candidate;using Produced=typename Store::Produced;
 auto abort_all=[&]()noexcept{for(auto& r:requests)if(r.store)r.store->close();};
 try{
  if(requests.empty()||requests.size()>64)throw std::runtime_error("private batch public capacity");
  for(size_t i=0;i<requests.size();++i){if(!requests[i].store)throw std::runtime_error("private batch null store");
   for(size_t j=0;j<i;++j)if(requests[i].store==requests[j].store)throw std::runtime_error("private batch duplicate conversation");}
  std::vector<Staged> staged;std::vector<VariableShape> shapes;staged.reserve(requests.size());shapes.reserve(requests.size());
  for(auto& r:requests){shapes.push_back(r.store->shape());staged.push_back(r.store->stage(std::move(r.payload),std::move(r.timestamp),std::move(r.request_id)));}
  reserve(shapes,static_cast<const std::vector<Staged>&>(staged));
  std::vector<SharedBits> inputs;inputs.reserve(staged.size());for(auto& token:staged)inputs.push_back(token.take_input());
  auto outputs=evaluate(shapes,std::move(inputs));
  if(outputs.size()!=requests.size())throw std::runtime_error("private batch result count");
  std::vector<Candidate> candidates;std::vector<Produced> results;candidates.reserve(requests.size());results.reserve(requests.size());
  for(size_t i=0;i<requests.size();++i)candidates.push_back(requests[i].store->preview(std::move(staged[i]),std::move(outputs[i])));
  for(size_t i=0;i<requests.size();++i)requests[i].store->validate_candidate(candidates[i]);
  commit(shapes,static_cast<const std::vector<Candidate>&>(candidates));
  // All candidates/dimensions were checked and the whole checkpoint committed.
  // Returned payloads stay local until EVERY selected state has installed.
  for(size_t i=0;i<requests.size();++i)results.push_back(requests[i].store->install(std::move(candidates[i])));
  return results;
 }catch(...){abort_all();throw;}
}
}
