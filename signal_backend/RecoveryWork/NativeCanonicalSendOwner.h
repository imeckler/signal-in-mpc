#pragma once
// Candidate wiring only; not registered/admitted in the normal provider.
#include "NativeRecordBinding.h"
#include "../VariableServiceWork/NativeVariableService.h"
#include "../VariableServiceWork/VariableSendBatch.h"
namespace signal_mpc::recovery {
class NativeCanonicalSendOwner {
 using Bits=tls_mpc_worker::Bits;using Store=VariableSendStore<Bits>;
 Bits record_,service_snapshot_;Store store_;NativeVariableService& service_;NativeRecordBinding& binding_;bool closed_=false;
 static Bits clone(const Bits& bits){return Bits(bits.begin(),bits.end());}
 static VariableShape checked(VariableShape shape,const Bits& record){if(record.size()!=8*NativeRecordBinding::snapshot_bytes||shape.certificate_bytes()!=260||shape.plaintext_bytes()!=80||shape.chunk_bytes()!=0||shape.address_bytes()!=0)throw std::runtime_error("canonical sender dimensions/profile");return shape;}
public:
 struct Request {NativeCanonicalSendOwner* owner;Bits payload,timestamp,request_id;};
 struct Prestate {uint64_t ticket;const Bits& record;const Bits& call;const Bits& request_id;};
 struct Poststate {uint64_t ticket;const Bits& record;const Bits& service;const Bits& outbox;const Bits& request_id;};
 NativeCanonicalSendOwner(VariableShape shape,Bits record,Bits input,const std::string& fence,NativeVariableService& service,NativeRecordBinding& binding)
 :record_(std::move(record)),service_snapshot_(clone(input)),store_(checked(shape,record_),std::move(input),fence),service_(service),binding_(binding){}
 NativeCanonicalSendOwner(const NativeCanonicalSendOwner&)=delete;NativeCanonicalSendOwner&operator=(const NativeCanonicalSendOwner&)=delete;
 ~NativeCanonicalSendOwner(){close();}
 // EvaluateBatch must be the same-worker pinned batch service; no unsafe
 // concurrent Machine calls. Tx callbacks borrow views only for their call.
 // One FULL-account Reserve and Commit cover all distinct conversations.
 template<class EvaluateBatch,class Transaction>static std::vector<Store::Produced> produce_batch(std::vector<Request> requests,EvaluateBatch&& evaluate,Transaction& transaction){
  auto close_all=[&]()noexcept{for(auto& r:requests)if(r.owner)r.owner->close();};
  try{
   if(requests.empty()||requests.size()>64)throw std::runtime_error("canonical batch public capacity");
   std::vector<BatchSendRequest<Bits>> staged;staged.reserve(requests.size());
   for(auto& r:requests){if(!r.owner||r.owner->closed_||!r.owner->binding_.same_domain(requests[0].owner->binding_))throw std::runtime_error("canonical batch owner/domain");
    staged.push_back({&r.owner->store_,std::move(r.payload),std::move(r.timestamp),std::move(r.request_id)});}
   std::vector<Bits> next_records;next_records.resize(requests.size());
   return produce_batch_with_checkpoint(std::move(staged),
    [&](const auto& shapes,const std::vector<Store::Staged>& tokens){std::vector<Prestate> views;views.reserve(tokens.size());for(size_t i=0;i<tokens.size();++i)views.push_back({tokens[i].ticket(),requests[i].owner->record_,tokens[i].input(),tokens[i].request_id()});transaction.reserve(shapes,views);},
    [&](const auto& shapes,std::vector<Bits> calls){std::vector<Bits> saved;saved.reserve(calls.size());for(auto& call:calls)saved.push_back(clone(call));
     auto outputs=evaluate(shapes,std::move(calls));if(outputs.size()!=requests.size())throw std::runtime_error("canonical batch result count");
     for(size_t i=0;i<outputs.size();++i){auto& owner=*requests[i].owner;auto bound=owner.binding_.apply(clone(owner.record_),shapes[i],std::move(saved[i]),std::move(outputs[i]));next_records[i]=std::move(bound.snapshot);outputs[i]=std::move(bound.service_result);}return outputs;},
    [&](const auto& shapes,const std::vector<Store::Candidate>& candidates){
     std::vector<Bits> next_service;next_service.reserve(candidates.size());std::vector<Poststate> views;views.reserve(candidates.size());
     for(size_t i=0;i<candidates.size();++i){if(next_records[i].size()!=NativeRecordBinding::snapshot_bytes*8)throw std::runtime_error("canonical candidate missing");next_service.push_back(clone(candidates[i].next_state()));views.push_back({candidates[i].ticket(),next_records[i],candidates[i].next_state(),candidates[i].payload(),candidates[i].request_id()});}
     transaction.commit(shapes,views); // durable FULL account/outbox cert first
     for(size_t i=0;i<requests.size();++i){requests[i].owner->record_=std::move(next_records[i]);requests[i].owner->service_snapshot_=std::move(next_service[i]);}
    });
  }catch(...){close_all();throw;}
 }
 // B1 delegates to the identical transaction phases; callers can choose actual
 // B2/B4 evaluation without changing persistence or per-conversation ordering.
 template<class Transaction>Store::Produced produce(Bits payload,Bits timestamp,Bits id,Transaction& transaction){
  std::vector<Request> request;request.push_back({this,std::move(payload),std::move(timestamp),std::move(id)});
  auto outputs=produce_batch(std::move(request),[&](const auto& shapes,std::vector<Bits> calls){if(shapes.size()!=1||calls.size()!=1)throw std::runtime_error("canonical B1 dimensions");std::vector<Bits> out;out.push_back(service_.evaluate(shapes[0],std::move(calls[0])));return out;},transaction);return std::move(outputs[0]);
 }
 const Bits& record_snapshot()const{return record_;}const Bits& service_snapshot()const{return service_snapshot_;}
 void response_complete(uint64_t ticket){if(closed_)throw std::runtime_error("canonical sender closed");store_.response_complete(ticket);}
 void close()noexcept{closed_=true;store_.close();record_.clear();service_snapshot_.clear();}
};
}
