#pragma once
#include "ShardCheckpoint.h"
#include "../../../handshake_backend/SessionWork/ErasedHostCall.h"
#include "../../../handshake_backend/NativeSession.h"
namespace signal_mpc::recovery::sharded {
// Actual Session-only capture. No supplied status/validator/program-hash API.
// The exact owned body is checked before local evaluations are serialized.
class NativeShardCapture {
 using Bits=tls_mpc_worker::Bits;
 const OwnShareBox& box_;CiphertextStore& bodies_;Epoch epoch_;Digest context_,manifest_,sharing_;unsigned party_;
 static Digest schema(bool conversation){return hash(label(conversation?"SIGNAL-SHARDED-ACCOUNT-V1/CONVERSATION12611/RECORD5550/SELECTED525/SERVICE611/INTENT612/OUTBOX4x1310/DISPOSITION4":"SIGNAL-SHARDED-ACCOUNT-V1/GLOBAL8306/CREDENTIAL38/IDENTITY65/STORE8195/CURSOR8"));}
 ShareDomain domain(bool conversation,uint64_t key,uint64_t generation)const{auto bytes=label("SIGNAL-SHARD-ENCRYPTED-DOMAIN-V1");append(bytes,schema(conversation));u64(bytes,key);return{party_,epoch_.number,generation,uint64_t(conversation?12611:8306)*8,context_,epoch_.digest(),manifest_,hash(bytes),sharing_};}
public:
 class Verified {
  friend class NativeShardCapture;Leaf leaf_;Digest program_;bool live_=true;
  Verified(Leaf leaf,Digest program):leaf_(leaf),program_(program){}
 public:
  Verified(const Verified&)=delete;Verified&operator=(const Verified&)=delete;
  Verified(Verified&& other)noexcept:leaf_(other.leaf_),program_(other.program_),live_(other.live_){other.live_=false;}
  Verified&operator=(Verified&&)=delete;
 };
 NativeShardCapture(const OwnShareBox& box,CiphertextStore& bodies,Epoch epoch,Digest context,Digest manifest,Digest sharing,unsigned party)
 :box_(box),bodies_(bodies),epoch_(epoch),context_(context),manifest_(manifest),sharing_(sharing),party_(party){require(party<5&&context!=Digest{}&&manifest!=Digest{}&&sharing!=Digest{},"native shard capture domain");epoch_.digest();}
 Verified seal(tls_mpc_worker::Session& session,bool conversation,uint64_t key,uint64_t generation,
  const Bits& current_global,Bits owned_body){
  require(tls_mpc_worker::ErasedHostCall::active()&&generation>0&&(conversation?key>0:key==0),"native shard capture phase/key");
  require(owned_body.size()==uint64_t(conversation?12611:8306)*8&&(!conversation||current_global.size()==8306*8),"native shard capture shape");
  NativeOwnShareArchive::require_cells(owned_body);
  auto program=session.check_shard_for_capture(conversation,conversation?current_global:owned_body,conversation?owned_body:Bits{},manifest_);
  require(program==NativeShardValidation::program_identity(conversation,manifest_),"native shard validator identity");
  auto d=domain(conversation,key,generation);SecretBytes local(owned_body.size()*16);
  for(size_t i=0;i<owned_body.size();++i)detail::encode_own_evaluation(local.data()+16*i,static_cast<const gf2n_long&>(owned_body[i][0].get_regs()[0]));
  auto ciphertext=box_.seal(d,QuarantinedEvaluations(std::move(local)));auto digest=bodies_.put(ciphertext);
  return Verified({key,generation,ciphertext.size(),digest,schema(conversation),{}},program);
 }
 // A one-shot token binds exact ciphertext/schema/key/generation to the actual
 // pinned computation above. Unchanged leaves inherit certified provenance.
 static void stage(Checkpoint& checkpoint,std::vector<Verified> verified){
  require(!verified.empty()&&verified.size()<=5,"native shard batch bounds");
  auto receipts=std::make_shared<std::map<uint64_t,std::pair<Leaf,Digest>>>();std::vector<Leaf> leaves;
  for(auto& token:verified){require(token.live_,"native shard validation token consumed");require(receipts->emplace(token.leaf_.key,std::make_pair(token.leaf_,token.program_)).second,"native shard duplicate key");leaves.push_back(token.leaf_);token.live_=false;}
  checkpoint.stage(std::move(leaves),[receipts](const std::optional<Leaf>&,const Leaf& value){auto at=receipts->find(value.key);require(at!=receipts->end(),"native shard validation token missing");auto& expected=at->second.first;
   require(expected.generation==value.generation&&expected.ciphertext_bytes==value.ciphertext_bytes&&expected.ciphertext==value.ciphertext&&expected.schema==value.schema,"native shard validation token mismatch");return at->second.second;});
 }
};
}
