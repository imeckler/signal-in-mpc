#pragma once
#include "OwnShareBox.h"
namespace signal_mpc::recovery {
// Capacities and section ordering are public. Contents are LOCAL GF128
// evaluations, never reconstructed account plaintext. This codec is not a
// proof that retained Rust state agrees with the active circuit projections.
enum class AccountSection:uint16_t {
 Credentials=1,IdentityKeyPair=2,RegistrationAndPreKeyStores=3,GlobalRequestCursor=4,
 // Per-conversation repeated group, indexed publicly from zero.
 RecipientAndServiceBinding=10,CurrentAndPreviousSessionRecords=11,
 SelectedVariableSendInput=12,SelectedReceiveState=13,
 FrozenIntent=14,ImmutableOutbox=15,OutboxDisposition=16
};
struct SectionCapacity {AccountSection section;uint32_t conversation;uint64_t bits;};
class AccountSchemaV1 {
 std::vector<SectionCapacity> sections_;unsigned conversations_;
 static bool global(AccountSection s){return unsigned(s)>=1&&unsigned(s)<=4;}
 static bool per_conversation(AccountSection s){return unsigned(s)>=10&&unsigned(s)<=16;}
public:
 AccountSchemaV1(unsigned conversations,std::vector<SectionCapacity> sections)
 :sections_(std::move(sections)),conversations_(conversations){
  require(conversations>0&&conversations<=64,"account conversation capacity");
  require(sections_.size()==4+7*conversations,"account section completeness");
  uint64_t total=0;size_t at=0;
  auto check=[&](unsigned tag,unsigned conversation){const auto& x=sections_[at++];require(unsigned(x.section)==tag&&x.conversation==conversation&&x.bits>0&&x.bits%8==0,"account section order/width");require(x.bits<=1024*1024-total,"account archive capacity");total+=x.bits;};
  for(unsigned tag=1;tag<=4;++tag)check(tag,0);
  for(unsigned c=0;c<conversations;++c)for(unsigned tag=10;tag<=16;++tag)check(tag,c);
 }
 uint64_t bits()const{uint64_t n=0;for(auto& x:sections_)n+=x.bits;return n;}
 Bytes encode()const{auto b=label("SIGNAL-ACCOUNT-SHARE-SCHEMA-V1/CCD128/904c8dc");u64(b,conversations_);for(auto& x:sections_){u64(b,unsigned(x.section));u64(b,x.conversation);u64(b,x.bits);}return b;}
 Digest digest()const{return hash(encode());}
 QuarantinedEvaluations pack(std::vector<QuarantinedEvaluations> local)const{
  require(local.size()==sections_.size(),"account archive section count");SecretBytes bytes(bits()*16);size_t offset=0;
  for(size_t i=0;i<local.size();++i){require(local[i].bit_count()==sections_[i].bits,"account archive section width");auto& part=local[i].local_bytes();std::memcpy(bytes.data()+offset,part.data(),part.size());offset+=part.size();}
  return QuarantinedEvaluations(std::move(bytes));
 }
 std::vector<QuarantinedEvaluations> unpack(QuarantinedEvaluations local)const{
  require(local.bit_count()==bits(),"account archive total width");std::vector<QuarantinedEvaluations> out;out.reserve(sections_.size());size_t offset=0;
  for(auto& x:sections_){SecretBytes part(x.bits*16);std::memcpy(part.data(),local.local_bytes().data()+offset,part.size());offset+=part.size();out.emplace_back(std::move(part));}return out;
 }
};
}
