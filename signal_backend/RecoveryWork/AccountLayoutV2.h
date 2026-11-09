#pragma once
#include "AccountSchemaV1.h"
#include "NativeOwnShareArchive.h"
namespace signal_mpc::recovery {
// Versioned full bounded established-account share layout. Opaque key-store
// contents are preserved; fresh/prekey/SPQR/skipped-key operations stay queued.
class AccountLayoutV2 {
 unsigned conversations_;
public:
 static constexpr size_t credential_bytes=38,identity_bytes=65,global_store_bytes=8195,cursor_bytes=8;
 static constexpr size_t binding_bytes=69,record_bytes=5550,service_bytes=611,selected_bytes=525,intent_bytes=612,outbox_bytes=5208,disposition_bytes=4;
 explicit AccountLayoutV2(unsigned n):conversations_(n){require(n>=1&&n<=4,"account layout conversation capacity");}
 unsigned conversations()const noexcept{return conversations_;}
 static size_t global_width(unsigned tag){switch(tag){case 1:return credential_bytes;case 2:return identity_bytes;case 3:return global_store_bytes;case 4:return cursor_bytes;default:throw std::runtime_error("account global section");}}
 static size_t conversation_width(unsigned tag){switch(tag){case 10:return binding_bytes;case 11:return record_bytes;case 12:return service_bytes;case 13:return selected_bytes;case 14:return intent_bytes;case 15:return outbox_bytes;case 16:return disposition_bytes;default:throw std::runtime_error("account conversation section");}}
 AccountSchemaV1 schema()const{std::vector<SectionCapacity> sections;for(unsigned t=1;t<=4;++t)sections.push_back({AccountSection(t),0,8*global_width(t)});for(unsigned c=0;c<conversations_;++c)for(unsigned t=10;t<=16;++t)sections.push_back({AccountSection(t),c,8*conversation_width(t)});return {conversations_,std::move(sections)};}
 Digest encoding()const{auto bytes=label("SIGNAL-ACCOUNT-LAYOUT-V2/904c8dc/CCD128/credential-uuid16-password22/identity65/global-store-v1-cap8192/cursor64/binding69/canonical5550/service611/selected525/intent1+611/outbox4x1+1293+8/disposition4");append(bytes,schema().digest());return hash(bytes);}
 size_t index(unsigned conversation,unsigned tag)const{require(conversation<conversations_&&tag>=10&&tag<=16,"account section index");return 4+7*conversation+tag-10;}
 size_t byte_count()const{return schema().bits()/8;}
};
class OwnedAccountV2 {
 AccountLayoutV2 layout_;std::vector<tls_mpc_worker::Bits> sections_;
public:
 OwnedAccountV2(AccountLayoutV2 layout,std::vector<tls_mpc_worker::Bits> sections):layout_(layout),sections_(std::move(sections)){
  require(sections_.size()==4+7*layout_.conversations(),"account owned section completeness");
  for(unsigned t=1;t<=4;++t)require(sections_[t-1].size()==8*layout_.global_width(t),"account owned global width");
  for(unsigned c=0;c<layout_.conversations();++c)for(unsigned t=10;t<=16;++t)require(sections_[layout_.index(c,t)].size()==8*layout_.conversation_width(t),"account owned conversation width");
  for(auto& section:sections_)NativeOwnShareArchive::require_cells(section);
 }
 OwnedAccountV2(const OwnedAccountV2&)=delete;OwnedAccountV2&operator=(const OwnedAccountV2&)=delete;
 OwnedAccountV2(OwnedAccountV2&&)=default;OwnedAccountV2&operator=(OwnedAccountV2&&)=default;
 const AccountLayoutV2& layout()const noexcept{return layout_;}
 const tls_mpc_worker::Bits& global(unsigned tag)const{require(tag>=1&&tag<=4,"account global lookup");return sections_[tag-1];}
 const tls_mpc_worker::Bits& conversation(unsigned c,unsigned tag)const{return sections_[layout_.index(c,tag)];}
 void replace_global(unsigned tag,tls_mpc_worker::Bits values){require(tag>=1&&tag<=4&&values.size()==8*layout_.global_width(tag),"account global replacement width");NativeOwnShareArchive::require_cells(values);sections_[tag-1]=std::move(values);}
 void replace_conversation(unsigned c,unsigned tag,tls_mpc_worker::Bits values){require(values.size()==8*layout_.conversation_width(tag),"account conversation replacement width");NativeOwnShareArchive::require_cells(values);sections_[layout_.index(c,tag)]=std::move(values);}
 std::vector<const tls_mpc_worker::Bits*> references()const{std::vector<const tls_mpc_worker::Bits*> result;for(auto& section:sections_)result.push_back(&section);return result;}
 tls_mpc_worker::Bits flatten()const{tls_mpc_worker::Bits result;result.reserve(layout_.schema().bits());for(auto& section:sections_)result.insert(result.end(),section.begin(),section.end());return result;}
 OwnedAccountV2 clone()const{std::vector<tls_mpc_worker::Bits> sections;sections.reserve(sections_.size());for(auto& section:sections_)sections.emplace_back(section.begin(),section.end());return {layout_,std::move(sections)};}
};
}
