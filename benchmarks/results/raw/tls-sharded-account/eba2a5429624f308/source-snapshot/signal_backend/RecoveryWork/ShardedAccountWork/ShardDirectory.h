#pragma once
#include "../CiphertextStore.h"
#include <functional>
#include <optional>
namespace signal_mpc::recovery::sharded {
// Public opaque-slot directory only. Secret shard bodies stay AEAD ciphertext.
// A fixed-depth persistent sparse tree rewrites at most64 branches per update.
struct Leaf {uint64_t key,generation,ciphertext_bytes;Digest ciphertext,schema,validation;};
class Directory {
 CiphertextStore& nodes_;Digest domain_;
 Bytes prefix(unsigned tag)const{auto b=label("SIGNAL-SHARD-DIRECTORY-V1");append(b,domain_);b.push_back(tag);return b;}
 Digest empty(unsigned depth)const{auto b=prefix(0);b.push_back(depth);return hash(b);}
 size_t branch_size()const{return prefix(1).size()+1+64;}
 size_t leaf_size()const{return prefix(2).size()+24+96;}
 std::pair<Digest,Digest> branch(const Digest& root,unsigned depth){
  if(root==empty(depth))return{empty(depth+1),empty(depth+1)};
  auto b=nodes_.get(root,branch_size());read_bytes+=b.size();auto p=prefix(1);require(std::equal(p.begin(),p.end(),b.begin())&&b[p.size()]==depth,"shard branch domain/depth");Digest l,r;std::copy_n(b.begin()+p.size()+1,32,l.begin());std::copy_n(b.begin()+p.size()+33,32,r.begin());return{l,r};
 }
 Leaf leaf(const Digest& root){auto b=nodes_.get(root,leaf_size());read_bytes+=b.size();auto p=prefix(2);require(std::equal(p.begin(),p.end(),b.begin()),"shard leaf domain");size_t n=p.size();Leaf x{read64(b.data()+n),read64(b.data()+n+8),read64(b.data()+n+16),{},{},{}};std::copy_n(b.begin()+n+24,32,x.ciphertext.begin());std::copy_n(b.begin()+n+56,32,x.schema.begin());std::copy_n(b.begin()+n+88,32,x.validation.begin());return x;}
 Digest update_at(const Digest& root,unsigned depth,const Leaf& value){
  if(depth==64){auto b=prefix(2);u64(b,value.key);u64(b,value.generation);u64(b,value.ciphertext_bytes);append(b,value.ciphertext);append(b,value.schema);append(b,value.validation);written_bytes+=b.size();return nodes_.put(b);}
  auto [l,r]=branch(root,depth);if((value.key>>(63-depth))&1)r=update_at(r,depth+1,value);else l=update_at(l,depth+1,value);
  auto b=prefix(1);b.push_back(depth);append(b,l);append(b,r);written_bytes+=b.size();return nodes_.put(b);
 }
public:
 uint64_t read_bytes=0,written_bytes=0;
 Directory(CiphertextStore& nodes,Digest domain):nodes_(nodes),domain_(domain){require(domain!=Digest{},"shard directory domain");}
 Digest genesis()const{return empty(0);}
 std::optional<Leaf> lookup(Digest root,uint64_t key){for(unsigned depth=0;depth<64;++depth){if(root==empty(depth))return{};auto [l,r]=branch(root,depth);root=((key>>(63-depth))&1)?r:l;}if(root==empty(64))return{};auto x=leaf(root);require(x.key==key,"shard leaf key");return x;}
 // The callback is a trusted embedding boundary: it must authenticate ciphertext
 // and consume actual computed private validity. Hashes alone do not prove it.
 // Returned program identity is recorded, together with predecessor provenance.
 using Validate=std::function<Digest(const std::optional<Leaf>&,const Leaf&)>;
 Digest replace(Digest root,Leaf value,const Validate& validate){
  require(bool(validate)&&value.ciphertext_bytes>0&&value.ciphertext!=Digest{}&&value.schema!=Digest{},"shard replacement dimensions");
  auto previous=lookup(root,value.key);require(value.generation==(previous?previous->generation+1:1)&&(!previous||previous->generation!=UINT64_MAX),"shard generation sequence");
  auto program=validate(previous,value);require(program!=Digest{},"shard private validity unavailable");
  auto provenance=prefix(3);append(provenance,root);append(provenance,program);u64(provenance,value.key);u64(provenance,value.generation);append(provenance,value.ciphertext);append(provenance,value.schema);value.validation=hash(provenance);
  return update_at(root,0,value);
 }
};
}
