#pragma once
// PUBLIC recovery metadata only. No Signal secret/share serialization or restore.
#include <array>
#include <vector>
#include <map>
#include <memory>
#include <stdexcept>
#include <string>
#include <cstdint>
#include <algorithm>
#include <openssl/evp.h>
#include <openssl/crypto.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <cerrno>
namespace signal_mpc::recovery {
using Bytes=std::vector<unsigned char>;
using Digest=std::array<unsigned char,32>;
using Signature=std::array<unsigned char,64>;
inline void require(bool ok,const char* message){if(!ok)throw std::runtime_error(message);}
inline void append(Bytes& b,const Digest& d){b.insert(b.end(),d.begin(),d.end());}
inline void u64(Bytes& b,uint64_t n){for(int i=7;i>=0;--i)b.push_back((n>>(8*i))&255);}
inline uint64_t read64(const unsigned char* p){uint64_t n=0;for(int i=0;i<8;++i)n=(n<<8)|p[i];return n;}
inline Digest hash(const Bytes& b){Digest d;unsigned n=0;require(EVP_Digest(b.data(),b.size(),d.data(),&n,EVP_sha256(),nullptr)==1&&n==32,"recovery hash failed");return d;}
inline Bytes label(const char* text){return Bytes(text,text+std::char_traits<char>::length(text));}
struct Epoch {
 uint64_t number;std::array<Digest,5> members;Digest genesis;
 Digest digest()const{
  require(number!=0,"invalid recovery epoch");
  for(size_t i=0;i<5;++i)for(size_t j=0;j<i;++j)require(members[i]!=members[j],"duplicate recovery member key");
  auto b=label("tls-mpc-signal-recovery-epoch-v1");u64(b,number);for(auto& p:members)append(b,p);append(b,genesis);return hash(b);
 }
};
enum class Phase:unsigned char {Reserve=1,Commit=2,Acknowledge=3};
struct Proposal {
 Phase phase;uint64_t slot;Digest context,parent,attempt,manifest;
 // Ciphertext bundle digests include intent/full state/immutable outbox. This
 // class cannot validate or admit those blobs; actual import remains separate.
 std::array<Digest,5> bundles;
 Bytes encode(const Epoch& e)const{
  require(slot>0,"zero recovery slot");auto phase_byte=static_cast<unsigned char>(phase);require(phase_byte>=1&&phase_byte<=3,"invalid recovery phase");
  auto b=label("tls-mpc-signal-recovery-vote-v1");append(b,e.digest());b.push_back(phase_byte);u64(b,slot);
  append(b,context);append(b,parent);append(b,attempt);append(b,manifest);for(auto& d:bundles)append(b,d);return b;
 }
 Digest digest(const Epoch& e)const{return hash(encode(e));}
};
class Signer {
 using Key=std::unique_ptr<EVP_PKEY,decltype(&EVP_PKEY_free)>;Key key_;
public:
 explicit Signer(const Digest& private_seed):key_(EVP_PKEY_new_raw_private_key(EVP_PKEY_ED25519,nullptr,private_seed.data(),32),EVP_PKEY_free){require(bool(key_),"recovery signing key rejected");}
 Signer(const Signer&)=delete;Signer& operator=(const Signer&)=delete;
 Digest public_key()const{Digest d;size_t n=32;require(EVP_PKEY_get_raw_public_key(key_.get(),d.data(),&n)==1&&n==32,"recovery public key failed");return d;}
 Signature sign(const Bytes& message)const{
  std::unique_ptr<EVP_MD_CTX,decltype(&EVP_MD_CTX_free)> ctx(EVP_MD_CTX_new(),EVP_MD_CTX_free);require(bool(ctx),"recovery sign context failed");
  require(EVP_DigestSignInit(ctx.get(),nullptr,nullptr,nullptr,key_.get())==1,"recovery sign init failed");Signature out;size_t n=64;
  require(EVP_DigestSign(ctx.get(),out.data(),&n,message.data(),message.size())==1&&n==64,"recovery sign failed");return out;
 }
};
inline bool verify(const Digest& key,const Bytes& message,const Signature& signature){
 std::unique_ptr<EVP_PKEY,decltype(&EVP_PKEY_free)> p(EVP_PKEY_new_raw_public_key(EVP_PKEY_ED25519,nullptr,key.data(),32),EVP_PKEY_free);
 std::unique_ptr<EVP_MD_CTX,decltype(&EVP_MD_CTX_free)> ctx(EVP_MD_CTX_new(),EVP_MD_CTX_free);
 return p&&ctx&&EVP_DigestVerifyInit(ctx.get(),nullptr,nullptr,nullptr,p.get())==1&&EVP_DigestVerify(ctx.get(),signature.data(),64,message.data(),message.size())==1;
}
struct Vote {unsigned party;Signature signature;};
inline bool certificate(const Epoch& epoch,const Proposal& proposal,const std::vector<Vote>& votes){
 if(votes.size()<4||votes.size()>5)return false;auto message=proposal.encode(epoch);unsigned mask=0;
 for(auto& v:votes){if(v.party>=5||(mask&(1u<<v.party))||!verify(epoch.members[v.party],message,v.signature))return false;mask|=1u<<v.party;}
 return true;
}
struct Status {
 unsigned party;uint64_t highest_slot;Digest context,challenge,journal;Signature signature;
 Bytes message(const Epoch& epoch)const{require(party<5,"invalid recovery status party");auto b=label("tls-mpc-signal-recovery-status-v1");append(b,epoch.digest());b.push_back(party);u64(b,highest_slot);append(b,context);append(b,challenge);append(b,journal);return b;}
};
inline bool verify_status(const Epoch& epoch,const Digest& context,const Digest& challenge,const Status& status){
 return status.party<5&&status.context==context&&status.challenge==challenge&&verify(epoch.members[status.party],status.message(epoch),status.signature);
}
// A candidate durable no-double-sign primitive, NOT a complete recovery state
// machine. Caller must still validate phase chains, certificates, full snapshots
// and private share re-admission. Stable honest storage is an explicit assumption.
class VoteJournal {
 int fd_=-1;bool failed_=false;Epoch epoch_;Digest context_;unsigned party_;const Signer& signer_;
 std::map<std::pair<unsigned char,uint64_t>,Digest> votes_;Digest chain_{};
 static constexpr size_t record_size=1+8+32+32;
 void write_all(const Bytes& b){size_t n=0;while(n<b.size()){auto k=::write(fd_,b.data()+n,b.size()-n);if(k<0&&errno==EINTR)continue;require(k>0,"recovery journal write failed");n+=size_t(k);}require(::fsync(fd_)==0,"recovery journal sync failed");}
 Bytes header()const{auto b=label("SIGREC-JOURNAL-1");append(b,epoch_.digest());append(b,context_);b.push_back(party_);return b;}
 void load(){
  struct stat info;require(::fstat(fd_,&info)==0&&S_ISREG(info.st_mode)&&info.st_size>=0,"recovery journal not regular");require(info.st_size<=64*1024*1024,"recovery journal capacity");
  Bytes b(size_t(info.st_size));size_t n=0;while(n<b.size()){auto k=::pread(fd_,b.data()+n,b.size()-n,n);if(k<0&&errno==EINTR)continue;require(k>0,"recovery journal read failed");n+=size_t(k);}
  auto h=header();require(b.size()>=h.size()&&std::equal(h.begin(),h.end(),b.begin()),"recovery journal domain mismatch");chain_=hash(h);
  require((b.size()-h.size())%record_size==0,"torn recovery journal");
  for(size_t off=h.size();off<b.size();off+=record_size){
   auto phase=b[off];auto slot=read64(b.data()+off+1);require(phase>=1&&phase<=3&&slot>0,"invalid journal entry");Digest d,saved;std::copy_n(b.begin()+off+9,32,d.begin());std::copy_n(b.begin()+off+41,32,saved.begin());
   Bytes record(chain_.begin(),chain_.end());record.insert(record.end(),b.begin()+off,b.begin()+off+41);auto next=hash(record);require(saved==next,"recovery journal integrity failure");
   auto key=std::make_pair(phase,slot);require(votes_.emplace(key,d).second,"duplicate journal entry");chain_=next;
  }
 }
public:
 VoteJournal(const std::string& path,Epoch epoch,Digest context,unsigned party,const Signer& signer)
  :epoch_(epoch),context_(context),party_(party),signer_(signer){
  require(party<5&&signer.public_key()==epoch.members[party],"recovery member identity mismatch");epoch_.digest();
  auto split=path.find_last_of('/');auto dir=split==std::string::npos?".":path.substr(0,split);if(dir.empty())dir="/";auto name=split==std::string::npos?path:path.substr(split+1);
  require(!name.empty()&&name!="."&&name!="..","invalid recovery journal name");int parent=::open(dir.c_str(),O_RDONLY|O_DIRECTORY|O_CLOEXEC|O_NOFOLLOW);require(parent>=0,"recovery directory unavailable");
  bool created=false;fd_=::openat(parent,name.c_str(),O_RDWR|O_APPEND|O_CREAT|O_EXCL|O_CLOEXEC|O_NOFOLLOW,0600);
  if(fd_>=0)created=true;else if(errno==EEXIST)fd_=::openat(parent,name.c_str(),O_RDWR|O_APPEND|O_CLOEXEC|O_NOFOLLOW);
  if(fd_<0){::close(parent);throw std::runtime_error("recovery journal unavailable");}
  try{require(::flock(fd_,LOCK_EX|LOCK_NB)==0,"recovery journal already owned");
   if(created){auto h=header();write_all(h);require(::fsync(parent)==0,"recovery directory sync failed");}
   load();::close(parent);
  }catch(...){::close(parent);::close(fd_);fd_=-1;throw;}
 }
 ~VoteJournal(){if(fd_>=0)::close(fd_);}
 VoteJournal(const VoteJournal&)=delete;VoteJournal&operator=(const VoteJournal&)=delete;
 Vote vote(const Proposal& proposal){
  require(!failed_&&fd_>=0,"recovery journal poisoned");
  try{
  require(proposal.context==context_,"recovery context mismatch");auto message=proposal.encode(epoch_);auto digest=hash(message);auto key=std::make_pair(static_cast<unsigned char>(proposal.phase),proposal.slot);
  auto found=votes_.find(key);if(found!=votes_.end())require(found->second==digest,"recovery double-sign refused");
  else{require(votes_.size()<(64*1024*1024-header().size())/record_size,"recovery journal capacity");Bytes entry;entry.push_back(key.first);u64(entry,key.second);append(entry,digest);Bytes auth(chain_.begin(),chain_.end());auth.insert(auth.end(),entry.begin(),entry.end());auto next=hash(auth);append(entry,next);
   // Write+flush BEFORE the signature can escape. If signing fails, the vote
   // remains durably reserved and can only be reissued for this exact digest.
   write_all(entry);votes_.emplace(key,digest);chain_=next;
  }
  return{party_,signer_.sign(message)};
  }catch(...){failed_=true;if(fd_>=0)::close(fd_);fd_=-1;throw;}
 }
 Status status(const Digest& challenge)const{
  require(!failed_&&fd_>=0,"recovery journal poisoned");uint64_t high=0;for(auto& entry:votes_)high=std::max(high,entry.first.second);
  Status out{party_,high,context_,challenge,chain_,{}};out.signature=signer_.sign(out.message(epoch_));return out;
 }
 size_t count()const{return votes_.size();}
};
}
