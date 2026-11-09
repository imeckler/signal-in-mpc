#pragma once
#include "EvidenceCodec.h"
#include <dirent.h>
#include <openssl/rand.h>
namespace signal_mpc::recovery {
// Public signed certificates only; secret share bundles use CiphertextStore.
class PublicCheckpointStore {
 int directory_=-1;
 static std::string hex(const Digest& value){std::string out;const char* chars="0123456789abcdef";for(auto byte:value){out+=chars[byte>>4];out+=chars[byte&15];}return out;}
 static std::string name(const Digest& id){return "phase-"+hex(id)+".cert";}
 static bool safe(const std::string& value){return value.size()==75&&value.substr(0,6)=="phase-"&&value.substr(70)==".cert"&&value.find_first_not_of("0123456789abcdef",6)>=70;}
public:
 explicit PublicCheckpointStore(const std::string& directory){directory_=::open(directory.c_str(),O_RDONLY|O_DIRECTORY|O_CLOEXEC|O_NOFOLLOW);require(directory_>=0,"public checkpoint directory unavailable");}
 ~PublicCheckpointStore(){if(directory_>=0)::close(directory_);}PublicCheckpointStore(const PublicCheckpointStore&)=delete;PublicCheckpointStore&operator=(const PublicCheckpointStore&)=delete;
 Bytes get(const Digest& id)const{
  auto path=name(id);int fd=::openat(directory_,path.c_str(),O_RDONLY|O_CLOEXEC|O_NOFOLLOW);if(fd<0){require(errno==ENOENT,"public checkpoint open failed");return {};}
  try{struct stat info;require(::fstat(fd,&info)==0&&S_ISREG(info.st_mode)&&info.st_size>0&&info.st_size<=4096,"public checkpoint file shape");Bytes out(size_t(info.st_size));size_t at=0;while(at<out.size()){auto n=::read(fd,out.data()+at,out.size()-at);if(n<0&&errno==EINTR)continue;require(n>0,"public checkpoint short read");at+=n;}::close(fd);return out;}catch(...){::close(fd);throw;}
 }
 void put(const Epoch& epoch,const CertifiedPhase& phase){auto bytes=encode_phase(epoch,phase);auto id=phase.proposal.digest(epoch);auto previous=get(id);if(!previous.empty()){require(decode_phase(epoch,previous).proposal.digest(epoch)==id,"public checkpoint certificate collision");return;}
  Digest random;require(RAND_bytes(random.data(),random.size())==1,"public checkpoint temporary entropy");auto temporary=".pending-"+hex(random);int fd=::openat(directory_,temporary.c_str(),O_WRONLY|O_CREAT|O_EXCL|O_CLOEXEC|O_NOFOLLOW,0600);require(fd>=0,"public checkpoint temporary create");bool open=true;
  try{size_t at=0;while(at<bytes.size()){auto n=::write(fd,bytes.data()+at,bytes.size()-at);if(n<0&&errno==EINTR)continue;require(n>0,"public checkpoint write failed");at+=n;}require(::fsync(fd)==0,"public checkpoint file sync");::close(fd);open=false;auto final=name(id);
   if(::linkat(directory_,temporary.c_str(),directory_,final.c_str(),0)<0){require(errno==EEXIST&&decode_phase(epoch,get(id)).proposal.digest(epoch)==id,"public checkpoint immutable install");}
   require(::fsync(directory_)==0,"public checkpoint directory sync");require(::unlinkat(directory_,temporary.c_str(),0)==0,"public checkpoint temporary unlink");require(::fsync(directory_)==0,"public checkpoint cleanup sync");
  }catch(...){if(open)::close(fd);::unlinkat(directory_,temporary.c_str(),0);throw;}
 }
 Bytes highest_commit(const Epoch& epoch,const Digest& context,const Digest& manifest)const{
  int fd=::dup(directory_);require(fd>=0,"public checkpoint directory duplicate");DIR* dir=::fdopendir(fd);if(!dir){::close(fd);throw std::runtime_error("public checkpoint directory scan");}
  ::rewinddir(dir);Bytes best;Digest best_id{};uint64_t high=0;size_t count=0;
  try{while(auto* entry=::readdir(dir)){std::string path(entry->d_name);if(!safe(path))continue;require(++count<=1000000,"public checkpoint file count");Digest id;for(size_t i=0;i<32;++i)id[i]=std::stoul(path.substr(6+2*i,2),nullptr,16);auto bytes=get(id);auto phase=decode_phase(epoch,bytes);require(phase.proposal.digest(epoch)==id&&phase.proposal.context==context&&phase.proposal.manifest==manifest,"public checkpoint certificate domain");
   if(phase.proposal.phase==Phase::Commit&&phase.proposal.slot>high){high=phase.proposal.slot;best_id=id;best=std::move(bytes);}else if(phase.proposal.phase==Phase::Commit&&phase.proposal.slot==high)require(id==best_id,"public checkpoint conflicting heads");}
   ::closedir(dir);return best;
  }catch(...){::closedir(dir);throw;}
 }
};
}
