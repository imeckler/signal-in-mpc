#pragma once
// Content-addressed immutable CIPHERTEXT files only. No plaintext/share API.
#include "Evidence.h"
#include <openssl/rand.h>
namespace signal_mpc::recovery {
class CiphertextStore {
 int directory_=-1;
 static constexpr size_t limit=32*1024*1024;
 static std::string hex(const unsigned char* p,size_t n){std::string out;const char* digits="0123456789abcdef";for(size_t i=0;i<n;++i){out+=digits[p[i]>>4];out+=digits[p[i]&15];}return out;}
 static std::string name(const Digest& digest){return "blob-"+hex(digest.data(),digest.size())+".box";}
public:
 explicit CiphertextStore(const std::string& directory){directory_=::open(directory.c_str(),O_RDONLY|O_DIRECTORY|O_CLOEXEC|O_NOFOLLOW);require(directory_>=0,"archive directory unavailable");}
 ~CiphertextStore(){if(directory_>=0)::close(directory_);}
 CiphertextStore(const CiphertextStore&)=delete;CiphertextStore&operator=(const CiphertextStore&)=delete;
 Bytes get(const Digest& expected,size_t expected_size)const{
  require(expected_size>0&&expected_size<=limit,"archive ciphertext size bounds");auto file=name(expected);int fd=::openat(directory_,file.c_str(),O_RDONLY|O_CLOEXEC|O_NOFOLLOW);require(fd>=0,"archive ciphertext unavailable");
  try{struct stat info;require(::fstat(fd,&info)==0&&S_ISREG(info.st_mode)&&info.st_size==static_cast<off_t>(expected_size),"archive ciphertext size/type mismatch");
   Bytes out(expected_size);size_t n=0;while(n<out.size()){auto k=::read(fd,out.data()+n,out.size()-n);if(k<0&&errno==EINTR)continue;require(k>0,"archive ciphertext read failed");n+=size_t(k);}require(hash(out)==expected,"archive ciphertext digest mismatch");::close(fd);return out;
  }catch(...){::close(fd);throw;}
 }
 Digest put(const Bytes& ciphertext){
  require(!ciphertext.empty()&&ciphertext.size()<=limit,"archive ciphertext size bounds");auto digest=hash(ciphertext);auto final=name(digest);
  std::array<unsigned char,16> random;require(RAND_bytes(random.data(),random.size())==1,"archive temporary entropy failed");auto temporary=".pending-"+hex(random.data(),random.size());
  int fd=::openat(directory_,temporary.c_str(),O_WRONLY|O_CREAT|O_EXCL|O_CLOEXEC|O_NOFOLLOW,0600);require(fd>=0,"archive temporary create failed");
  bool open=true;
  try{size_t n=0;while(n<ciphertext.size()){auto k=::write(fd,ciphertext.data()+n,ciphertext.size()-n);if(k<0&&errno==EINTR)continue;require(k>0,"archive ciphertext write failed");n+=size_t(k);}
   require(::fsync(fd)==0,"archive ciphertext sync failed");::close(fd);open=false;
   if(::linkat(directory_,temporary.c_str(),directory_,final.c_str(),0)<0){require(errno==EEXIST,"archive install failed");require(get(digest,ciphertext.size())==ciphertext,"archive immutable collision");}
   require(::fsync(directory_)==0,"archive install directory sync failed");require(::unlinkat(directory_,temporary.c_str(),0)==0,"archive temporary cleanup failed");require(::fsync(directory_)==0,"archive cleanup directory sync failed");return digest;
  }catch(...){if(open)::close(fd);::unlinkat(directory_,temporary.c_str(),0);throw;}
 }
};
}
