#pragma once
// Local encrypted OWN evaluations only. Decryption returns quarantine, not Bits
// or secure restore admission. No interpolation or host key reconstruction.
#include "Evidence.h"
#include <cstring>
namespace signal_mpc::recovery {
class SecretBytes {
 unsigned char* data_=nullptr;size_t size_=0;
public:
 explicit SecretBytes(size_t size):data_(static_cast<unsigned char*>(OPENSSL_malloc(size))),size_(size){require(data_||size==0,"private archive allocation failed");if(size)std::memset(data_,0,size);}
 ~SecretBytes(){if(data_)OPENSSL_clear_free(data_,size_);}
 SecretBytes(const SecretBytes&)=delete;SecretBytes&operator=(const SecretBytes&)=delete;
 SecretBytes(SecretBytes&& x)noexcept:data_(x.data_),size_(x.size_){x.data_=nullptr;x.size_=0;}
 SecretBytes&operator=(SecretBytes&& x)noexcept{if(this!=&x){if(data_)OPENSSL_clear_free(data_,size_);data_=x.data_;size_=x.size_;x.data_=nullptr;x.size_=0;}return *this;}
 unsigned char* data(){return data_;}const unsigned char* data()const{return data_;}size_t size()const{return size_;}
};
struct ShareDomain {
 unsigned party;uint64_t epoch,slot,bit_count;
 Digest context,membership,manifest,schema,sharing_epoch;
 Bytes header()const{
  require(party<5&&epoch>0&&slot>0&&bit_count>0&&bit_count<=1024*1024,"private archive domain bounds");
  auto b=label("SIGNAL-OWN-SHARES-SIV-1/CCD128/t2/n5/x1..5/LE128/x128+x7+x2+x+1");b.push_back(party);u64(b,epoch);u64(b,slot);u64(b,bit_count);
  append(b,context);append(b,membership);append(b,manifest);append(b,schema);append(b,sharing_epoch);return b;
 }
};
// Bytes are local GF(2^128) evaluations in little-endian polynomial basis,
// one128-bit evaluation per original wire bit. They are NOT decoded secret bits.
class QuarantinedEvaluations {
 SecretBytes bytes_;
public:
 explicit QuarantinedEvaluations(SecretBytes bytes):bytes_(std::move(bytes)){require(bytes_.size()%16==0,"private evaluation width");}
 QuarantinedEvaluations(QuarantinedEvaluations&&)=default;QuarantinedEvaluations&operator=(QuarantinedEvaluations&&)=default;
 QuarantinedEvaluations(const QuarantinedEvaluations&)=delete;QuarantinedEvaluations&operator=(const QuarantinedEvaluations&)=delete;
 const SecretBytes& local_bytes()const{return bytes_;}size_t bit_count()const{return bytes_.size()/16;}
 // Intentionally no conversion to NativeWorker Bits. A fresh private-MPC
 // consistency/bitness/re-sharing step must precede any provider admission.
};
class OwnShareBox {
 SecretBytes key_;
 struct Cipher {
  std::unique_ptr<EVP_CIPHER,decltype(&EVP_CIPHER_free)> cipher{EVP_CIPHER_fetch(nullptr,"AES-256-SIV",nullptr),EVP_CIPHER_free};
  std::unique_ptr<EVP_CIPHER_CTX,decltype(&EVP_CIPHER_CTX_free)> ctx{EVP_CIPHER_CTX_new(),EVP_CIPHER_CTX_free};
  Cipher(){require(cipher&&ctx,"AES256SIV archive provider unavailable");require(EVP_CIPHER_get_key_length(cipher.get())==64,"archive key width mismatch");}
 };
public:
 explicit OwnShareBox(const std::array<unsigned char,64>& local_storage_key):key_(64){std::memcpy(key_.data(),local_storage_key.data(),64);}
 OwnShareBox(const OwnShareBox&)=delete;OwnShareBox&operator=(const OwnShareBox&)=delete;
 Bytes seal(const ShareDomain& domain,const QuarantinedEvaluations& local)const{
  auto h=domain.header();require(local.bit_count()==domain.bit_count,"archive evaluation count mismatch");Cipher c;
  require(EVP_EncryptInit_ex2(c.ctx.get(),c.cipher.get(),key_.data(),nullptr,nullptr)==1,"archive seal init failed");int n=0,m=0;
  require(EVP_EncryptUpdate(c.ctx.get(),nullptr,&n,h.data(),int(h.size()))==1,"archive seal AAD failed");
  Bytes out=h;out.resize(h.size()+16+local.local_bytes().size()+16);
  require(EVP_EncryptUpdate(c.ctx.get(),out.data()+h.size()+16,&n,local.local_bytes().data(),int(local.local_bytes().size()))==1,"archive seal failed");
  require(EVP_EncryptFinal_ex(c.ctx.get(),out.data()+h.size()+16+n,&m)==1&&size_t(n+m)==local.local_bytes().size(),"archive seal final failed");
  require(EVP_CIPHER_CTX_ctrl(c.ctx.get(),EVP_CTRL_AEAD_GET_TAG,16,out.data()+h.size())==1,"archive tag failed");out.resize(h.size()+16+local.local_bytes().size());return out;
 }
 QuarantinedEvaluations open_quarantined(const ShareDomain& expected,const Bytes& box)const{
  auto h=expected.header();auto size=expected.bit_count*16;
  require(box.size()==h.size()+16+size&&std::equal(h.begin(),h.end(),box.begin()),"archive authentication failed");Cipher c;
  require(EVP_DecryptInit_ex2(c.ctx.get(),c.cipher.get(),key_.data(),nullptr,nullptr)==1,"archive open init failed");int n=0,m=0;
  require(EVP_CIPHER_CTX_ctrl(c.ctx.get(),EVP_CTRL_AEAD_SET_TAG,16,const_cast<unsigned char*>(box.data()+h.size()))==1,"archive authentication failed");
  require(EVP_DecryptUpdate(c.ctx.get(),nullptr,&n,h.data(),int(h.size()))==1,"archive authentication failed");
  SecretBytes plain(size+16);
  require(EVP_DecryptUpdate(c.ctx.get(),plain.data(),&n,box.data()+h.size()+16,int(size))==1,"archive authentication failed");
  require(EVP_DecryptFinal_ex(c.ctx.get(),plain.data()+n,&m)==1&&size_t(n+m)==size,"archive authentication failed");
  // Copy only authenticated bytes into the fixed owner. Any unauthenticated
  // temporary is cleared by SecretBytes on every failure/success path.
  SecretBytes exact(size);std::memcpy(exact.data(),plain.data(),size);return QuarantinedEvaluations(std::move(exact));
 }
};
}
