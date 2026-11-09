#pragma once
#ifndef TLS_PINNED_PUBLIC_CODE_HELPER_H
#define TLS_PINNED_PUBLIC_CODE_HELPER_H
#include <sodium.h>
#include <array>
#include <fstream>
#include <map>
#include <sstream>
#include <stdexcept>
#include <string>
namespace tls_public_code {
inline std::string sha256(const std::string&bytes){
 unsigned char digest[crypto_hash_sha256_BYTES];char hex[crypto_hash_sha256_BYTES*2+1];
 crypto_hash_sha256(digest,reinterpret_cast<const unsigned char*>(bytes.data()),bytes.size());
 sodium_bin2hex(hex,sizeof(hex),digest,sizeof(digest));return hex;
}
inline std::string read(const std::string&path,const std::map<std::string,std::string>&expected){
 auto found=expected.find(path);if(found==expected.end()||found->second.size()!=64)throw std::runtime_error("public code missing from admitted closure");
 std::ifstream input(path,std::ios::binary);if(!input)throw std::runtime_error("admitted public code unavailable");
 std::string bytes;std::array<char,65536> buffer;
 while(input){input.read(buffer.data(),buffer.size());bytes.append(buffer.data(),input.gcount());if(bytes.size()>size_t(1024)*1024*1024)throw std::runtime_error("admitted public code exceeds bound");}
 if(!input.eof()||sha256(bytes)!=found->second)throw std::runtime_error("admitted public code digest mismatch");
 return bytes;
}
// Noncopying read-only stream over an owned SHA-verified byte snapshot. Parsing
// cannot race a second pathname read or observe bytes different from its hash.
class Buffer:public std::streambuf {
protected:
 pos_type seekoff(off_type off,std::ios_base::seekdir direction,std::ios_base::openmode which)override{
  if((which&std::ios_base::out)!=0)return pos_type(off_type(-1));
  auto size=egptr()-eback();auto base=direction==std::ios_base::beg?0:direction==std::ios_base::cur?gptr()-eback():size;
  if(off < -base || off > size-base)return pos_type(off_type(-1));
  setg(eback(),eback()+base+off,egptr());return pos_type(base+off);
 }
 pos_type seekpos(pos_type position,std::ios_base::openmode which)override{return seekoff(off_type(position),std::ios_base::beg,which);}
public:explicit Buffer(std::string&bytes){auto begin=bytes.data();setg(begin,begin,begin+bytes.size());}
};
class Stream:public std::istream {Buffer buffer;public:explicit Stream(std::string&bytes):std::istream(nullptr),buffer(bytes){rdbuf(&buffer);}};
}

#endif
