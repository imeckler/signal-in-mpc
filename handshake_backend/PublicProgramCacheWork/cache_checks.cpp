#include "PublicCodeCache.h"
#include "PinnedPublicCode.h"
#include <cassert>
#include <fstream>
#include <iostream>
struct PublicImage {int value;};
int main(int argc,char**argv){
 if(argc!=2)return 2;if(sodium_init()<0)return 2;
 tls_public_code::Cache<PublicImage> cache(10,2);auto put=[&](const char*k,int v,size_t n){cache.put(k,std::make_unique<PublicImage>(PublicImage{v}),n);};
 put("closure-a",1,6);put("closure-b",2,4);assert(cache.retained_bytes()==10);
 auto a=cache.take("closure-a");assert(a&&a->value==1&&cache.retained_bytes()==4);
 put("closure-a",3,6);put("closure-c",4,5);assert(!cache.take("closure-b")&&!cache.take("closure-a"));assert(cache.take("closure-c")->value==4);
 put("too-large",5,11);assert(cache.size()==0);put("same",6,4);put("same",7,5);assert(cache.size()==1&&cache.take("same")->value==7);
 put("config-1",8,4);assert(!cache.take("config-2"));cache.clear();assert(!cache.take("config-1")&&cache.retained_bytes()==0);
 std::string path=argv[1];{std::ofstream f(path,std::ios::binary);f<<"public-bytecode-v1";}
 std::map<std::string,std::string> pins{{path,tls_public_code::sha256("public-bytecode-v1")}};
 auto bytes=tls_public_code::read(path,pins);{std::ofstream f(path);f<<"modified-after-snapshot";}
 tls_public_code::Stream stream(bytes);std::string parsed;stream>>parsed;assert(parsed=="public-bytecode-v1");stream.clear();stream.seekg(7);assert(stream.tellg()==7);stream>>parsed;assert(parsed=="bytecode-v1");stream.clear();stream.seekg(0);assert(stream.tellg()==0);
 bool rejected=false;try{tls_public_code::read(path,pins);}catch(const std::runtime_error&){rejected=true;}assert(rejected);
 rejected=false;try{tls_public_code::read(path,{});}catch(const std::runtime_error&){rejected=true;}assert(rejected);
 std::cout<<"PASS public LRU/budget/replacement/config/mutation/snapshot checks\n";
}
