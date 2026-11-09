#pragma once
#include <cstddef>
#include <cstdint>
#include <list>
#include <map>
#include <memory>
#include <stdexcept>
#include <string>
// Storage policy only. Runtime instantiates Image exclusively with parsed
// public instructions + schedule metadata; never with Processor/prep/IO state.
namespace tls_public_code {
template<class Image> class Cache {
 struct Entry {std::unique_ptr<Image> image;size_t bytes;typename std::list<std::string>::iterator age;};
 std::map<std::string,Entry> entries;std::list<std::string> lru;
 size_t budget,limit,retained=0;
public:
 uint64_t hits=0,misses=0,evictions=0;
 Cache(size_t budget,size_t limit):budget(budget),limit(limit){if(!budget||!limit)throw std::invalid_argument("empty public cache budget");}
 Cache(const Cache&)=delete;Cache&operator=(const Cache&)=delete;
 size_t retained_bytes()const{return retained;}
 size_t size()const{return entries.size();}
 void clear()noexcept{entries.clear();lru.clear();retained=0;}
 std::unique_ptr<Image> take(const std::string&key){
  auto found=entries.find(key);if(found==entries.end()){++misses;return {};}
  ++hits;auto result=std::move(found->second.image);retained-=found->second.bytes;lru.erase(found->second.age);entries.erase(found);return result;
 }
 void put(std::string key,std::unique_ptr<Image> image,size_t bytes){
  if(!image||key.empty())throw std::invalid_argument("invalid public cache image");
  if(bytes>budget)return;
  auto old=entries.find(key);if(old!=entries.end()){retained-=old->second.bytes;lru.erase(old->second.age);entries.erase(old);}
  while(!lru.empty()&&(entries.size()>=limit||retained>budget-bytes)){
   auto found=entries.find(lru.front());retained-=found->second.bytes;entries.erase(found);lru.pop_front();++evictions;
  }
  lru.push_back(key);
  try{entries.emplace(key,Entry{std::move(image),bytes,std::prev(lru.end())});}
  catch(...){lru.pop_back();throw;}
  retained+=bytes;
 }
};
}
