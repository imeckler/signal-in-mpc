#pragma once
// PUBLIC DISPOSABLE FIXTURES ONLY. Repeated bodies are intentional; each round
// has a distinct timestamp. No real credential/plaintext import or production API.
#include "PublicTextFixture.h"
#include <cstdint>
namespace signal_mpc {
struct PublicTextExtendedFixture {
 static std::vector<unsigned char> initial(size_t slot){return PublicTextFixture::initial(slot);}
 static std::vector<unsigned char> text_input(size_t slot,size_t round){
  if(slot>=2||round>=4)throw std::runtime_error("extended public text fixture index");
  auto raw=PublicTextFixture::text_input(slot,round%2);
  if(round>=2){uint64_t time=0;for(size_t i=51;i<59;++i)time=(time<<8)|raw[i];time+=4;for(size_t i=0;i<8;++i)raw[58-i]=time>>(8*i);}
  return raw;
 }
};
}
