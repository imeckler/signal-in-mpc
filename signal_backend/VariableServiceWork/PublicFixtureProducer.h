#pragma once
// PUBLIC DISPOSABLE FIXTURE ONLY. Never a production initialization/import API.
#include "NativeVariableService.h"
#include "VariableSendStore.h"
#include <vector>
namespace signal_mpc {
struct PublicVariableFixture {
 static std::vector<unsigned char> initial(){
  const std::string text=
    "a87f0d9eaea4d4bf5438b887e34d0cf87e7f98d97da70eff001850487b2cae630abf0110011900204aa9d10100002221"
    "054b200536e27622b684a45207bf001de9d867a80828a52a227f0d5002156e097e2a690a250801122105b5d3124be473"
    "78e836eaa45f611101dafbc87479963d65dfd0d47e4d304ce302124051175f1f3cdde6a3ae6e2643d3d9f1d7d3fa09ea"
    "9869975d3a2f1ba808e2001383b4ac3cd5eb0fdbe810c5367b6f2e32a7580b9799b50256cdc69ae0c1f3df0e32243030"
    "3131323233332d343435352d363637372d383839392d6161626263636464656566661240d8a57cb295711013ae63788f"
    "66e181a5d972ed40c2ccf054499937582590e657bde92f09cfaf3cd30955f60ce085cb4e85a314082601ef993e2154f6"
    "549bf507040000007f0000007f61495c6d3b3215b0b6d10a73415f8e271852515c5808f7fbb970e1156e87ba50c901e6"
    "b2fedd436fa6c9b4b6261a785f01af17571d8b0e0cd5527366e55da368e449b8b68b121f83e2c864b88cdf7db05280c5"
    "f32914349361bb349f28e89dfd0000007e000000000000007f004b200536e27622b684a45207bf001de9d867a80828a5"
    "2a227f0d5002156e097e5e9e5d4757138081f4f40bd032f284c4453aead5ccc81a649a99bdd6afe44319ffeeddccbbaa"
    "99887766554433221100103ce6993f721dd949a1194fefaa28b8000001ba60d33800000000000000007f0100003fff11"
    "1d3547";
  std::vector<unsigned char> out;for(size_t i=0;i<text.size();i+=2)out.push_back(std::stoul(text.substr(i,2),nullptr,16));return out;
 }
 static std::vector<unsigned char> timestamp(){auto b=initial();VariableShape s(260,0,false,false);return {b.begin()+s.metadata_offset()+32,b.begin()+s.metadata_offset()+40};}
};
template<class SharedBits>class PublicVariableProducer {
 VariableShape shape_{260,0,false,false};VariableSendStore<SharedBits> store_;size_t produced_=0;bool closed_=false;
public:
 template<class PublicBits>PublicVariableProducer(PublicBits&& public_bits,const std::string& slot)
  :store_(shape_,public_bits(PublicVariableFixture::initial()),slot){}
 const VariableShape& shape()const{return shape_;}
 template<class Evaluate,class PublicBits>typename VariableSendStore<SharedBits>::Produced
 produce(Evaluate&& evaluate,PublicBits&& public_bits,SharedBits timestamp){
  if(closed_||produced_>=2){close();throw std::runtime_error("public variable fixture exhausted");}
  try{auto out=store_.produce(public_bits(std::vector<unsigned char>{0}),std::move(timestamp),std::forward<Evaluate>(evaluate));++produced_;return out;}
  catch(...){close();throw;}
 }
 void response_complete(uint64_t ticket){try{store_.response_complete(ticket);}catch(...){close();throw;}}
 void close()noexcept{closed_=true;store_.close();}
};
}
