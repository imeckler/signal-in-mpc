#pragma once
#include "Shape.h"
namespace signal_mpc {
class ServiceShape {
 SealedShape sealed_;
 size_t dw_,rw_,tw_,iw_;
 static size_t width(size_t n){size_t w=1;while(n>=128){n>>=7;++w;}return w;}
 static size_t field(size_t n){return 1+width(n)+n;}
public:
 ServiceShape(size_t cert,size_t inner,size_t dw,size_t rw,size_t tw,size_t iw)
  :sealed_(cert,inner),dw_(dw),rw_(rw),tw_(tw),iw_(iw){
  if(dw<1||dw>3||rw<1||rw>10||tw<1||tw>20||iw<1||iw>10)throw std::runtime_error("invalid relay width profile");}
 size_t certificate_bytes()const{return sealed_.certificate_bytes();}
 size_t inner_bytes()const{return sealed_.inner_bytes();}
 size_t input_bytes()const{return sealed_.input_bytes()+57;}
 size_t output_bytes()const{
  size_t body=132+4*((sealed_.wire_bytes()+2)/3)+dw_+rw_+tw_;
  size_t request=field(3)+field(61)+field(body)+1+iw_+field(30)+field(49);
  size_t envelope=2+field(request);
  return 1+4+4+envelope;
 }
 std::string name()const{return "signal_private_sealed_relay_"+std::to_string(certificate_bytes())+"_"+
  std::to_string(inner_bytes())+"_"+std::to_string(dw_)+"_"+std::to_string(rw_)+"_"+std::to_string(tw_)+"_"+std::to_string(iw_);}
 std::string descriptor()const{return "Programs/Functions/"+name()+"-sbv:["+
  std::to_string(8*input_bytes())+"x1]-sbv:["+std::to_string(8*output_bytes())+"x1]";}
};
}
