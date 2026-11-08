#pragma once
#include <cstddef>
#include <string>
#include <stdexcept>
namespace signal_mpc {
class SealedShape {
 size_t cert_,inner_;
 static size_t width(size_t n){size_t w=1;while(n>=128){n>>=7;++w;}return w;}
public:
 SealedShape(size_t cert,size_t inner):cert_(cert),inner_(inner){
  if(cert==0||cert>1024||inner==0||inner>4096)throw std::runtime_error("invalid sealed sender shape");}
 size_t certificate_bytes()const{return cert_;}
 size_t inner_bytes()const{return inner_;}
 // Identity secret32, retained sender public32, recipient public32,certificate,inner.
 size_t input_bytes()const{return 96+cert_+inner_;}
 size_t usmc_bytes()const{return 4+width(cert_)+cert_+width(inner_)+inner_;}
 size_t wire_bytes()const{return 92+width(usmc_bytes()+10)+usmc_bytes();}
 size_t output_bytes()const{return 1+wire_bytes();}
 std::string name()const{return "signal_sealed_v1_"+std::to_string(cert_)+"_"+std::to_string(inner_);}
 std::string descriptor()const{return "Programs/Functions/"+name()+"-sbv:["+
  std::to_string(8*input_bytes())+"x1]-sbv:["+std::to_string(8*output_bytes())+"x1]";}
};
}
