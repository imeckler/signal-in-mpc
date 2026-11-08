#pragma once
#include <cstddef>
#include <stdexcept>
#include <string>
namespace signal_mpc {
class VariableShape {
 size_t cert_,plain_;bool chunk_,addresses_;
public:
 VariableShape(size_t cert,size_t plain,bool chunk,bool addresses):cert_(cert),plain_(plain),chunk_(chunk),addresses_(addresses){
  if(cert<1||cert>1024||plain>1024||frame_capacity()>16384)throw std::runtime_error("invalid variable conversation shape");
 }
 size_t certificate_bytes()const{return cert_;}size_t plaintext_bytes()const{return plain_;}
 size_t chunk_bytes()const{return chunk_?34:0;}size_t address_bytes()const{return addresses_?36:0;}
 size_t spqr_bytes()const{return 182+chunk_bytes()+plain_+address_bytes();}
 size_t spqr_offset()const{return 32+cert_;}size_t metadata_offset()const{return spqr_offset()+spqr_bytes();}
 size_t input_bytes()const{return metadata_offset()+57;}
 size_t frame_capacity()const{
  size_t width=1;for(size_t n=cert_;n>=128;n>>=7)++width;
  auto inner=(plain_/16+1)*16+32+address_bytes()+(chunk_?52:17)+64;
  auto sealed=81+2+(cert_+width+1)+(inner+4)+10+4;
  return 4*((sealed+2)/3)+256+256+4+2+8;
 }
 size_t output_bytes()const{return 83+frame_capacity();}
 std::string name()const{return "signal_private_variable_conversation_"+std::to_string(cert_)+"_"+std::to_string(plain_)+"_"+std::to_string(chunk_)+"_"+std::to_string(addresses_);}
 std::string descriptor()const{return name()+"-sbv:["+std::to_string(8*input_bytes())+"x1]-sbv:["+std::to_string(8*output_bytes())+"x1]";}
};
}
