// PUBLIC MOCK BITS ONLY: verifies host slicing/ownership/failure transitions,
// not cryptography, native runtime, or secret-share reconstruction behavior.
#include "VariableSendStore.h"
#include <cassert>
#include <iostream>
#include <vector>
using Bits=std::vector<unsigned char>;
static Bits bits(const std::vector<unsigned char>& bytes){Bits out;for(auto b:bytes)for(int i=7;i>=0;--i)out.push_back((b>>i)&1);return out;}
static std::vector<unsigned char> bytes(const Bits& b){assert(b.size()%8==0);std::vector<unsigned char> out(b.size()/8);for(size_t i=0;i<b.size();++i)out[i/8]|=b[i]<<(7-i%8);return out;}
template<class F>static void rejected(F f){bool yes=false;try{f();}catch(const std::exception&){yes=true;}assert(yes);}
static void put32(std::vector<unsigned char>& b,size_t p,uint32_t n){for(size_t i=0;i<4;++i)b[p+i]=n>>(8*(3-i));}
static void put64(std::vector<unsigned char>& b,size_t p,uint64_t n){for(size_t i=0;i<8;++i)b[p+i]=n>>(8*(7-i));}
int main(int argc,char**argv){assert(argc==2);unsigned profiles=0;
 for(size_t cert:{size_t(1),size_t(127),size_t(128),size_t(1024)})for(size_t plain:{size_t(0),size_t(1024)})for(bool chunk:{false,true})for(bool address:{false,true}){
  signal_mpc::VariableShape shape(cert,plain,chunk,address);const auto base=shape.spqr_offset(),meta=shape.metadata_offset();
  std::vector<unsigned char> initial(shape.input_bytes());for(size_t i=0;i<initial.size();++i)initial[i]=i%251;
  put32(initial,base+1,127);put32(initial,base+105,126);put64(initial,meta+40,127);
  auto current=initial;const auto slot=std::string(argv[1])+"/slot-"+std::to_string(profiles);
  signal_mpc::VariableSendStore<Bits> store(shape,bits(initial),slot);
  std::vector<unsigned char> payload(1+shape.chunk_bytes()+plain,31),timestamp(8,42);
  auto expected_input=[&]{auto value=current;std::copy(payload.begin(),payload.begin()+1+shape.chunk_bytes(),value.begin()+base+117);
   std::copy(payload.begin()+1+shape.chunk_bytes(),payload.end(),value.begin()+base+182+shape.chunk_bytes());
   std::copy(timestamp.begin(),timestamp.end(),value.begin()+meta+32);return value;};
  auto evaluate=[&](const signal_mpc::VariableShape& s,Bits input){assert(s.descriptor()==shape.descriptor());assert(bytes(input)==expected_input());
   std::vector<unsigned char> output(shape.output_bytes());output[0]=255;
   for(size_t i=0;i<32;++i){output[1+i]=current[base+41+i]^0x5a;output[37+i]=current[base+73+i]^0x69;}
   const auto step=current[base+4]==127?0:1;put32(output,33,128+step);put32(output,69,127+step);put64(output,73,128+step);
   output[81]=0;output[82]=3;output[83]=1;output[84]=0;output[85]=2;
   std::copy(output.begin()+1,output.begin()+33,current.begin()+base+41);std::copy(output.begin()+33,output.begin()+37,current.begin()+base+1);
   std::copy(output.begin()+37,output.begin()+69,current.begin()+base+73);std::copy(output.begin()+69,output.begin()+73,current.begin()+base+105);
   std::copy(output.begin()+73,output.begin()+81,current.begin()+meta+40);return bits(output);};
  for(unsigned step=0;step<2;++step){auto p=store.produce(bits(payload),bits(timestamp),evaluate);assert(p.ticket==step+1);
   std::vector<unsigned char> id(8);put64(id,0,127+step);assert(bytes(p.request_id)==id);
   auto wire=bytes(p.payload);assert(wire.size()==shape.frame_capacity()+3&&wire[0]==255&&wire[1]==0&&wire[2]==3&&wire[3]==1&&wire[4]==0&&wire[5]==2);
   rejected([&]{store.produce(bits(payload),bits(timestamp),evaluate);});rejected([&]{store.response_complete(p.ticket+1);});store.response_complete(p.ticket);
  }
  rejected([&]{store.produce(bits(payload),bits(timestamp),[](const auto&,Bits)->Bits{throw std::runtime_error("mock runtime failure");});});
  rejected([&]{store.produce(bits(payload),bits(timestamp),evaluate);});
  rejected([&]{signal_mpc::VariableSendStore<Bits> reopened(shape,bits(initial),slot);});
  auto short_slot=slot+"-short";signal_mpc::VariableSendStore<Bits> short_store(shape,bits(initial),short_slot);
  rejected([&]{short_store.produce(bits(payload),bits(timestamp),[](const auto&,Bits){return Bits(1);});});
  rejected([&]{short_store.produce(bits(payload),bits(timestamp),evaluate);});
  std::cout<<shape.descriptor()<<'\n';++profiles;
 }
 assert(profiles==32);std::cout<<"32 public mock store profiles passed\n";
}
