// PUBLIC SYNTHETIC COMPONENT FIXTURE. No live service/TLS response is used.
// Only synthetic final payload/status is opened; chain states, request IDs,
// generated ephemeral scalars and computed DH remain unopened in the store.
#include "NativeVariableService.h"
#include "VariableSendStore.h"
#include "NativeCollective.h"
#include "Protocols/Opener.h"
#include <fstream>
#include <iostream>
#include <iomanip>
using namespace tls_mpc_worker;
static PublicBytes decode(const std::string& s){PublicBytes b;for(size_t i=0;i<s.size();i+=2)b.push_back(std::stoul(s.substr(i,2),nullptr,16));return b;}
int main(int argc,char**argv){if(argc!=6)return 2;try{
 unsigned party=std::stoul(argv[1]),port=std::stoul(argv[3]);public_require(party<5&&port>1024&&port<65530,"invalid fixture party/port");
 PinnedPrograms pinned(argv[4]);ShamirOptions::singleton={5,2};OnlineOptions options;
 options.playerno=party;options.live_prep=true;options.security_parameter=128;options.lg2=128;options.lgp=255;
 options.prime=1;options.prime<<=255;options.prime-=19;Names names(party,port,std::string(argv[2]));
 public_require(names.num_players()==5,"five parties required");Machine<tls_mpc_worker::Share> machine(names,true,options);
 Collective collective(machine.get_player(),pinned.digest(),PublicBytes(32,84));Worker worker(machine,pinned);
 signal_mpc::NativeVariableService service(machine,worker,pinned);signal_mpc::VariableShape shape(260,0,false,false);
 auto public_bits=[&](const PublicBytes& raw){auto out=worker.allocate(raw.size()*8);for(size_t i=0;i<out.size();++i){
  out[i][0]=tls_mpc_worker::Bit::constant((raw[i/8]>>(7-i%8))&1,party,machine.get_bit_mac_key());}return out;};
 auto open_fixture=[&](const tls_mpc_worker::Bits& output){Opener<tls_mpc_worker::Bit> opener(machine.get_player(),machine.get_bit_mac_key());
  opener.init_open();for(const auto& bit:output)opener.prepare_open(bit[0]);opener.exchange();PublicBytes bytes(output.size()/8);
  for(size_t i=0;i<output.size();++i)bytes[i/8]|=(opener.finalize_open().get()&1)<<(7-i%8);opener.Check();return bytes;};
 std::ifstream file(argv[5]);std::string text;size_t count=0;
 while(file>>text){auto input=decode(text);public_require(input.size()==shape.input_bytes(),"public fixture dimensions");
  auto slot=std::string(argv[5])+"-party"+std::to_string(party)+"-case"+std::to_string(count)+".fence";
  signal_mpc::VariableSendStore<tls_mpc_worker::Bits> store(shape,public_bits(input),slot);
  auto payload=PublicBytes{input[shape.spqr_offset()+117]};
  PublicBytes timestamp(input.begin()+shape.metadata_offset()+32,input.begin()+shape.metadata_offset()+40);
  const auto steps=count==0?2:1;
  for(int step=0;step<steps;++step){std::cerr<<"begin private conversation case "<<count<<" step "<<step<<'\n';
   auto produced=store.produce(public_bits(payload),public_bits(timestamp),[&](const auto& s,tls_mpc_worker::Bits bits){return service.evaluate(s,std::move(bits));});
   auto bytes=open_fixture(produced.payload);
   if(count==0){public_require(bytes[0]==255,"valid private conversation rejected");size_t n=size_t(bytes[1])*256+bytes[2];
    public_require(n<=shape.frame_capacity()&&std::all_of(bytes.begin()+3+n,bytes.end(),[](auto b){return b==0;}),"private length/tail invalid");
    std::cout<<"FRAME "<<step<<' ';for(size_t i=3;i<3+n;++i)std::cout<<std::hex<<std::setw(2)<<std::setfill('0')<<unsigned(bytes[i]);std::cout<<std::dec<<'\n';
    // Synthetic fixture acknowledgement ONLY. Real store callers wait for an
    // authenticated, correlated response policy before unlocking another send.
    store.response_complete(produced.ticket);
   }else{public_require(std::all_of(bytes.begin(),bytes.end(),[](auto b){return b==0;}),"binding rejection not canonical");std::cout<<"REJECT "<<count<<'\n';store.close();}
  }++count;
 }
 public_require(count==2,"expected initial conversation and mismatched identity fixture");
 std::cout<<"private variable conversation fixture passed\n";return 0;
 }catch(const std::exception&e){std::cerr<<"private variable conversation failed: "<<e.what()<<'\n';return 1;}}
