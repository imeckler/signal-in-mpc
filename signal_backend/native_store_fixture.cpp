// PUBLIC SYNTHETIC FIXTURE ONLY. Opens the wire for comparison, never live data.
// The second send consumes actual shared state produced by the first send.
#include "NativeWorker.h"
#include "NativeCollective.h"
#include "Protocols/Opener.h"
#include "EstablishedSendStore.h"
#include "PrivateGrpcRequest.h"
#include <fstream>
#include <iostream>
using namespace tls_mpc_worker;
static PublicBytes decode(const std::string& text){
 public_require(text.size()%2==0,"invalid fixture hex");PublicBytes b;
 for(size_t i=0;i<text.size();i+=2)b.push_back(std::stoul(text.substr(i,2),nullptr,16));return b;
}
int main(int argc,char** argv){
 if(argc!=6)return 2;
 try{
  unsigned party=std::stoul(argv[1]),port=std::stoul(argv[3]);
  public_require(party<5&&port>1024&&port<65530,"invalid fixture party/port");
  PinnedPrograms pinned(argv[4]);ShamirOptions::singleton={5,2};
  OnlineOptions options;options.playerno=party;options.live_prep=true;
  options.security_parameter=128;options.lg2=128;options.lgp=255;
  options.prime=1;options.prime<<=255;options.prime-=19;
  Names names(party,port,std::string(argv[2]));public_require(names.num_players()==5,"five parties required");
  Machine<tls_mpc_worker::Share> machine(names,true,options);
  Collective collective(machine.get_player(),pinned.digest(),PublicBytes(32,19));
  Worker worker(machine,pinned);
  auto share=[&](const PublicBytes& bytes){auto b=worker.allocate(bytes.size()*8);
   for(size_t i=0;i<b.size();++i)b[i][0]=tls_mpc_worker::Bit::constant((bytes[i/8]>>(7-i%8))&1,party,machine.get_bit_mac_key());return b;};
  auto check=[&](const tls_mpc_worker::Bits& result,const PublicBytes& wanted){
   public_require(result.size()==wanted.size()*8,"fixture output dimension mismatch");
   Opener<tls_mpc_worker::Bit> opener(machine.get_player(),machine.get_bit_mac_key());
   opener.init_open();for(const auto& bit:result)opener.prepare_open(bit[0]);opener.exchange();bool correct=true;
   for(size_t i=0;i<result.size();++i)correct&=(opener.finalize_open().get()&1)==((wanted[i/8]>>(7-i%8))&1);
   opener.Check();public_require(correct,"fixture Signal wire mismatch");};
  signal_mpc::SendShape shape(0,1,1,1,1,0,false,false);
  std::ifstream input(argv[5]);std::string raw_hex,out_hex;
  public_require(bool(input>>raw_hex>>out_hex),"missing initial fixture");
  auto first=decode(raw_hex);
  PublicBytes initial(first.begin(),first.begin()+117);initial.insert(initial.end(),first.begin()+118,first.begin()+182);
  signal_mpc::EstablishedSendStore<tls_mpc_worker::Bits> store(share(initial),{});
  size_t calls=0;
  do{
   auto raw=decode(raw_hex),expected=decode(out_hex);
   public_require(raw.size()==182&&expected.size()==shape.output_bytes(),"wrong fixture shape");
   auto produced=store.produce(shape,share(PublicBytes{raw[117]}),
     [&](const signal_mpc::SendShape& s,tls_mpc_worker::Bits in){return worker.signal(s,std::move(in));});
   check(produced.wire,PublicBytes(expected.begin()+73,expected.end()));
   // Exercise the exact OwnedBits framing instantiation without opening it.
   auto text=[&](const std::string& s){return share(PublicBytes(s.begin(),s.end()));};
   auto framed=signal_mpc::frame_grpc_request(1,text("fixture.invalid"),text("/fixture.Service/Send"),
       text("Basic fixture"),std::move(produced.wire),share);
   public_require(framed.size()<=16384*8,"framed private fixture exceeds TLS payload bound");
   store.transport_complete(produced.ticket);++calls;
  }while(input>>raw_hex>>out_hex);
  public_require(calls==2,"expected two consecutive native sends");
  std::cout<<"native Signal store fixture passed: two consecutive sends; only public fixture wire opened\n";
  return 0;
 }catch(const std::exception& error){std::cerr<<"native Signal fixture failed: "<<error.what()<<'\n';return 1;}
}
