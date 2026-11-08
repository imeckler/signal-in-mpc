// PUBLIC SYNTHETIC FIXTURE ONLY. Fresh ephemeral secrets and DH remain inside
// MPC. Only synthetic final request frames/status are opened for a local oracle.
#include "NativeService.h"
#include "NativeCollective.h"
#include "Protocols/Opener.h"
#include <fstream>
#include <iostream>
#include <iomanip>
using namespace tls_mpc_worker;
static PublicBytes decode(const std::string& s){PublicBytes b;for(size_t i=0;i<s.size();i+=2)b.push_back(std::stoul(s.substr(i,2),nullptr,16));return b;}
int main(int argc,char** argv){if(argc!=6)return 2;try{
 unsigned party=std::stoul(argv[1]),port=std::stoul(argv[3]);public_require(party<5&&port>1024&&port<65530,"invalid fixture party/port");
 PinnedPrograms pinned(argv[4]);ShamirOptions::singleton={5,2};
 OnlineOptions options;options.playerno=party;options.live_prep=true;options.security_parameter=128;options.lg2=128;options.lgp=255;
 options.prime=1;options.prime<<=255;options.prime-=19;
 Names names(party,port,std::string(argv[2]));public_require(names.num_players()==5,"five parties required");
 Machine<tls_mpc_worker::Share> machine(names,true,options);
 Collective collective(machine.get_player(),pinned.digest(),PublicBytes(32,71));
 Worker worker(machine,pinned);signal_mpc::NativeService service(machine,worker,pinned);
 signal_mpc::ServiceShape shape(260,72,1,5,13,1);
 std::ifstream file(argv[5]);std::string raw;size_t index=0;
 while(file>>raw){
  auto input=decode(raw);public_require(input.size()==shape.input_bytes(),"fixture input length mismatch");
  auto bits=worker.allocate(input.size()*8);
  for(size_t i=0;i<bits.size();++i)bits[i][0]=tls_mpc_worker::Bit::constant((input[i/8]>>(7-i%8))&1,party,machine.get_bit_mac_key());
  std::cerr<<"begin public fixture case "<<index<<'\n';
  auto output=service.evaluate(shape,std::move(bits));
  Opener<tls_mpc_worker::Bit> opener(machine.get_player(),machine.get_bit_mac_key());
  opener.init_open();for(const auto& bit:output)opener.prepare_open(bit[0]);opener.exchange();
  PublicBytes bytes(output.size()/8,0);
  for(size_t i=0;i<output.size();++i)bytes[i/8]|=(opener.finalize_open().get()&1)<<(7-i%8);
  opener.Check();
  if(index==0){public_require(bytes[0]==255,"valid synthetic private service rejected");std::cout<<"FRAME ";
   for(size_t i=1;i<bytes.size();++i)std::cout<<std::hex<<std::setw(2)<<std::setfill('0')<<unsigned(bytes[i]);std::cout<<std::dec<<'\n';}
  else{public_require(std::all_of(bytes.begin(),bytes.end(),[](auto b){return b==0;}),"invalid agreement/key binding was not masked");std::cout<<"REJECT "<<index<<'\n';}
  ++index;
 }
 public_require(index==3,"expected valid,low-order,key-mismatch cases");
 std::cout<<"private computed-DH service fixture passed\n";return 0;
 }catch(const std::exception& e){std::cerr<<"private service fixture failed: "<<e.what()<<'\n';return 1;}}
