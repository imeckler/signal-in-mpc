// PUBLIC disposable new-DH receiving fixture. No key/state shares are opened;
// only secure equality against independently computed PUBLIC oracle constants.
#include "NativeNewDhReceive.h"
#include "NativeCollective.h"
#include "Protocols/Opener.h"
#include <fstream>
#include <iostream>
using namespace tls_mpc_worker;
static PublicBytes decode(const std::string& s){PublicBytes b;for(size_t i=0;i<s.size();i+=2)b.push_back(std::stoul(s.substr(i,2),nullptr,16));return b;}
int main(int argc,char**argv){if(argc!=6)return 2;try{
 unsigned party=std::stoul(argv[1]),port=std::stoul(argv[3]);public_require(party<5&&port>1024&&port<65530,"fixture party/port");
 PinnedPrograms pinned(argv[4]);ShamirOptions::singleton={5,2};OnlineOptions options;
 options.playerno=party;options.live_prep=true;options.security_parameter=128;options.lg2=128;options.lgp=255;
 options.prime=1;options.prime<<=255;options.prime-=19;Names names(party,port,std::string(argv[2]));
 public_require(names.num_players()==5,"five parties required");Machine<tls_mpc_worker::Share> machine(names,true,options);
 Collective collective(machine.get_player(),pinned.digest(),PublicBytes(32,85));Worker worker(machine,pinned);
 signal_mpc::NativeNewDhReceive receiver(machine,worker,pinned);
 auto public_bits=[&](const PublicBytes& raw){auto out=worker.allocate(raw.size()*8);for(size_t i=0;i<out.size();++i){
  out[i][0]=tls_mpc_worker::Bit::constant((raw[i/8]>>(7-i%8))&1,party,machine.get_bit_mac_key());}return out;};
 std::ifstream file(argv[5]);std::string input_hex,expected_hex;size_t step=0;
 while(file>>input_hex>>expected_hex){auto raw=decode(input_hex),expected=decode(expected_hex);
  public_require(raw.size()==848&&expected.size()==608,"fixture dimensions");auto input=public_bits(raw);
  auto output=receiver.evaluate(std::move(input));
  if(step==0){
   // Fresh root/private/public/sending-chain material has no public expected
   // value. Compare ONLY status, actual receiving chains/PQ and plaintext.
   // Constants replace the omitted136 bytes on BOTH sides inside MPC.
   std::fill(expected.begin()+1,expected.begin()+137,0);
   auto zeros=public_bits(PublicBytes(136,0));std::copy(zeros.begin(),zeros.end(),output.begin()+8);
  }
  auto comparison=std::move(output);auto constants=public_bits(expected);
  comparison.insert(comparison.end(),constants.begin(),constants.end());
  auto accepted=worker.allocate(8);std::vector<FunctionArgument>args={{1,comparison.function_argument()},{1,accepted.function_argument()}};
  const std::string check="signal_new_dh_fixture_equal_4864";pinned.verify_function(check,args);FunctionArgument ignored;machine.run_function(check,ignored,args);
  Opener<tls_mpc_worker::Bit> opener(machine.get_player(),machine.get_bit_mac_key());opener.init_open();opener.prepare_open(accepted[0][0]);opener.exchange();
  auto passed=opener.finalize_open().get();opener.Check();public_require(passed==1,"new-DH candidate/public actual-oracle mismatch");
  std::cout<<"STEP "<<step++<<" equality passed\n";
 }
 public_require(step==2,"expected actual receive and MAC rejection");return 0;
 }catch(const std::exception&){std::cerr<<"private new-DH fixture failed\n";return 1;}}
