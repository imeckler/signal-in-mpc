// PUBLIC disposable archive fixture. Fresh rawGF128 MPC input/checks; only an
// aggregate equality bit is opened on success. No Signal provider admission.
#include "RawFieldReadmit.h"
#include "CiphertextStore.h"
#include "NativeCollective.h"
#include "Protocols/Opener.h"
#include <filesystem>
#include <fstream>
#include <iostream>
using namespace signal_mpc::recovery;
using F=gf2n_long;
static std::string hex(const Digest& d){std::string out;const char* h="0123456789abcdef";for(auto b:d){out+=h[b>>4];out+=h[b&15];}return out;}
static Digest digest(const std::string& s){require(s.size()==64,"fixture digest length");Digest d;for(size_t i=0;i<32;++i)d[i]=std::stoul(s.substr(i*2,2),nullptr,16);return d;}
static ShareDomain domain(unsigned party,unsigned test,const tls_mpc_worker::PinnedPrograms& pin){ShareDomain d{};d.party=party;d.epoch=7;d.slot=test+1;d.bit_count=16;d.context.fill(22);d.membership.fill(23);d.schema.fill(24);d.sharing_epoch.fill(25);std::copy_n(pin.digest().begin(),32,d.manifest.begin());return d;}
static std::array<unsigned char,64> key(unsigned party){std::array<unsigned char,64> k;for(size_t i=0;i<64;++i)k[i]=i+party*7;return k;}
static void prepare(const std::string& manifest,const std::filesystem::path& root){F::init_field(128);tls_mpc_worker::PinnedPrograms pin(manifest);
 for(unsigned test=0;test<4;++test)for(unsigned party=0;party<5;++party){auto dir=root/std::to_string(test)/std::to_string(party);std::filesystem::create_directories(dir);auto d=domain(party,test,pin);SecretBytes local(16*16);
  for(size_t i=0;i<16;++i){F constant(test==3?2:int(i%2));F a=(F(1)<<95)+F(int(11+i)),b=(F(1)<<127)+F(int(81+i)),x(int(party+1));F own=constant+a*x+b*x*x;
   if(test==1&&party==4)own+=F(1)<<101;
   if(test==2&&(party==3||party==4))own+=F(1)<<(party==3?103:117);
   detail::encode_own_evaluation(local.data()+16*i,own);
  }
  OwnShareBox box(key(party));QuarantinedEvaluations values(std::move(local));auto cipher=box.seal(d,values);CiphertextStore store(dir.string());auto hash=store.put(cipher);std::ofstream ref(dir/"reference.txt");ref<<hex(hash)<<' '<<cipher.size()<<'\n';require(bool(ref),"fixture reference write failed");
 }
}
int main(int argc,char**argv){try{
 if(argc==4&&std::string(argv[1])=="prepare"){prepare(argv[2],argv[3]);std::cout<<"encrypted fixture preparation passed\n";return 0;}
 if(argc!=6)return 2;
 unsigned party=std::stoul(argv[1]),port=std::stoul(argv[3]);require(party<5&&port>1024&&port<65530,"fixture party/port");
 std::filesystem::path root(argv[5]);unsigned test=std::stoul(root.filename());require(test<4,"fixture case");
 tls_mpc_worker::PinnedPrograms pin(argv[4]);auto d=domain(party,test,pin);auto dir=root/std::to_string(party);std::ifstream ref(dir/"reference.txt");std::string h;size_t size=0;ref>>h>>size;require(bool(ref),"fixture archive reference");OwnShareBox box(key(party));CiphertextStore store(dir.string());auto archived=box.open_quarantined(d,store.get(digest(h),size));
 ShamirOptions::singleton={5,2};OnlineOptions options;options.playerno=party;options.live_prep=true;options.security_parameter=128;options.lg2=128;options.lgp=255;options.batch_size=64;
 options.prime=1;options.prime<<=255;options.prime-=19;Names names(party,port,std::string(argv[2]));require(names.num_players()==5,"fixture members");
 Machine<tls_mpc_worker::Share> machine(names,true,options);tls_mpc_worker::Collective collective(machine.get_player(),pin.digest(),tls_mpc_worker::PublicBytes(32,74));tls_mpc_worker::Worker worker(machine,pin);
 RawFieldReadmit importer(machine.get_player());
 try{auto restored=importer.values_candidate(std::move(archived),d,worker);require(test==0,"malformed archive accepted");
  auto expected=worker.allocate(16);for(size_t i=0;i<16;++i)expected[i][0]=tls_mpc_worker::Bit::constant(i%2,party,machine.get_bit_mac_key());
  restored.insert(restored.end(),expected.begin(),expected.end());auto result=worker.allocate(8);std::vector<FunctionArgument> args={{1,restored.function_argument()},{1,result.function_argument()}};
  const std::string name="signal_recovery_fixture_equal_16";pin.verify_function(name,args);FunctionArgument ignored;machine.run_function(name,ignored,args);
  Opener<tls_mpc_worker::Bit> opener(machine.get_player(),machine.get_bit_mac_key());opener.init_open();opener.prepare_open(result[0][0]);opener.exchange();auto success=opener.finalize_open().get();opener.Check();require(success==1,"restored private equality failed");std::cout<<"fresh private CCD equality passed\n";
 }catch(const std::runtime_error& e){require(test>0&&std::string(e.what())=="private share consistency/bitness import failed","unexpected raw import failure");std::cout<<"malformed private archive rejected\n";}
 return 0;
 }catch(const std::exception& e){std::cerr<<"raw import fixture failed: "<<e.what()<<'\n';return 1;}}
