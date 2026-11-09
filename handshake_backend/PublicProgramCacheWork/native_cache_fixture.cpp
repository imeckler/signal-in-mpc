#include "NativeWorker.h"
#include "NativeCollective.h"
#include "SessionWork/NativeLifecycle.h"
#include "PinnedCacheAdmission.h"
#include "Protocols/Opener.h"
#include <iostream>
using namespace tls_mpc_worker;
struct State {std::unique_ptr<Names> names;std::unique_ptr<PinnedCacheAdmission> admission;std::unique_ptr<Machine<tls_mpc_worker::Share>> machine;std::unique_ptr<NativeLifecycle> lifecycle;std::unique_ptr<Worker> worker;};
int main(int argc,char**argv){
 SecureGmp::install_before_threads();if(argc!=5)return 2;auto s=new State;unsigned party=std::stoul(argv[1]),port=std::stoul(argv[3]);
 try{
 public_require(ErasedHostCall::run([&]{s->admission=std::make_unique<PinnedCacheAdmission>(argv[4]);ShamirOptions::singleton={5,2};OnlineOptions o;o.playerno=party;o.live_prep=true;o.security_parameter=128;o.lg2=128;o.lgp=255;o.prime=1;o.prime<<=255;o.prime-=19;s->names=std::make_unique<Names>(party,port,std::string(argv[2]));s->machine=std::make_unique<Machine<tls_mpc_worker::Share>>(*s->names,true,o);s->lifecycle=std::make_unique<NativeLifecycle>(*s->machine);s->worker=std::make_unique<Worker>(*s->machine,s->admission->programs());}),"cache bootstrap failed");
 public_require(ErasedHostCall::run([&]{
 auto call=[&](const std::string&name,tls_mpc_worker::Bits&input,size_t size){auto output=s->worker->allocate(size);std::vector<FunctionArgument>a={{1,input.function_argument()},{1,output.function_argument()}};FunctionArgument ignored;s->admission->run(*s->machine,name,ignored,a);return output;};
 auto zero=s->worker->allocate(8);auto input=call("tls_batch_random_8",zero,64);
 auto first=call("signal_private_variable_conversation_cache_fixture",input,296);
 auto second=call("signal_private_variable_conversation_cache_fixture",input,296); // adjacent hit
 auto other=call("tls_batch_tiny_batch_8",input,296);
 auto third=call("signal_private_variable_conversation_cache_fixture",input,296); // interleaved hit
 auto compare=[&](tls_mpc_worker::Bits&x){auto pair=first;pair.insert(pair.end(),x.begin(),x.end());auto status=call("tls_batch_compare_8",pair,8);Opener<tls_mpc_worker::Bit> opener(s->machine->get_player(),s->machine->get_bit_mac_key());opener.init_open();for(auto&b:status)opener.prepare_open(b[0]);opener.exchange();for(unsigned i=0;i<8;++i)public_require((opener.finalize_open().get()&1)==1,"cache equality failed");opener.Check();};
 compare(second);compare(other);compare(third);
 auto before=s->machine->public_program_cache_metrics();auto epoch=s->machine->worker_epoch;s->lifecycle->renew_epoch();public_require(s->machine->worker_epoch==epoch+1,"cache epoch did not renew");
 auto fourth=call("signal_private_variable_conversation_cache_fixture",input,296);compare(fourth);
 auto after=s->machine->public_program_cache_metrics();public_require(after[1]==before[1],"public code reloaded after interleaving/epoch");public_require(after[0]>before[0]&&after[0]>=5,"missing public cache hits");
 ++s->machine->opts.batch_size; // public configuration invalidates code metadata
 auto fifth=call("signal_private_variable_conversation_cache_fixture",input,296);compare(fifth);
 auto changed=s->machine->public_program_cache_metrics();public_require(changed[1]==after[1]+2,"configuration did not invalidate cached metadata");after=changed;
 // Fixed public admission failure, not a MAC-tamper simulation. It must poison
 // cached execution and discard retained public images without stale outputs.
 auto denied_output=s->worker->allocate(296);std::vector<FunctionArgument> denied_args={{1,input.function_argument()},{1,denied_output.function_argument()}};FunctionArgument ignored;
 bool denied=false;try{s->machine->run_function_pinned("signal_private_variable_conversation_cache_fixture",ignored,denied_args,std::string(64,'0'),{{"Programs/Functions/no-such-admission",std::string(64,'0')}});}catch(const std::exception&){denied=true;}public_require(denied,"invalid closure identity accepted");
 denied=false;try{call("signal_private_variable_conversation_cache_fixture",input,296);}catch(const std::exception&){denied=true;}public_require(denied,"poisoned public cache executed");
 public_require(s->machine->public_program_cache_metrics()[4]==0,"failed public cache retained images");
 std::cout<<"CACHE_FAILURE_CLOSED 1\n";
 std::cout<<"CACHE_METRIC {\"hits\":"<<after[0]<<",\"loads\":"<<after[1]<<",\"evictions\":"<<after[2]<<",\"retained_accounted_bytes\":"<<after[3]<<",\"retained_entries\":"<<after[4]<<",\"epoch\":"<<s->machine->worker_epoch<<"}\n";
 fifth.clear();denied_output.clear();first.clear();second.clear();third.clear();fourth.clear();other.clear();input.clear();zero.clear();
 }),"cache fixture/barrier failed");
 public_require(ErasedHostCall::run([&]{public_require(s->lifecycle->abort_epoch(),"cache abort failed");delete s;s=nullptr;}),"cache destructor barrier failed");std::cout<<"private native cache fixture passed\n";return 0;
 }catch(...){if(s){try{ErasedHostCall::run([&]{s->lifecycle->abort_epoch();delete s;s=nullptr;});}catch(...){}}std::cerr<<"private native cache fixture failed\n";return 1;}
}
