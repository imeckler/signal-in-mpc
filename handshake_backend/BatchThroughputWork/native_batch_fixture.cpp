// Fresh private instance inputs; only aggregate equality flags are opened.
#include "NativeWorker.h"
#include "NativeCollective.h"
#include "SessionWork/NativeLifecycle.h"
#include "Protocols/Opener.h"
#include "Tools/PublicProtocolMetrics.h"
#include <iostream>
using namespace tls_mpc_worker;
struct State {std::unique_ptr<Names> names;std::unique_ptr<PinnedPrograms> pinned;std::unique_ptr<Machine<tls_mpc_worker::Share>> machine;std::unique_ptr<Collective> collective;std::unique_ptr<NativeLifecycle> lifecycle;std::unique_ptr<Worker> worker;};
int main(int argc,char**argv){
 SecureGmp::install_before_threads();if(argc!=5)return 2;State* s=new State;unsigned party=std::stoul(argv[1]),port=std::stoul(argv[3]);
 try{
 public_require(ErasedHostCall::run([&]{
 s->pinned=std::make_unique<PinnedPrograms>(argv[4]);ShamirOptions::singleton={5,2};OnlineOptions o;o.playerno=party;o.live_prep=true;o.security_parameter=128;o.lg2=128;o.lgp=255;o.prime=1;o.prime<<=255;o.prime-=19;
 s->names=std::make_unique<Names>(party,port,std::string(argv[2]));public_require(s->names->num_players()==5,"five parties required");s->machine=std::make_unique<Machine<tls_mpc_worker::Share>>(*s->names,true,o);s->collective=std::make_unique<Collective>(s->machine->get_player(),s->pinned->digest(),PublicBytes(32,119));s->lifecycle=std::make_unique<NativeLifecycle>(*s->machine);s->worker=std::make_unique<Worker>(*s->machine,*s->pinned);
 }),"batch bootstrap failed");
 for(unsigned count:{2u,4u,8u})for(unsigned iteration=0;iteration<2;++iteration){public_require(ErasedHostCall::run([&]{
 auto call=[&](const std::string&name,tls_mpc_worker::Bits&input,size_t size){auto output=s->worker->allocate(size);std::vector<FunctionArgument>a={{1,input.function_argument()},{1,output.function_argument()}};s->pinned->verify_function(name,a);FunctionArgument ignored;s->machine->run_function(name,ignored,a);return output;};
 auto zero=s->worker->allocate(8);auto input=call("tls_batch_random_"+std::to_string(count),zero,8*count);tls_mpc_worker::Bits sequential,batched;
 for(unsigned turn=0;turn<2;++turn){bool batch=(turn+iteration)%2;auto mode=batch?"batch":"sequential";auto before=tls_public_diagnostics::snapshot();auto start=std::chrono::steady_clock::now();auto output=call("tls_batch_tiny_"+std::string(mode)+"_"+std::to_string(count),input,37*count);auto ns=std::chrono::duration_cast<std::chrono::nanoseconds>(std::chrono::steady_clock::now()-start).count();auto after=tls_public_diagnostics::snapshot();auto usage=s->machine->public_function_usage();
 std::cout<<"BATCH_METRIC {\"party\":"<<party<<",\"count\":"<<count<<",\"iteration\":"<<iteration<<",\"order\":"<<turn<<",\"mode\":\""<<mode<<"\",\"elapsed_ns\":"<<ns<<",\"prepare_ns\":"<<after.prepare_ns-before.prepare_ns<<",\"load_ns\":"<<after.load_ns-before.load_ns<<",\"bytes\":[";for(unsigned i=0;i<9;++i){if(i)std::cout<<',';std::cout<<after.bytes[i]-before.bytes[i];}std::cout<<"],\"consumed\":[";bool first=true;for(size_t f=0;f<N_DATA_FIELD_TYPE;++f)for(size_t k=0;k<N_DTYPE;++k)if(usage.files[f][k]){if(!first)std::cout<<',';first=false;std::cout<<'['<<f<<','<<k<<','<<usage.files[f][k]<<']';}std::cout<<"]}\n";if(batch)batched=std::move(output);else sequential=std::move(output);
 }
 auto check=sequential;check.insert(check.end(),batched.begin(),batched.end());auto compare=[&](bool expected){auto status=call("tls_batch_compare_"+std::to_string(count),check,8);Opener<tls_mpc_worker::Bit> opener(s->machine->get_player(),s->machine->get_bit_mac_key());opener.init_open();for(auto&bit:status)opener.prepare_open(bit[0]);opener.exchange();for(unsigned i=0;i<8;++i)public_require((opener.finalize_open().get()&1)==expected,"aggregate batch equality failed");opener.Check();};compare(true);
 // Functional rejection only; this does NOT simulate a malformed MAC.
 check[37*count][0]+=tls_mpc_worker::Bit::constant(1,party,s->machine->get_bit_mac_key());compare(false);
 check.clear();sequential.clear();batched.clear();input.clear();zero.clear();s->lifecycle->renew_epoch();
 }),"batch case/barrier failed");}
 public_require(ErasedHostCall::run([&]{public_require(s->lifecycle->abort_epoch(),"batch cleanup failed");delete s;s=nullptr;}),"batch destructor barrier failed");std::cout<<"private native batch fixture passed\n";return 0;
 }catch(...){if(s){try{ErasedHostCall::run([&]{s->lifecycle->abort_epoch();delete s;s=nullptr;});}catch(...){}}std::cerr<<"private native batch fixture failed\n";return 1;}
}
