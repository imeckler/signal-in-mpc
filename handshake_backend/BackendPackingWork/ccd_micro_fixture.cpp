// Synthetic public fixture inputs; only a comparison byte is opened.
#include "NativeWorker.h"
#include "Protocols/Opener.h"
#include "NativeCollective.h"
#include "SessionWork/NativeLifecycle.h"
#include "Tools/PublicProtocolMetrics.h"
#include <iostream>
using namespace tls_mpc_worker;
struct State {
 std::unique_ptr<Names> names;std::unique_ptr<PinnedPrograms> pinned;
 std::unique_ptr<Machine<tls_mpc_worker::Share>> machine;std::unique_ptr<Collective> collective;
 std::unique_ptr<NativeLifecycle> lifecycle;std::unique_ptr<Worker> worker;tls_mpc_worker::Bits retained;
};
int main(int argc,char** argv){
 SecureGmp::install_before_threads();if(argc!=5)return 2;State* state=new State;
 unsigned party=std::stoul(argv[1]);unsigned port=std::stoul(argv[3]);
 try{
 public_require(ErasedHostCall::run([&]{
  state->pinned=std::make_unique<PinnedPrograms>(argv[4]);ShamirOptions::singleton={5,2};OnlineOptions opts;
  opts.playerno=party;opts.live_prep=true;opts.security_parameter=128;opts.lg2=128;opts.lgp=255;opts.prime=1;opts.prime<<=255;opts.prime-=19;
  state->names=std::make_unique<Names>(party,port,std::string(argv[2]));public_require(state->names->num_players()==5,"five parties required");
  state->machine=std::make_unique<Machine<tls_mpc_worker::Share>>(*state->names,true,opts);
  state->collective=std::make_unique<Collective>(state->machine->get_player(),state->pinned->digest(),PublicBytes(32,77));
  state->lifecycle=std::make_unique<NativeLifecycle>(*state->machine);
  state->worker=std::make_unique<Worker>(*state->machine,*state->pinned);
 }),"microfixture bootstrap failed");
 std::vector<unsigned char> expected_input(128);for(size_t i=0;i<128;++i)expected_input[i]=(i%3)!=0;
 for(size_t step=0;step<3;++step){
  public_require(ErasedHostCall::run([&]{
   auto share=[&](const std::vector<unsigned char>& raw){auto bits=state->worker->allocate(raw.size());for(size_t i=0;i<raw.size();++i)bits[i][0]=tls_mpc_worker::Bit::constant(raw[i],party,state->machine->get_bit_mac_key());return bits;};
   if(step==0)state->retained=share(expected_input);
   auto output=state->worker->allocate(320);std::vector<FunctionArgument> args={{1,state->retained.function_argument()},{1,output.function_argument()}};
   state->pinned->verify_function("tls_diagnostic_mix",args);
   auto original_before=state->machine->total_stats().comm_stats.sent+state->machine->get_player().total_comm().sent;
   auto before=tls_public_diagnostics::snapshot();FunctionArgument ignored;
   state->machine->run_function("tls_diagnostic_mix",ignored,args);
   auto usage=state->machine->public_function_usage();auto after=tls_public_diagnostics::snapshot();
   auto original_after=state->machine->total_stats().comm_stats.sent+state->machine->get_player().total_comm().sent;
   std::vector<unsigned char> expected(320);unsigned value=0;
   for(size_t i=0;i<64;++i){expected[i]=expected_input[i]&expected_input[64+i];if(i<8)value|=unsigned(expected[i])<<i;}
   value=value*value+17;
   // field_to_wire_bits is little-endian bytes, MSB-first within each byte.
   for(size_t i=0;i<256;++i){auto shift=8*(i/8)+7-i%8;expected[64+i]=shift<32?((value>>shift)&1):0;}
   auto check_input=output;auto expected_shares=share(expected);check_input.insert(check_input.end(),expected_shares.begin(),expected_shares.end());
   auto status=state->worker->allocate(8);std::vector<FunctionArgument> checks={{1,check_input.function_argument()},{1,status.function_argument()}};
   state->pinned->verify_function("tls_diagnostic_compare",checks);state->machine->run_function("tls_diagnostic_compare",ignored,checks);
   { Opener<tls_mpc_worker::Bit> opener(state->machine->get_player(),state->machine->get_bit_mac_key());opener.init_open();for(auto& bit:status)opener.prepare_open(bit[0]);opener.exchange();
   for(size_t i=0;i<8;++i)public_require((opener.finalize_open().get()&1)==1,"private synthetic comparison failed");opener.Check(); }
   state->retained=tls_mpc_worker::Bits(output.begin(),output.begin()+128);expected_input.assign(expected.begin(),expected.begin()+128);
   std::cout<<"DIAGNOSTIC {\"party\":"<<party<<",\"step\":"<<step<<",\"prepare_ns\":"<<after.prepare_ns-before.prepare_ns<<",\"load_ns\":"<<after.load_ns-before.load_ns<<",\"original_payload_byte_delta\":"<<original_after-original_before<<",\"bytes\":[";
   for(size_t i=0;i<9;++i){if(i)std::cout<<',';std::cout<<after.bytes[i]-before.bytes[i];}std::cout<<"],\"scope_calls\":[";
   for(size_t i=0;i<9;++i){if(i)std::cout<<',';std::cout<<after.calls[i]-before.calls[i];}std::cout<<"],\"consumed\":[";bool first=true;
   for(size_t f=0;f<N_DATA_FIELD_TYPE;++f)for(size_t k=0;k<N_DTYPE;++k)if(usage.files[f][k]){if(!first)std::cout<<',';first=false;std::cout<<'['<<f<<','<<k<<','<<usage.files[f][k]<<']';}std::cout<<"]}\n";
   // No per-thread usage sum is asserted for parallel schedules; this fixture
   // closure declares one worker and both exported functions stay on it.
   args.clear();checks.clear();output.clear();check_input.clear();expected_shares.clear();status.clear();
   state->lifecycle->renew_epoch();
  }),"microfixture step/barrier failed");
 }
 public_require(ErasedHostCall::run([&]{state->retained.clear();public_require(state->lifecycle->abort_epoch(),"microfixture terminal cleanup failed");delete state;state=nullptr;}),"microfixture destructor barrier failed");
 std::cout<<"diagnostic CCD microfixture passed\n";return 0;
 }catch(...){if(state){try{ErasedHostCall::run([&]{state->retained.clear();state->lifecycle->abort_epoch();delete state;state=nullptr;});}catch(...){}}std::cerr<<"diagnostic CCD microfixture failed\n";return 1;}
}
