// Public synthetic test only. No production fault-injection surface.
#define TLS_CAUGHT_FAILURE_TEST_HOOKS
#include "NativeWorker.h"
#include "Protocols/Opener.h"
#include "SessionWork/NativeLifecycle.h"
#include "Tools/SocketCancellation.h"
#include <iostream>
using namespace tls_mpc_worker;
struct State {
 std::unique_ptr<Names> names; std::unique_ptr<PinnedPrograms> pinned;
 std::unique_ptr<Machine<tls_mpc_worker::Share>> machine; std::unique_ptr<Worker> worker;
 std::unique_ptr<NativeLifecycle> lifecycle; tls_mpc_worker::Bits input;
};
int main(int argc,char**argv){
 SecureGmp::install_before_threads();if(argc!=6)return 2;
 auto* state=new State;unsigned party=std::stoul(argv[1]);std::string mode=argv[5];
 bool success=false;size_t wiped=ErasingThreadStack::wiped_stacks.load();
 try {
  public_require(ErasedHostCall::run([&]{
   ShamirOptions::singleton={5,2};OnlineOptions opts;opts.playerno=party;opts.live_prep=true;opts.security_parameter=128;opts.lg2=128;opts.lgp=255;opts.prime=1;opts.prime<<=255;opts.prime-=19;
   state->names=std::make_unique<Names>(party,std::stoul(argv[3]),std::string(argv[2]));
   state->pinned=std::make_unique<PinnedPrograms>(argv[4]);state->machine=std::make_unique<Machine<tls_mpc_worker::Share>>(*state->names,true,opts);
   state->worker=std::make_unique<Worker>(*state->machine,*state->pinned);state->lifecycle=std::make_unique<NativeLifecycle>(*state->machine);
   state->input=state->worker->allocate(128);for(size_t i=0;i<128;++i)state->input[i][0]=tls_mpc_worker::Bit::constant(i%2,party,state->machine->get_bit_mac_key());
  }),"fixture bootstrap failed");
  auto run=[&]{
   auto output=state->worker->allocate(320);std::vector<FunctionArgument> args={{1,state->input.function_argument()},{1,output.function_argument()}};FunctionArgument result;
   state->pinned->verify_function("tls_diagnostic_mix",args);state->machine->run_function("tls_diagnostic_mix",result,args);
   auto expected=state->worker->allocate(320);unsigned number=170*170+17;
   for(size_t i=0;i<320;++i){unsigned bit;if(i<64)bit=i%2;else{size_t k=i-64,shift=8*(k/8)+7-k%8;bit=shift<32?((number>>shift)&1):0;}expected[i][0]=tls_mpc_worker::Bit::constant(bit,party,state->machine->get_bit_mac_key());}
   auto combined=output;combined.insert(combined.end(),expected.begin(),expected.end());auto status=state->worker->allocate(8);std::vector<FunctionArgument> checks={{1,combined.function_argument()},{1,status.function_argument()}};
   state->pinned->verify_function("tls_diagnostic_compare",checks);state->machine->run_function("tls_diagnostic_compare",result,checks);
   Opener<tls_mpc_worker::Bit> opener(state->machine->get_player(),state->machine->get_bit_mac_key());opener.init_open();for(auto& bit:status)opener.prepare_open(bit[0]);opener.exchange();for(unsigned i=0;i<8;++i)public_require((opener.finalize_open().get()&1)==1,"comparison failed");opener.Check();
  };
  // Warm initialization is completed before the adversarial boundary.
  public_require(ErasedHostCall::run(run),"fixture warmup failed");
  if(mode=="positive") {
   for(unsigned i=0;i<2;++i)public_require(ErasedHostCall::run([&]{state->lifecycle->renew_epoch();run();}),"positive epoch failed");
   public_require(ErasedHostCall::run([&]{state->input.clear();public_require(state->lifecycle->abort_epoch(),"positive abort failed");}),"positive cleanup failed");
   success=true;
  } else {
   bool caught=false;
   public_require(ErasedHostCall::run([&]{
    if(mode=="tamper"&&party==0)state->input[0][0].get_regs()[0]+=gf2n_long(1);
    if(mode=="protocol"&&party==0)tls_caught_failure::fixture_fault_stage=1;
    if(mode=="teardown"&&party==0)tls_caught_failure::fixture_fault_stage=2;
    try {if(mode=="teardown")state->machine->retire_worker_epoch();else run();}
    catch(...) {caught=true;}
    public_require(caught&&state->machine->has_caught_failure(),"fault was not caught");
    state->machine->cleanup_caught_failure();
    public_require(state->machine->failed_cleanup_complete(),"caught cleanup incomplete");
    state->input.clear();
    public_require(!state->lifecycle->abort_epoch(),"failed epoch returned retirement success");
    bool rejected=false;try{FunctionArgument ignored;std::vector<FunctionArgument> empty;state->machine->run_function("tls_diagnostic_mix",ignored,empty);}catch(...){rejected=true;}public_require(rejected,"failed runtime accepted replay");
    public_require(tls_caught_failure::runtime_sockets.active()==0,"owned transport survived cleanup");
    public_require(ErasingThreadStack::wiped_stacks.load()>=wiped+17,"owned stacks were not wiped");
   }),"failure fixture erased host failed");
   success=true;
  }
 }catch(...){std::cerr<<"fixture failure category=assertion\n";}
 bool cleaned=ErasedHostCall::run([&]{state->input.clear();delete state;state=nullptr;});
 if(success&&cleaned){std::cout<<"FAILURE_FIXTURE {\"passed\":true,\"retirement_on_failure\":false,\"mode\":\""<<mode<<"\"}\n";return 0;}return 1;
}
