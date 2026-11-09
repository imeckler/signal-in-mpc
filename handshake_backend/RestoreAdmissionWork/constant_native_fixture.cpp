#include "NativeWorker.h"
#include "SessionWork/NativeLifecycle.h"
#include "../signal_backend/RecoveryWork/NativeOwnShareArchive.h"
#include "Protocols/Opener.h"
#include <iostream>
using namespace tls_mpc_worker;using signal_mpc::recovery::NativeOwnShareArchive;
struct State{std::unique_ptr<Names> names;std::unique_ptr<PinnedPrograms> pinned;std::unique_ptr<Machine<tls_mpc_worker::Share>> machine;std::unique_ptr<Worker> worker;std::unique_ptr<NativeLifecycle> lifecycle;};
int main(int argc,char**argv){SecureGmp::install_before_threads();if(argc!=5)return 2;auto s=new State;auto party=unsigned(std::stoul(argv[1]));try{
 public_require(ErasedHostCall::run([&]{s->pinned=std::make_unique<PinnedPrograms>(argv[4]);ShamirOptions::singleton={5,2};OnlineOptions o;o.playerno=party;o.live_prep=true;o.security_parameter=128;o.lg2=128;o.lgp=255;o.prime=1;o.prime<<=255;o.prime-=19;s->names=std::make_unique<Names>(party,std::stoul(argv[3]),std::string(argv[2]));s->machine=std::make_unique<Machine<tls_mpc_worker::Share>>(*s->names,true,o);s->worker=std::make_unique<Worker>(*s->machine,*s->pinned);s->lifecycle=std::make_unique<NativeLifecycle>(*s->machine);}),"constant bootstrap");
 for(unsigned turn=0;turn<2;++turn)public_require(ErasedHostCall::run([&]{
 auto input=s->worker->allocate(16);NativeOwnShareArchive::require_cells(input); // BEFORE VM overwrite.
 for(auto& bit:input)bit[0]=single_cell_constant<tls_mpc_worker::Bit>(1,party,s->machine->get_bit_mac_key());
 NativeOwnShareArchive::require_cells(input);auto result=s->worker->binary("tls-provider-validity",std::move(input),8);NativeOwnShareArchive::require_cells(result);auto copy=result;NativeOwnShareArchive::require_cells(copy);
 Opener<tls_mpc_worker::Bit> opener(s->machine->get_player(),s->machine->get_bit_mac_key());opener.init_open();for(auto& bit:result)opener.prepare_open(bit[0]);opener.exchange();bool accepted=true;for(size_t i=0;i<8;++i)accepted&=opener.finalize_open().get()==1;opener.Check();public_require(accepted,"public fixture validity");
 result.clear();copy.clear();s->lifecycle->renew_epoch();}),"constant interface/epoch");
 public_require(ErasedHostCall::run([&]{public_require(s->lifecycle->abort_epoch(),"constant cleanup");delete s;s=nullptr;}),"constant host cleanup");std::cout<<"public exact-cell native fixture passed\n";return 0;
 }catch(...){if(s){try{ErasedHostCall::run([&]{if(s->lifecycle)s->lifecycle->abort_epoch();delete s;s=nullptr;});}catch(...){}}std::cerr<<"public exact-cell native fixture failed\n";return 1;}}
