#include "NativeCollective.h"
#include "SessionWork/NativeLifecycle.h"
#include <memory>
#include <iostream>
using namespace tls_mpc_worker;
int main(int argc,char** argv){
    SecureGmp::install_before_threads();if(argc!=4)return 2;
    unsigned party=std::stoul(argv[1]),port=std::stoul(argv[3]);bool rejected=false,erased=false;
    std::unique_ptr<Names> names;std::unique_ptr<Machine<tls_mpc_worker::Share>> machine;
    std::unique_ptr<Collective> collective;std::unique_ptr<NativeLifecycle> lifecycle;
    auto destroy=[&]{return ErasedHostCall::run([&]{lifecycle.reset();collective.reset();machine.reset();names.reset();});};
    try{
        public_require(ErasedHostCall::run([&]{
            ShamirOptions::singleton={5,2};OnlineOptions opts;opts.playerno=party;opts.live_prep=true;
            opts.security_parameter=128;opts.lg2=128;opts.lgp=255;opts.prime=1;opts.prime<<=255;opts.prime-=19;
            names=std::make_unique<Names>(party,port,std::string(argv[2]));
            machine=std::make_unique<Machine<tls_mpc_worker::Share>>(*names,true,opts);
            collective=std::make_unique<Collective>([&]() -> Player& {return machine->get_player();},PublicBytes(32,53),PublicBytes(32,84));
            lifecycle=std::make_unique<NativeLifecycle>(*machine);
        }),"readiness bootstrap failed");
        public_require(ErasedHostCall::run([&]{
            try{collective->require_local_success(party!=2);}catch(const std::runtime_error&){rejected=true;}
            collective->require_local_success(rejected); // All five observed rejection before any producerVM.
            erased=lifecycle->abort_epoch();public_require(erased,"readiness abort failed");
        }),"readiness failure barrier failed");
        public_require(rejected&&erased&&destroy(),"readiness cleanup failed");
        std::cout<<"collective local failure rejected; no producerVM; erasure barrier passed\n";return 0;
    }catch(...){try{destroy();}catch(...){}std::cerr<<"readiness negative fixture failed\n";return 1;}
}
