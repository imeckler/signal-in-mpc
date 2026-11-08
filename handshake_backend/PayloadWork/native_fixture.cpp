// Disposable public fixture only. Actual MPC output, authenticated status gate,
// ciphertext comparison and runtime retirement; no live application imports.
#include "PayloadWork/StatusGate.h"
#include "SessionWork/NativeLifecycle.h"
#include "Protocols/Opener.h"
#include <fstream>
#include <memory>
#include <iostream>
using namespace tls_mpc_worker;
static PublicBytes unhex(const std::string& s) {
    public_require(s.size()%2==0,"invalid fixture hex");PublicBytes out;
    for(size_t i=0;i<s.size();i+=2)out.push_back(std::stoul(s.substr(i,2),nullptr,16));return out;
}
int main(int argc,char** argv) {
    if(argc!=6)return 2;
    SecureGmp::install_before_threads();
    std::unique_ptr<Names> names;std::unique_ptr<PinnedPrograms> pinned;
    std::unique_ptr<Machine<tls_mpc_worker::Share>> machine;std::unique_ptr<Worker> worker;
    std::unique_ptr<NativeLifecycle> lifecycle;
    try {
        unsigned party=std::stoul(argv[1]),port=std::stoul(argv[3]);
        public_require(ErasedHostCall::run([&] {
            pinned=std::make_unique<PinnedPrograms>(argv[4]);ShamirOptions::singleton={5,2};
            OnlineOptions o;o.playerno=party;o.live_prep=true;o.security_parameter=128;o.lg2=128;o.lgp=255;
            o.prime=1;o.prime<<=255;o.prime-=19;
            names=std::make_unique<Names>(party,port,std::string(argv[2]));
            public_require(names->num_players()==5,"five parties required");
            machine=std::make_unique<Machine<tls_mpc_worker::Share>>(*names,true,o);
            worker=std::make_unique<Worker>(*machine,*pinned);
            lifecycle=std::make_unique<NativeLifecycle>(*machine);
        }),"fixture bootstrap failed");
        std::ifstream cases(argv[5]);std::string input,expected;size_t valid=0,rejected=0;
        while(cases>>input>>expected) {
            public_require(!rejected,"fixture tried to reuse rejected lifecycle");
            public_require(ErasedHostCall::run([&] {
                auto bytes=unhex(input);public_require(bytes.size()==55,"bad fixture input size");
                size_t releases=0;
                {
                    auto shared=worker->allocate(bytes.size()*8);
                    for(size_t i=0;i<shared.size();++i)shared[i][0]=tls_mpc_worker::Bit::constant((bytes[i/8]>>(7-i%8))&1,party,machine->get_bit_mac_key());
                    auto sealed=worker->binary("tls-seal-private-record-16",std::move(shared),39*8);
                    auto release=[&](const tls_mpc_worker::Bits& bits) {
                        ++releases;Opener<tls_mpc_worker::Bit> opener(machine->get_player(),machine->get_bit_mac_key());
                        opener.init_open();for(const auto& bit:bits)opener.prepare_open(bit[0]);opener.exchange();
                        PublicBytes out(bits.size()/8,0);
                        for(size_t i=0;i<bits.size();++i)out[i/8]|=(opener.finalize_open().get()&1)<<(7-i%8);
                        opener.Check();return out;
                    };
                    bool failed=false;PublicBytes wire;
                    try {wire=release_private_seal(sealed,16,release);}catch(const std::runtime_error&){failed=true;}
                    if(expected=="reject") {
                        public_require(failed&&releases==1,"rejected payload reconstructed ciphertext");++rejected;
                    } else {
                        public_require(!failed&&releases==2&&wire==unhex(expected),"private ciphertext mismatch");++valid;
                    }
                }
                if(rejected)public_require(lifecycle->abort_epoch()&&lifecycle->abort_epoch(),"terminal abort failed");
                else lifecycle->renew_epoch();
            }),"private seal/gate/retirement failed");
        }
        public_require(valid==4&&rejected==1,"missing fixture cases");
        public_require(ErasedHostCall::run([&] {lifecycle.reset();worker.reset();machine.reset();pinned.reset();names.reset();}),"fixture destruction failed");
        std::cout<<"private seal native fixture passed: four ciphertexts; one authenticated rejection; zero rejected-wire releases; terminal abort\n";
        return 0;
    } catch(...) {
        ErasedHostCall::run([&] {lifecycle.reset();worker.reset();machine.reset();pinned.reset();names.reset();});
        std::cerr<<"private seal native fixture failed\n";return 1;
    }
}
