// Public disposable protocol fixtures only. Opens decisions, never IDs/bodies.
#include "WebSocketWork/NativeChatResponse.h"
#include "SessionWork/NativeLifecycle.h"
#include "Protocols/Opener.h"
#include <memory>
#include <iostream>
using namespace tls_mpc_worker;
static PublicBytes unhex(const std::string& text){PublicBytes b;for(size_t i=0;i<text.size();i+=2)b.push_back(std::stoul(text.substr(i,2),nullptr,16));return b;}
int main(int argc,char** argv) {
    if(argc!=6)return 2;SecureGmp::install_before_threads();
    std::unique_ptr<Names> names;std::unique_ptr<PinnedPrograms> pinned;
    std::unique_ptr<Machine<tls_mpc_worker::Share>> machine;std::unique_ptr<Worker> worker;
    std::unique_ptr<NativeLifecycle> lifecycle;
    auto destroy=[&] {lifecycle.reset();worker.reset();machine.reset();pinned.reset();names.reset();};
    try {
        unsigned party=std::stoul(argv[1]),port=std::stoul(argv[3]);
        public_require(ErasedHostCall::run([&] {
            pinned=std::make_unique<PinnedPrograms>(argv[4]);ShamirOptions::singleton={5,2};
            OnlineOptions o;o.playerno=party;o.live_prep=true;o.security_parameter=128;o.lg2=128;o.lgp=255;
            o.prime=1;o.prime<<=255;o.prime-=19;names=std::make_unique<Names>(party,port,std::string(argv[2]));
            public_require(names->num_players()==5,"five parties required");
            machine=std::make_unique<Machine<tls_mpc_worker::Share>>(*names,true,o);
            worker=std::make_unique<Worker>(*machine,*pinned);lifecycle=std::make_unique<NativeLifecycle>(*machine);
        }),"chat fixture bootstrap failed");
        std::ifstream cases(argv[5]);std::string raw,id,outcome;size_t accepted=0,rejected=0;
        while(cases>>raw>>id>>outcome) {
            public_require(!rejected,"fixture reused rejected runtime");
            public_require(ErasedHostCall::run([&] {
                auto share=[&](const PublicBytes& bytes) {
                    auto bits=worker->allocate(bytes.size()*8);
                    for(size_t i=0;i<bits.size();++i)bits[i][0]=tls_mpc_worker::Bit::constant((bytes[i/8]>>(7-i%8))&1,party,machine->get_bit_mac_key());
                    return bits;
                };
                auto release=[&](const tls_mpc_worker::Bits& bits) {
                    public_require(bits.size()==24,"fixture attempted non-decision opening");
                    Opener<tls_mpc_worker::Bit> opener(machine->get_player(),machine->get_bit_mac_key());
                    opener.init_open();for(const auto& bit:bits)opener.prepare_open(bit[0]);opener.exchange();
                    PublicBytes value(bits.size()/8,0);
                    for(size_t i=0;i<bits.size();++i)value[i/8]|=(opener.finalize_open().get()&1)<<(7-i%8);
                    opener.Check();return value;
                };
                NativeChatResponse parser(*worker,*pinned,4096,share(unhex(id)),share);
                auto start=parser.step(share({0}),share({255}),share({0}),share({0}));
                auto wire=unhex(raw);
                for(size_t i=0;i<wire.size();++i) {
                    if(i%17==0) {auto idle=parser.step(share({0}),share({0}),share({0}),share({173}));}
                    auto event=parser.step(share({255}),share({0}),share({uint8_t(i+1==wire.size()?255:0)}),share({wire[i]}));
                }
                bool failed=false;NativeChatResponse::Result result{false,false};
                try {result=parser.finish_chunk(release);}catch(const std::runtime_error&){failed=true;}
                if(outcome=="reject") {public_require(failed,"wrong request ID accepted");++rejected;}
                else {public_require(!failed&&result.complete&&result.successful==(outcome=="success"),"private response outcome mismatch");++accepted;}
                parser.close();
                if(rejected)public_require(lifecycle->abort_epoch()&&lifecycle->abort_epoch(),"chat reject abort failed");
                else lifecycle->renew_epoch();
            }),"native chat/correlation fixture failed");
        }
        public_require(accepted==4&&rejected==1,"missing native chat cases");
        public_require(ErasedHostCall::run(destroy),"chat fixture teardown failed");
        std::cout<<"native private chat fixture passed: four accepted decisions; one wrong-ID rejection; IDs/status numbers/body/header/length never opened; terminal abort\n";return 0;
    } catch(...) {ErasedHostCall::run(destroy);std::cerr<<"native chat fixture failed\n";return 1;}
}
