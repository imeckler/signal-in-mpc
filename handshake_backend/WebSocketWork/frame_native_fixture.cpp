// Public disposable response only. No private production bodies are opened.
#include "WebSocketWork/NativeUpgradeResponse.h"
#include "WebSocketWork/NativeFrame.h"
#include <array>
#include "SessionWork/NativeLifecycle.h"
#include "Protocols/Opener.h"
#include <memory>
#include <iostream>
using namespace tls_mpc_worker;
int main(int argc,char** argv) {
    if(argc!=5)return 2;SecureGmp::install_before_threads();
    std::unique_ptr<Names> names;std::unique_ptr<PinnedPrograms> pinned;
    std::unique_ptr<Machine<tls_mpc_worker::Share>> machine;
    std::unique_ptr<Worker> worker;std::unique_ptr<NativeLifecycle> lifecycle;
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
        }),"upgrade fixture bootstrap failed");
        for(bool invalid:{false,true}) {
            public_require(ErasedHostCall::run([&] {
                auto share=[&](const PublicBytes& bytes) {
                    auto bits=worker->allocate(bytes.size()*8);
                    for(size_t i=0;i<bits.size();++i)bits[i][0]=tls_mpc_worker::Bit::constant((bytes[i/8]>>(7-i%8))&1,party,machine->get_bit_mac_key());
                    return bits;
                };
                auto release=[&](const tls_mpc_worker::Bits& bits) {
                    Opener<tls_mpc_worker::Bit> opener(machine->get_player(),machine->get_bit_mac_key());
                    opener.init_open();for(const auto& bit:bits)opener.prepare_open(bit[0]);opener.exchange();
                    PublicBytes out(bits.size()/8,0);
                    for(size_t i=0;i<bits.size();++i)out[i/8]|=(opener.finalize_open().get()&1)<<(7-i%8);
                    opener.Check();return out;
                };
                const std::string accept="s3pPLMBiTxaQ9kYGzzhZRbK+xOo=";
                NativeUpgradeResponse parser(*worker,*pinned,PublicBytes(accept.begin(),accept.end()),share);
                NativeFrame frames(*worker,*pinned,4096,share);
                std::string response="HTTP/1.1 101 Switching Protocols\r\nSEC-websocket-accept: "+
                  accept+"\r\nX-Extra: bounded\r\nConnection:\t Upgrade \t\r\nupgrade: WebSocket\r\n\r\n";
                if(invalid) {
                    response.append("\x82\x80",2);response.append(4,'\0');
                } else {
                    const unsigned char wire[]={2,2,'a','b',137,1,'X',128,2,'c','d',138,0,136,2,3,232};
                    response.append(reinterpret_cast<const char*>(wire),sizeof(wire));
                }
                std::array<tls_mpc_worker::Bits,6> events;
                bool rejected=false,complete=false;size_t offset=0;
                for(size_t count:{size_t(50),size_t(41),response.size()-91}) {
                    PublicBytes padded(128,173);
                    for(size_t i=0;i<count;++i)padded[i]=uint8_t(response[offset+i]);
                    try {
                        complete=parser.feed(PrivatePayload(share(padded),share({uint8_t(count>>8),uint8_t(count)}),share({255}),128),
                          release,[&](tls_mpc_worker::Bits byte,tls_mpc_worker::Bits active) {
                            auto e=frames.step(std::move(active),std::move(byte));
                            const tls_mpc_worker::Bits* values[]={&e.data,&e.control,&e.message_start,&e.frame_done,&e.message_done,&e.control_done};
                            for(size_t i=0;i<6;++i)events[i].insert(events[i].end(),values[i]->begin(),values[i]->end());
                          });
                        frames.finish_chunk(release);
                    } catch(const std::runtime_error&) {rejected=true;break;}
                    offset+=count;
                    if(!invalid&&offset<response.size())public_require(!complete,"premature upgrade completion");
                }
                public_require(rejected==invalid,"combined frame acceptance mismatch");
                if(!invalid) {
                    public_require(complete,"upgrade never completed");
                    const size_t expected[]={4,3,1,5,1,3};
                    for(size_t i=0;i<6;++i) {
                        auto flags=release(events[i]);size_t count=0;
                        for(auto flag:flags){public_require(flag==0||flag==255,"noncanonical frame event");count+=flag==255;}
                        public_require(count==expected[i],"fragment/control/message event mismatch");
                    }
                }
                for(auto& e:events)e.clear();frames.close();parser.close();
                if(invalid)public_require(lifecycle->abort_epoch()&&lifecycle->abort_epoch(),"upgrade reject abort failed");
                else lifecycle->renew_epoch();
            }),"native upgrade parser/retirement failed");
        }
        public_require(ErasedHostCall::run(destroy),"upgrade fixture teardown failed");
        std::cout<<"native HTTP/frame fixture passed: private retained state; private HTTP chunks; binary fragmentation; interleaved ping/pong/close; masked server frame rejects; terminal abort\n";return 0;
    } catch(...) {ErasedHostCall::run(destroy);std::cerr<<"native HTTP/frame fixture failed\n";return 1;}
}
