#include "NativeWorker.h"
#include "SessionWork/NativeLifecycle.h"
#include "Protocols/Opener.h"
#include <iostream>
using namespace tls_mpc_worker;
struct State{std::unique_ptr<Names> names;std::unique_ptr<PinnedPrograms> pinned;std::unique_ptr<Machine<tls_mpc_worker::Share>> machine;std::unique_ptr<NativeLifecycle> lifecycle;std::unique_ptr<Worker> worker;};
int main(int argc,char**argv){
 SecureGmp::install_before_threads();if(argc!=5)return 2;auto s=new State;auto party=unsigned(std::stoul(argv[1]));
 try{
 public_require(ErasedHostCall::run([&]{s->pinned=std::make_unique<PinnedPrograms>(argv[4]);ShamirOptions::singleton={5,2};OnlineOptions o;o.playerno=party;o.live_prep=true;o.security_parameter=128;o.lg2=128;o.lgp=255;o.prime=1;o.prime<<=255;o.prime-=19;s->names=std::make_unique<Names>(party,std::stoul(argv[3]),std::string(argv[2]));public_require(s->names->num_players()==5,"five parties required");s->machine=std::make_unique<Machine<tls_mpc_worker::Share>>(*s->names,true,o);s->lifecycle=std::make_unique<NativeLifecycle>(*s->machine);s->worker=std::make_unique<Worker>(*s->machine,*s->pinned);}),"remask bootstrap");
 for(unsigned mode=0;mode<4;++mode)public_require(ErasedHostCall::run([&]{
 constexpr size_t cap=1290,len=200;PublicBytes raw(cap+4,0);raw[0]=mode==2?0:255;raw[1]=255;raw[2]=len>>8;raw[3]=len&255;raw[4]=130;raw[5]=254;raw[6]=(len-8)>>8;raw[7]=(len-8)&255;
 for(size_t i=0;i<4;++i)raw[8+i]=i+1;
 for(size_t i=0;i<len-8;++i)raw[12+i]=uint8_t(i+41)^uint8_t(1+i%4);
 if(mode==3)raw[4+len]=1;
 auto input=s->worker->allocate(raw.size()*8);for(size_t i=0;i<raw.size();++i)for(size_t j=0;j<8;++j)input[8*i+j][0]=tls_mpc_worker::Bit::constant((raw[i]>>(7-j))&1,party,s->machine->get_bit_mac_key());
 auto output=s->worker->binary("tls-websocket-remask-1290",std::move(input),(cap+3)*8);
 Opener<tls_mpc_worker::Bit> opener(s->machine->get_player(),s->machine->get_bit_mac_key());opener.init_open();for(auto& bit:output)opener.prepare_open(bit[0]);opener.exchange();PublicBytes opened(cap+3,0);for(size_t i=0;i<output.size();++i)opened[i/8]|=(opener.finalize_open().get()&1)<<(7-i%8);opener.Check();
 if(mode<2){public_require(opened[0]==255&&opened[1]==0&&opened[2]==len&&opened[3]==130&&opened[4]==254,"remask positive header");
  for(size_t i=0;i<len-8;++i)public_require((opened[11+i]^opened[7+i%4])==uint8_t(i+41),"unmasked payload changed");
  for(size_t i=3+len;i<opened.size();++i)public_require(opened[i]==0,"remask padding changed");
  std::cout<<"REMASK_PUBLIC_MASK "<<mode;for(size_t i=7;i<11;++i)std::cout<<' '<<unsigned(opened[i]);std::cout<<'\n';
 }else for(auto byte:opened)public_require(byte==0,"rejected remask output released");
 output.clear();s->lifecycle->renew_epoch();
 }),"remask computation/barrier");
 public_require(ErasedHostCall::run([&]{public_require(s->lifecycle->abort_epoch(),"remask abort");delete s;s=nullptr;}),"remask teardown");std::cout<<"private native remask fixture passed\n";return 0;
 }catch(...){if(s){try{ErasedHostCall::run([&]{if(s->lifecycle)s->lifecycle->abort_epoch();delete s;s=nullptr;});}catch(...){}}std::cerr<<"private native remask fixture failed\n";return 1;}
}
