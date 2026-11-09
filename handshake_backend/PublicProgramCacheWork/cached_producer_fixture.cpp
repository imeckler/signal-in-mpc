// PUBLIC DISPOSABLE COMPONENT FIXTURE, not normal provider/bootstrap/TLS.
// Selected ratchet state, identities, fresh scalars/DHs remain unopened. Only
// final fixture wire and builder validity are explicitly declassified.
#include "NativeWorker.h"
#include "NativeCollective.h"
#include "SessionWork/NativeLifecycle.h"
#include "CachedBatchService.h"
#include "../../signal_backend/VariableServiceWork/VariableSendBatch.h"
#include "../../signal_backend/TextNotificationWork/PublicTextFixture.h"
#include "../../signal_backend/TextNotificationWork/TextNotificationInput.h"
#include "Protocols/Opener.h"
#include "Tools/PublicProtocolMetrics.h"
#include <sys/resource.h>
#include <time.h>
#include <iomanip>
#include <iostream>
using namespace tls_mpc_worker;
using Store=signal_mpc::VariableSendStore<tls_mpc_worker::Bits>;
static uint64_t now_ns(){timespec t;clock_gettime(CLOCK_MONOTONIC_RAW,&t);return uint64_t(t.tv_sec)*1000000000+t.tv_nsec;}
struct State {std::unique_ptr<Names> names;std::unique_ptr<PinnedCacheAdmission> admission;std::unique_ptr<Machine<tls_mpc_worker::Share>> machine;std::unique_ptr<NativeLifecycle> lifecycle;std::unique_ptr<Worker> worker;std::vector<std::unique_ptr<Store>> stores;};
int main(int argc,char**argv){
 SecureGmp::install_before_threads();if(argc!=6)return 2;auto s=new State;unsigned party=std::stoul(argv[1]),port=std::stoul(argv[3]);
 try{
 public_require(ErasedHostCall::run([&]{s->admission=std::make_unique<PinnedCacheAdmission>(argv[4]);ShamirOptions::singleton={5,2};OnlineOptions o;o.playerno=party;o.live_prep=true;o.security_parameter=128;o.lg2=128;o.lgp=255;o.prime=1;o.prime<<=255;o.prime-=19;s->names=std::make_unique<Names>(party,port,std::string(argv[2]));public_require(s->names->num_players()==5,"five parties required");s->machine=std::make_unique<Machine<tls_mpc_worker::Share>>(*s->names,true,o);s->lifecycle=std::make_unique<NativeLifecycle>(*s->machine);s->worker=std::make_unique<Worker>(*s->machine,s->admission->programs());}),"cached producer bootstrap failed");
 auto public_bits=[&](const PublicBytes&bytes){auto out=s->worker->allocate(bytes.size()*8);for(size_t i=0;i<out.size();++i)out[i][0]=tls_mpc_worker::Bit::constant((bytes[i/8]>>(7-i%8))&1,party,s->machine->get_bit_mac_key());return out;};
 auto open_fixture=[&](const tls_mpc_worker::Bits&bits){public_require(bits.size()%8==0,"fixture byte dimensions");Opener<tls_mpc_worker::Bit> opener(s->machine->get_player(),s->machine->get_bit_mac_key());opener.init_open();for(const auto&b:bits)opener.prepare_open(b[0]);opener.exchange();PublicBytes bytes(bits.size()/8);for(size_t i=0;i<bits.size();++i)bytes[i/8]|=(opener.finalize_open().get()&1)<<(7-i%8);opener.Check();return bytes;};
 signal_mpc::VariableShape shape(260,80,false,false);
 public_require(ErasedHostCall::run([&]{for(unsigned slot=0;slot<2;++slot)s->stores.emplace_back(new Store(shape,public_bits(signal_mpc::PublicTextFixture::initial(slot)),std::string(argv[5])+"-party"+std::to_string(party)+"-slot"+std::to_string(slot)));}),"cached producer store setup failed");
 for(unsigned round=0;round<2;++round){
  std::vector<PublicBytes> frames;std::vector<uint64_t> tickets;
  public_require(ErasedHostCall::run([&]{
   std::vector<signal_mpc::BatchSendRequest<tls_mpc_worker::Bits>> requests;
   for(unsigned slot=0;slot<2;++slot){
    auto input=public_bits(signal_mpc::PublicTextFixture::text_input(slot,round));auto output=s->worker->allocate(720);std::vector<FunctionArgument>args={{1,input.function_argument()},{1,output.function_argument()}};FunctionArgument ignored;s->admission->run(*s->machine,"signal_private_text_notification_48_80",ignored,args);
    auto text=signal_mpc::split_text_notification(std::move(output));public_require(open_fixture(text.validity)==PublicBytes{255},"fixture builder rejected");
    PublicBytes id(8);uint64_t value=(uint64_t(1)<<63)+2*round+slot;for(size_t i=0;i<8;++i)id[7-i]=(value>>(8*i))&255;
    requests.push_back({s->stores[slot].get(),std::move(text.payload),std::move(text.timestamp),public_bits(id)});
   }
   auto before=tls_public_diagnostics::snapshot();auto before_cache=s->machine->public_program_cache_metrics();auto started=now_ns();
   CachedBatchService service(*s->machine,*s->worker,*s->admission);
   auto produced=signal_mpc::produce_batch_with_checkpoint<tls_mpc_worker::Bits>(std::move(requests),[](const auto&,const auto&){},[&](const auto&shapes,std::vector<tls_mpc_worker::Bits>inputs){return service.evaluate(shapes,std::move(inputs));},[](const auto&,const auto&){});
   auto elapsed=now_ns()-started;auto after=tls_public_diagnostics::snapshot();auto cache=s->machine->public_program_cache_metrics();auto usage=s->machine->public_function_usage(); // Job-local: runtime resets usage on every tape.
   if(round==1)public_require(cache[1]==before_cache[1]&&cache[0]>before_cache[0],"real producer reloaded after epoch/interleave");
   std::cout<<"CACHED_PRODUCER_METRIC {\"round\":"<<round<<",\"instances\":2,\"call_ns\":"<<elapsed<<",\"prepare_ns\":"<<after.prepare_ns-before.prepare_ns<<",\"load_ns\":"<<after.load_ns-before.load_ns<<",\"prepare_calls\":"<<after.prepare_calls-before.prepare_calls<<",\"load_calls\":"<<after.load_calls-before.load_calls<<",\"cache_hits_delta\":"<<cache[0]-before_cache[0]<<",\"cache_loads_delta\":"<<cache[1]-before_cache[1]<<",\"epoch\":"<<s->machine->worker_epoch<<",\"bytes\":[";for(unsigned i=0;i<9;++i){if(i)std::cout<<',';std::cout<<after.bytes[i]-before.bytes[i];}std::cout<<"],\"consumed\":[";bool first=true;for(size_t f=0;f<N_DATA_FIELD_TYPE;++f)for(size_t k=0;k<N_DTYPE;++k)if(usage.files[f][k]){if(!first)std::cout<<',';first=false;std::cout<<'['<<f<<','<<k<<','<<usage.files[f][k]<<']';}std::cout<<"]}\n"<<std::flush;
   for(auto&item:produced){auto bytes=open_fixture(item.payload);public_require(bytes.size()==3+shape.frame_capacity()&&bytes[0]==255,"fixture producer rejected");size_t length=size_t(bytes[1])*256+bytes[2];public_require(length<=shape.frame_capacity()&&std::all_of(bytes.begin()+3+length,bytes.end(),[](auto b){return b==0;}),"fixture payload framing");frames.emplace_back(bytes.begin()+3,bytes.begin()+3+length);tickets.push_back(item.ticket);}
  }),"cached producer evaluation/barrier failed");
  // Owned helper traces are gone and the host stack completed before renewal.
  public_require(ErasedHostCall::run([&]{s->lifecycle->renew_epoch();}),"cached producer renewal failed");
  for(unsigned slot=0;slot<2;++slot){std::cout<<"FRAME "<<round<<' '<<slot<<' ';for(auto b:frames[slot])std::cout<<std::hex<<std::setw(2)<<std::setfill('0')<<unsigned(b);std::cout<<std::dec<<'\n';}
  public_require(ErasedHostCall::run([&]{for(unsigned slot=0;slot<2;++slot)s->stores[slot]->response_complete(tickets[slot]);}),"synthetic component acknowledgement failed");
 }
 public_require(ErasedHostCall::run([&]{s->stores.clear();public_require(s->lifecycle->abort_epoch(),"cached producer abort failed");delete s;s=nullptr;}),"cached producer destructor barrier failed");
 rusage usage;getrusage(RUSAGE_SELF,&usage);std::cout<<"CACHED_PRODUCER_RSS {\"maxrss_bytes\":"<<usage.ru_maxrss<<"}\nprivate cached producer fixture passed\n";return 0;
 }catch(...){if(s){try{ErasedHostCall::run([&]{s->stores.clear();s->lifecycle->abort_epoch();delete s;s=nullptr;});}catch(...){}}std::cerr<<"private cached producer fixture failed\n";return 1;}
}
