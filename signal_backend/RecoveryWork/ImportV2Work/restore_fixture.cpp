// PUBLIC bounded session-snapshot fixture, not full-account/certified recovery.
#include "RawFieldReadmitV2.h"
#include "../NativeRecordAdmission.h"
#include "../NativeCanonicalSendOwner.h"
#include "../CiphertextStore.h"
#include "NativeCollective.h"
#include "SessionWork/NativeLifecycle.h"
#include "Protocols/Opener.h"
#include "Tools/FailureScope.h"
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
using namespace tls_mpc_worker;
using namespace signal_mpc;
using namespace signal_mpc::recovery;
using SecretBits=tls_mpc_worker::Bits;
static SecretBits clone(const SecretBits& b){return {b.begin(),b.end()};}
static void append(SecretBits& a,const SecretBits& b){a.insert(a.end(),b.begin(),b.end());}
static SecretBits slice(const SecretBits& a,size_t byte,size_t count){public_require(byte+count<=a.size()/8,"restore slice bounds");return {a.begin()+8*byte,a.begin()+8*(byte+count)};}
static PublicBytes decode(const std::string& s){PublicBytes b;for(size_t i=0;i<s.size();i+=2)b.push_back(std::stoul(s.substr(i,2),nullptr,16));return b;}
static size_t frame_capacity(){return VariableShape(260,80,false,false).frame_capacity();}
static size_t pending_bytes(){return frame_capacity()+3+8;}
static ShareDomain old_domain(unsigned party,const PinnedPrograms& pin){ShareDomain d{};d.party=party;d.epoch=1;d.slot=2;d.bit_count=8*(6686+pending_bytes());d.context.fill(71);d.membership.fill(72);d.schema.fill(2);d.sharing_epoch.fill(73);std::copy_n(pin.digest().begin(),32,d.manifest.begin());return d;}
static std::array<unsigned char,64> key(unsigned party){std::array<unsigned char,64> k;for(size_t i=0;i<64;++i)k[i]=i+party*7;return k;}
struct Completion {size_t& done;~Completion(){++done;}};
struct HelperScope {Completion completion;import_v2::RawFieldReadmitV2 helper;HelperScope(size_t& done,Player& p):completion{done},helper(p){}};
struct State {
 std::unique_ptr<Names> names;std::unique_ptr<PinnedPrograms> pin;std::unique_ptr<Machine<tls_mpc_worker::Share>> machine;
 std::unique_ptr<Worker> worker;std::unique_ptr<NativeLifecycle> lifecycle;std::unique_ptr<Collective> collective;
 std::optional<QuarantinedEvaluations> raw;SecretBits restored,valid;Digest fresh_sharing{};size_t helper_done=0;bool helper_entered=false,helper_constructed=false,consistency_rejected=false,cancel_hit=false,load_attempted=false,local_ready=false;
};
static PublicBytes open_fixture(State& s,const SecretBits& bits){Opener<tls_mpc_worker::Bit> open(s.machine->get_player(),s.machine->get_bit_mac_key());open.init_open();for(const auto& b:bits)open.prepare_open(b[0]);open.exchange();PublicBytes bytes(bits.size()/8);for(size_t i=0;i<bits.size();++i)bytes[i/8]|=(open.finalize_open().get()&1)<<(7-i%8);open.Check();return bytes;}
static SecretBits constants(State& s,const PublicBytes& bytes){auto out=s.worker->allocate(bytes.size()*8);for(size_t i=0;i<out.size();++i)out[i][0]=tls_mpc_worker::Bit::constant((bytes[i/8]>>(7-i%8))&1,s.machine->get_player().my_num(),s.machine->get_bit_mac_key(),1);return out;}
struct Transaction {
 State& state;OwnShareBox& box;CiphertextStore& files;SecretBits retained;unsigned party;size_t reserves=0,commits=0,retained_checks=0;
 void save(unsigned phase,const SecretBits& bits){auto d=old_domain(party,*state.pin);d.slot=3;d.bit_count=bits.size();auto tag=label("PARTIAL-CANONICAL-RESTORE-V2");tag.push_back(phase);d.schema=signal_mpc::recovery::hash(tag);d.sharing_epoch=state.fresh_sharing;auto encrypted=NativeOwnShareArchive::seal(d,bits,state.machine->get_player(),box);auto digest=files.put(encrypted);
  if(phase==2){auto restored=box.open_quarantined(d,files.get(digest,encrypted.size()));for(size_t i=0;i<retained.size();++i){unsigned char local[16];detail::encode_own_evaluation(local,static_cast<const gf2n_long&>(retained[i][0].get_regs()[0]));public_require(std::memcmp(local,restored.local_bytes().data()+16*(6686*8+i),16)==0,"retained outbox archive mismatch");sodium_memzero(local,16);}++retained_checks;}}
 void reserve(const std::vector<VariableShape>& shapes,const std::vector<NativeCanonicalSendOwner::Prestate>& values){public_require(shapes.size()==1&&values.size()==1&&reserves==0,"restore reserve ordering");auto bits=clone(values[0].record);append(bits,values[0].selected);append(bits,values[0].call);append(bits,retained);save(1,bits);++reserves;}
 void commit(const std::vector<VariableShape>& shapes,const std::vector<NativeCanonicalSendOwner::Poststate>& values){public_require(shapes.size()==1&&values.size()==1&&reserves==1&&commits==0,"restore commit ordering");auto bits=clone(values[0].record);append(bits,values[0].selected);append(bits,values[0].service);append(bits,retained);append(bits,values[0].outbox);append(bits,values[0].request_id);save(2,bits);++commits;}
};
int main(int argc,char**argv){SecureGmp::install_before_threads();if(argc!=9)return 2;auto* s=new State;bool passed=false,epoch_completed=false;uint64_t import_generation=0,epoch_generation=0;unsigned party=std::stoul(argv[1]);std::string mode=argv[8];size_t before_stacks=ErasingThreadStack::wiped_stacks.load();
 try {
  public_require(ErasedHostCall::run([&]{
   ShamirOptions::singleton={5,2};OnlineOptions opts;opts.playerno=party;opts.live_prep=true;opts.security_parameter=128;opts.lg2=128;opts.lgp=255;opts.batch_size=4096;opts.prime=1;opts.prime<<=255;opts.prime-=19;
   s->names=std::make_unique<Names>(party,std::stoul(argv[3]),std::string(argv[2]));s->pin=std::make_unique<PinnedPrograms>(argv[4]);
   s->machine=std::make_unique<Machine<tls_mpc_worker::Share>>(*s->names,true,opts);s->worker=std::make_unique<Worker>(*s->machine,*s->pin);s->lifecycle=std::make_unique<NativeLifecycle>(*s->machine);
   s->collective=std::make_unique<Collective>([&]()->Player&{return s->machine->get_player();},s->pin->digest(),PublicBytes(32,74));PinnedPrograms extension(argv[5]);s->collective->agree_program("record-admission-v1",extension.digest());s->pin->append(extension);auto sharing=s->collective->public_random();std::copy_n(sharing.begin(),32,s->fresh_sharing.begin());
   s->load_attempted=true;bool ready=false;try{OwnShareBox box(key(party));auto d=old_domain(party,*s->pin);auto wanted=d.header();std::filesystem::path dir=std::string(argv[6])+"-party"+std::to_string(party);CiphertextStore files(dir.string());size_t found=0;
    for(auto& entry:std::filesystem::directory_iterator(dir)){if(entry.path().extension()!=".box")continue;std::ifstream file(entry.path(),std::ios::binary);Bytes header(wanted.size());file.read(reinterpret_cast<char*>(header.data()),header.size());if(header!=wanted)continue;auto name=entry.path().filename().string();public_require(name.size()==73,"restore blob name");Digest digest;for(size_t i=0;i<32;++i)digest[i]=std::stoul(name.substr(5+2*i,2),nullptr,16);auto cipher=files.get(digest,wanted.size()+16+d.bit_count*16);if(mode=="aead"&&party==4)cipher.back()^=1;s->raw.emplace(box.open_quarantined(d,cipher));++found;}
    public_require(found==1,"restore head selection");ready=true;
   }catch(...){s->raw.reset();}s->local_ready=ready;s->collective->require_local_success(ready);
  }),"restore load/collective readiness failed");
  bool imported=ErasedHostCall::run([&]{
   import_generation=ErasedHostCall::generation();
   try {auto full=old_domain(party,*s->pin);{
    s->helper_entered=true;HelperScope scope(s->helper_done,s->machine->get_player());s->helper_constructed=true;
    if(mode=="cancel"){s->cancel_hit=true;throw std::runtime_error("public fixture cancellation after helper construction");}
    for(size_t offset=0;offset<full.bit_count;offset+=4096){size_t count=std::min<size_t>(4096,full.bit_count-offset);SecretBytes bytes(count*16);std::memcpy(bytes.data(),s->raw->local_bytes().data()+16*offset,count*16);
     if(offset==0&&((mode=="one"&&party==4)||(mode=="two"&&(party==3||party==4))))bytes.data()[12]^=1;
     if(offset==0&&mode=="nonbit")bytes.data()[0]^=2;
     auto domain=full;domain.bit_count=count;auto fresh=scope.helper.values_candidate(QuarantinedEvaluations(std::move(bytes)),domain,*s->worker);append(s->restored,fresh);
    }
   }public_require(s->helper_done==1,"helper destruction incomplete");s->raw.reset();
   if(mode=="semantic")s->restored[5550*8][0].get_regs()[0]+=gf2n_long(1);
   NativeRecordAdmission validator(*s->machine,*s->worker,*s->pin);s->valid=validator.evaluate(slice(s->restored,0,6686));
   }catch(...){try{throw;}catch(const std::exception& error){s->consistency_rejected=std::string(error.what())=="private share consistency/bitness import failed";}catch(...){}s->restored.clear();s->valid.clear();s->raw.reset();throw;}
  });
  if(mode=="one"||mode=="two"||mode=="nonbit"||mode=="cancel"){
   public_require(!imported&&s->helper_constructed&&s->helper_done==1&&((mode=="cancel"&&s->cancel_hit)||(mode!="cancel"&&s->consistency_rejected))&&s->restored.empty()&&s->valid.empty()&&!s->raw,"failed helper did not clear owned inputs");passed=true;
  }else{
   public_require(imported&&s->helper_done==1,"restore import failed");
   // The import/helper stack is now completely erased BEFORE runtime renewal.
   public_require(ErasedHostCall::run([&]{public_require(!s->lifecycle->application_allowed(),"fresh runtime incorrectly admitted");s->lifecycle->renew_epoch();epoch_generation=ErasedHostCall::generation();public_require(!s->lifecycle->application_allowed(),"retirement bypassed current host barrier");}),"restore epoch retirement failed");epoch_completed=ErasedHostCall::completed(epoch_generation);public_require(epoch_completed&&ErasedHostCall::completed(import_generation),"host completion evidence absent");
   public_require(ErasedHostCall::run([&]{public_require(s->lifecycle->application_allowed(),"completed retirement barrier absent");auto valid=open_fixture(*s,s->valid);
    if(mode=="semantic"){public_require(valid==PublicBytes(1,0),"incoherent selected state admitted");return;}
    public_require(mode=="positive"&&valid==PublicBytes(1,255),"unsupported restore mode or invalid record");
    std::ifstream input(argv[7]);std::string encoded;auto read=[&](){public_require(bool(input>>encoded),"resume fixture truncated");return decode(encoded);};auto expected=read(),after=read(),payload=read(),timestamp=read();public_require(expected.size()==6686&&after.size()==6686,"resume expectation shape");
    auto values=slice(s->restored,0,6686);append(values,constants(*s,expected));auto flag=s->worker->allocate(8);std::vector<FunctionArgument> args={{1,values.function_argument()},{1,flag.function_argument()}};s->pin->verify_function("signal_canonical_fixture_equal_53488",args);FunctionArgument ignored;s->machine->run_function("signal_canonical_fixture_equal_53488",ignored,args);public_require(open_fixture(*s,flag)==PublicBytes(1,255),"restored canonical/selected/service state mismatch");
    auto old_outbox=slice(s->restored,6686,pending_bytes());auto replay=open_fixture(*s,slice(old_outbox,0,frame_capacity()+3));public_require(replay[0]==255,"old outbox invalid");size_t length=256*replay[1]+replay[2];public_require(length<=frame_capacity(),"old outbox length");std::cout<<"OLD ";for(size_t i=3;i<3+length;++i)std::cout<<std::hex<<std::setw(2)<<std::setfill('0')<<unsigned(replay[i]);std::cout<<std::dec<<'\n';
    auto dir=std::string(argv[7])+"-resumed-party"+std::to_string(party);std::filesystem::create_directory(dir);OwnShareBox box(key(party));CiphertextStore files(dir);Transaction tx{*s,box,files,clone(old_outbox),party};NativeVariableService service(*s->machine,*s->worker,*s->pin);NativeRecordBinding binding(*s->machine,*s->worker,*s->pin);auto service_view=slice(s->restored,6075,611);auto id=slice(service_view,594,8);
    NativeCanonicalSendOwner owner(VariableShape(260,80,false,false),slice(s->restored,0,5550),slice(s->restored,5550,525),std::move(service_view),dir+"/fence",service,binding);
    // Synthetic component ACK policy; retained old immutable outbox is included
    // unchanged in BOTH new snapshots. Real correlated response policy remains required.
    auto produced=owner.produce(constants(*s,payload),constants(*s,timestamp),std::move(id),tx);
    auto post=clone(owner.record_snapshot());append(post,owner.selected_snapshot());append(post,owner.service_snapshot());append(post,constants(*s,after));auto post_flag=s->worker->allocate(8);std::vector<FunctionArgument> post_args={{1,post.function_argument()},{1,post_flag.function_argument()}};s->pin->verify_function("signal_canonical_fixture_equal_53488",post_args);s->machine->run_function("signal_canonical_fixture_equal_53488",ignored,post_args);public_require(open_fixture(*s,post_flag)==PublicBytes(1,255),"resumed canonical state mismatch");
    auto wire=open_fixture(*s,produced.payload);public_require(wire[0]==255,"resumed service rejected");length=256*wire[1]+wire[2];public_require(length<=frame_capacity(),"resumed length");std::cout<<"NEW ";for(size_t i=3;i<3+length;++i)std::cout<<std::hex<<std::setw(2)<<std::setfill('0')<<unsigned(wire[i]);std::cout<<std::dec<<'\n';owner.response_complete(produced.ticket);public_require(tx.reserves==1&&tx.commits==1&&tx.retained_checks==1,"resumed transaction missing");owner.close();
   }),"restore admission/continuation check failed");passed=true;
  }
 }catch(...){if(mode=="aead"&&s->load_attempted&&!s->helper_entered&&s->local_ready==(party!=4))passed=true;else std::cerr<<"restore fixture category=phase\n";}
 size_t helper_completed=s->helper_done;bool import_completed=ErasedHostCall::completed(import_generation);
 bool cleaned=ErasedHostCall::run([&]{s->raw.reset();s->restored.clear();s->valid.clear();if(s->lifecycle&&s->machine&&!s->machine->queues.empty())s->lifecycle->abort_epoch();delete s;s=nullptr;});
 bool owners_closed=tls_caught_failure::runtime_sockets.active()==0&&!tls_caught_failure::runtime_join_error&&tls_caught_failure::runtime_threads_started==tls_caught_failure::runtime_threads_joined;
 if(passed&&cleaned&&owners_closed){std::cout<<"RESTORE_FIXTURE {\"passed\":true,\"mode\":\""<<mode<<"\",\"helper_completed\":"<<helper_completed<<",\"import_host_completed\":"<<(import_completed?"true":"false")<<",\"epoch_host_completed\":"<<(epoch_completed?"true":"false")<<",\"stack_wipes\":"<<ErasingThreadStack::wiped_stacks.load()-before_stacks<<"}\n";return 0;}return 1;
}
