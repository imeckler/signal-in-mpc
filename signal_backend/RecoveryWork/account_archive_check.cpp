// PUBLIC fixture: actual libsignal record bytes, disposable member/storage keys.
// Other bootstrap sections are dummy, so this is NOT normal account admission.
#include "LocalAccountCheckpoint.h"
#include <filesystem>
#include <fstream>
#include <iostream>
#include <sys/wait.h>
using namespace signal_mpc::recovery;
static Bytes read(const std::string& path){std::ifstream f(path,std::ios::binary);return Bytes(std::istreambuf_iterator<char>(f),{});}
static void save(const std::string& path,const Bytes& bytes){int fd=::open(path.c_str(),O_WRONLY|O_CREAT|O_EXCL,0600);require(fd>=0,"fixture cert create");size_t at=0;while(at<bytes.size()){auto n=::write(fd,bytes.data()+at,bytes.size()-at);require(n>0,"fixture cert write");at+=n;}require(::fsync(fd)==0,"fixture cert sync");::close(fd);auto dir=path.substr(0,path.find_last_of('/'));fd=::open(dir.c_str(),O_RDONLY|O_DIRECTORY);require(fd>=0&&::fsync(fd)==0,"fixture cert directory sync");::close(fd);}
static Digest digest(const char* x){return hash(label(x));}
static std::array<unsigned char,64> storage_key(unsigned party){std::array<unsigned char,64> key{};for(unsigned i=0;i<64;++i)key[i]=i+party*17;return key;}
static Digest signing_seed(unsigned party){Digest seed{};seed[0]=party+1;return seed;}
static Signer signer(unsigned party){return Signer(signing_seed(party));}
static Epoch epoch(){Epoch e{9,{},digest("genesis")};for(unsigned i=0;i<5;++i)e.members[i]=signer(i).public_key();return e;}
static std::vector<SectionCapacity> capacities(){std::vector<SectionCapacity> c;for(unsigned t=1;t<=4;++t)c.push_back({AccountSection(t),0,8*64});for(unsigned conv=0;conv<2;++conv)for(unsigned t=10;t<=16;++t)c.push_back({AccountSection(t),conv,uint64_t(8)*(t==11?8195:t==12?136:t==13?525:t==15?259:64)});return c;}
// Full128bit LOCAL degree2 evaluations. Only disposable PUBLIC fixtures use this
// deterministic polynomial; production capture is NativeOwnShareArchive only.
static QuarantinedEvaluations evaluate(const Bytes& bytes,unsigned party){SecretBytes out(bytes.size()*8*16);using U=unsigned __int128;
 auto mul=[](U a,unsigned b){U r=0;for(unsigned i=0;i<3;++i){if((b>>i)&1)r^=a;bool carry=a>>127;a<<=1;if(carry)a^=0x87;}return r;};unsigned x=party+1;
 for(size_t bit=0;bit<bytes.size()*8;++bit){U a=(U(0xa317c529)<<96)^U(bit+7),b=(U(0xe351c7a9)<<64)^U(bit+19);U y=mul(a,x)^mul(mul(b,x),x)^U((bytes[bit/8]>>(7-bit%8))&1);for(unsigned j=0;j<16;++j)out.data()[16*bit+j]=y>>(8*j);}
 return QuarantinedEvaluations(std::move(out));}
static std::vector<QuarantinedEvaluations> sections(const std::string& fixtures,unsigned round,unsigned party){auto caps=capacities();std::vector<QuarantinedEvaluations> result;
 for(auto& cap:caps){Bytes data(cap.bits/8,0);if(cap.conversation==0&&unsigned(cap.section)>=10){const auto tag=unsigned(cap.section);if(tag==11){auto record=read(fixtures+"/record"+std::to_string(round));require(record.size()<=8192,"fixture record size");data[0]=255;data[1]=record.size()/256;data[2]=record.size();std::copy(record.begin(),record.end(),data.begin()+3);}if(tag==12||tag==13){auto state=read(fixtures+"/state"+std::to_string(round));require(state.size()==525,"fixture selected state");std::copy_n(state.begin(),tag==12?136:525,data.begin());}if(tag==15){auto wire=read(fixtures+"/wire"+std::to_string(round));require(wire.size()<=256,"fixture outbox capacity");data[0]=255;data[1]=wire.size()/256;data[2]=wire.size();std::copy(wire.begin(),wire.end(),data.begin()+3);}if(tag==16)data[0]=1;}
 // Conversation1 remains fixed; it must survive both commits unchanged.
 if(cap.conversation==1)std::fill(data.begin(),data.end(),0x53);
 result.push_back(evaluate(data,party));}return result;}
static CertifiedPhase phase(const Proposal& p,const std::vector<Vote>& votes){return{p,votes};}
int main(int argc,char**argv){require(argc==3,"fixture arguments");std::string directory=argv[1],fixtures=argv[2];auto e=epoch();AccountSchemaV1 schema(2,capacities());
 auto context=digest("account"),manifest=digest("pinned-record-profile"),sharing=digest("CCD128-static-epoch");
 auto child=::fork();require(child>=0,"fixture fork");if(child==0){try{
 std::vector<std::unique_ptr<Signer>> keys;std::vector<std::unique_ptr<OwnShareBox>> boxes;std::vector<std::unique_ptr<CiphertextStore>> stores;std::vector<std::unique_ptr<VoteJournal>> journals;std::vector<std::unique_ptr<LocalAccountCheckpoint>> accounts;
 for(unsigned i=0;i<5;++i){auto path=directory+"/party"+std::to_string(i);std::filesystem::create_directory(path);keys.push_back(std::make_unique<Signer>(signing_seed(i)));boxes.push_back(std::make_unique<OwnShareBox>(storage_key(i)));stores.push_back(std::make_unique<CiphertextStore>(path));journals.push_back(std::make_unique<VoteJournal>(path+"/journal",e,context,i,*keys.back()));accounts.push_back(std::make_unique<LocalAccountCheckpoint>(e,schema,context,manifest,sharing,i,*boxes.back(),*stores.back(),*journals.back()));}
 CertifiedPhase previous{};
 for(unsigned round=0;round<2;++round){std::vector<LocalAccountCheckpoint::Prepared> prepared;Proposal r{Phase::Reserve,round+1,context,round?previous.proposal.digest(e):e.genesis,digest(round?"attempt2":"attempt1"),manifest,{}};
  for(unsigned i=0;i<5;++i){prepared.push_back(accounts[i]->persist(Phase::Reserve,r.slot,sections(fixtures,round,i)));r.bundles[i]=prepared.back().ciphertext();}
  std::vector<Vote> votes;for(unsigned i=0;i<5;++i)votes.push_back(accounts[i]->vote(prepared[i],r,round?&previous:nullptr));auto reserve=phase(r,votes);
  prepared.clear();auto c=r;c.phase=Phase::Commit;c.parent=r.digest(e);for(unsigned i=0;i<5;++i){prepared.push_back(accounts[i]->persist(Phase::Commit,c.slot,sections(fixtures,round,i)));c.bundles[i]=prepared.back().ciphertext();}
  votes.clear();for(unsigned i=0;i<5;++i)votes.push_back(accounts[i]->vote(prepared[i],c,&reserve));auto commit=phase(c,votes);
  auto a=c;a.phase=Phase::Acknowledge;a.parent=c.digest(e);votes.clear();for(unsigned i=0;i<5;++i)votes.push_back(accounts[i]->acknowledge(prepared[i],a,commit));auto ack=phase(a,votes);
  save(directory+"/reserve"+std::to_string(round),encode_phase(e,reserve));save(directory+"/commit"+std::to_string(round),encode_phase(e,commit));save(directory+"/ack"+std::to_string(round),encode_phase(e,ack));previous=ack;
 }
 ::_exit(0); // No destructor flushes: all durable work must already be complete.
 }catch(...){::_exit(3);}}
 int status=0;require(::waitpid(child,&status,0)==child&&WIFEXITED(status)&&WEXITSTATUS(status)==0,"fixture child checkpoint failed");
 std::vector<std::unique_ptr<Signer>> keys;std::vector<std::unique_ptr<OwnShareBox>> boxes;std::vector<std::unique_ptr<CiphertextStore>> stores;std::vector<std::unique_ptr<VoteJournal>> journals;std::vector<std::unique_ptr<LocalAccountCheckpoint>> accounts;std::vector<Status> statuses;auto challenge=digest("fresh-restart-challenge");
 for(unsigned i=0;i<5;++i){auto path=directory+"/party"+std::to_string(i);keys.push_back(std::make_unique<Signer>(signing_seed(i)));boxes.push_back(std::make_unique<OwnShareBox>(storage_key(i)));stores.push_back(std::make_unique<CiphertextStore>(path));journals.push_back(std::make_unique<VoteJournal>(path+"/journal",e,context,i,*keys.back()));accounts.push_back(std::make_unique<LocalAccountCheckpoint>(e,schema,context,manifest,sharing,i,*boxes.back(),*stores.back(),*journals.back()));statuses.push_back(journals.back()->status(challenge));}
 auto reserve=decode_phase(e,read(directory+"/reserve1")),commit=decode_phase(e,read(directory+"/commit1")),ack=decode_phase(e,read(directory+"/ack1")),oldAck=decode_phase(e,read(directory+"/ack0"));unsigned checks=0;
 for(unsigned i=0;i<5;++i){auto loaded=accounts[i]->load_committed(i,schema.bits(),oldAck.proposal.digest(e),reserve,commit,ack,challenge,statuses);auto actual=schema.unpack(std::move(loaded));auto expected=sections(fixtures,1,i);require(actual.size()==expected.size(),"fixture account section count");for(size_t j=0;j<actual.size();++j){require(actual[j].local_bytes().size()==expected[j].local_bytes().size()&&CRYPTO_memcmp(actual[j].local_bytes().data(),expected[j].local_bytes().data(),actual[j].local_bytes().size())==0,"fixture fullstate/outbox changed");++checks;}}
 bool rejected=false;try{auto r=decode_phase(e,read(directory+"/reserve0")),c=decode_phase(e,read(directory+"/commit0"));accounts[0]->load_committed(0,schema.bits(),e.genesis,r,c,oldAck,challenge,statuses);}catch(const std::runtime_error&){rejected=true;}require(rejected,"fixture stale account restored");++checks;
 auto tampered=encode_phase(e,commit);tampered.back()^=1;rejected=false;try{decode_phase(e,tampered);}catch(const std::runtime_error&){rejected=true;}require(rejected,"fixture altered certificate accepted");++checks;
 rejected=false;try{LocalAccountCheckpoint wrong(e,schema,context,manifest,sharing,1,*boxes[0],*stores[0],*journals[0]);}catch(const std::runtime_error&){rejected=true;}require(rejected,"fixture wrong journal owner");++checks;
 rejected=false;try{accounts[0]->load_committed(1,schema.bits(),oldAck.proposal.digest(e),reserve,commit,ack,challenge,statuses);}catch(const std::runtime_error&){rejected=true;}require(rejected,"fixture foreign member restore");++checks;
 rejected=false;try{auto changed=statuses;changed[0].challenge=digest("old challenge");changed[0].signature=keys[0]->sign(changed[0].message(e));accounts[0]->load_committed(0,schema.bits(),oldAck.proposal.digest(e),reserve,commit,ack,challenge,changed);}catch(const std::runtime_error&){rejected=true;}require(rejected,"fixture stale freshness challenge");++checks;
 rejected=false;try{auto shortened=encode_phase(e,ack);shortened.pop_back();decode_phase(e,shortened);}catch(const std::runtime_error&){rejected=true;}require(rejected,"fixture truncated certificate");++checks;
 std::cout<<checks<<" durable account-section/outbox checks passed\n";
}
