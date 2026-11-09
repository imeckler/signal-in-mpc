// PUBLIC fixture: actual full-layout capture/certificates/current-head network.
// No private Signal evaluation/import/provider activation is claimed here.
#include "../AccountCheckpointCoordinator.h"
#include "../AccountLayoutV2.h"
#include "LifecycleWork/SecureGmp.h"
#include <filesystem>
#include <fstream>
#include <iostream>
using namespace tls_mpc_worker;using namespace signal_mpc::recovery;
static Bytes decode(const std::string& text){Bytes out;for(size_t i=0;i<text.size();i+=2)out.push_back(std::stoul(text.substr(i,2),nullptr,16));return out;}
static Digest seed(unsigned party){Digest out;out.fill(party+17);return out;}
static Epoch epoch(){Epoch out{};out.number=1;out.genesis=signal_mpc::recovery::hash(label("PUBLIC-ACCOUNT-LEDGER-GENESIS-V2"));for(unsigned p=0;p<5;++p){Signer signer(seed(p));out.members[p]=signer.public_key();}return out;}
int main(int argc,char**argv){SecureGmp::install_before_threads();if(argc!=8)return 2;unsigned party=std::stoul(argv[1]);std::string mode=argv[7];bool passed=false;const char* stage="options";auto run=[&]{try{
 ShamirOptions::singleton={5,2};OnlineOptions opts;opts.playerno=party;opts.live_prep=true;opts.security_parameter=128;opts.lg2=128;opts.lgp=255;opts.prime=1;opts.prime<<=255;opts.prime-=19;
 stage="machine";Names names(party,std::stoul(argv[3]),std::string(argv[2]));Machine<tls_mpc_worker::Share> machine(names,true,opts);stage="pin";PinnedPrograms pinned(argv[4]);Collective collective(machine.get_player(),pinned.digest(),PublicBytes(32,75));
 stage="archive_setup";auto e=epoch();Digest context;context.fill(81);Digest manifest;std::copy_n(pinned.digest().begin(),32,manifest.begin());Digest sharing;sharing.fill(82);Signer signer(seed(party));
 auto dir=std::filesystem::path(argv[5])/std::to_string(party);std::filesystem::create_directories(dir/"shares");std::filesystem::create_directories(dir/"certificates");std::array<unsigned char,64> storage_key;for(size_t i=0;i<64;++i)storage_key[i]=i+party*7;OwnShareBox box(storage_key);CiphertextStore files((dir/"shares").string());PublicCheckpointStore certificates((dir/"certificates").string());VoteJournal journal((dir/"votes.journal").string(),e,context,party,signer);AccountLayoutV2 layout(2);auto schema=layout.schema();LocalAccountCheckpoint local(e,schema,context,manifest,sharing,layout.encoding(),party,box,files,journal);NativeAccountCapture capture(local,schema,party,[&]()->Player&{return machine.get_player();});AccountCheckpointCoordinator coordinator(e,context,manifest,party,capture,local,journal,certificates,collective,[&]()->Player&{return machine.get_player();});
 stage="fixture_read";std::ifstream input(argv[6]);std::string text;std::vector<std::vector<Bytes>> plain;
 for(unsigned state=0;state<5;++state){std::vector<Bytes> sections;for(unsigned i=0;i<18;++i){require(bool(input>>text),"account ledger fixture truncated");sections.push_back(decode(text));}plain.push_back(std::move(sections));}
 auto native=[&](unsigned index){std::vector<tls_mpc_worker::Bits> sections;for(auto& bytes:plain[index]){tls_mpc_worker::Bits bits;bits.reserve(bytes.size()*8);for(size_t i=0;i<bytes.size()*8;++i)bits.push_back(std::vector<tls_mpc_worker::Bit>{tls_mpc_worker::Bit::constant((bytes[i/8]>>(7-i%8))&1,party,machine.get_bit_mac_key(),1)});sections.push_back(std::move(bits));}return OwnedAccountV2(layout,std::move(sections));};
 if(mode=="reject"){
  bool rejected=false;try{coordinator.recover_current();}catch(const std::exception& error){rejected=std::string(error.what())=="account coordinator unresolved higher reservation/head";}require(rejected&&coordinator.failed(),"higher/stale head not rejected");passed=true;return;
 }
 stage="current_head";auto head=coordinator.recover_current();
 if(mode=="write"){
  require(!head.commit,"new account unexpectedly has head");stage="reserve_commit";auto reserve=native(1);auto commit=native(2);auto r1=coordinator.reserve(reserve.references());auto c1=coordinator.commit(commit.references());require(r1.proposal.slot==1&&c1.proposal.slot==1,"first slot wrong");reserve=native(3);commit=native(4);auto r2=coordinator.reserve(reserve.references());auto c2=coordinator.commit(commit.references());require(r2.proposal.slot==2&&c2.proposal.slot==2&&journal.count()==4,"second slot wrong");passed=true;
 }else if(mode=="reserve"){
  require(head.commit&&head.commit->proposal.slot==2,"reservation predecessor missing");auto state=native(4);require(coordinator.reserve(state.references()).proposal.slot==3,"higher reservation slot wrong");passed=true;
 }else if(mode=="read"){
  require(head.commit&&head.reservation&&head.commit->proposal.slot==2,"current signed head wrong");std::optional<QuarantinedEvaluations> restored;try{restored.emplace(local.load_committed(party,schema.bits(),head.reservation->proposal.parent,*head.reservation,*head.commit,head.challenge,head.statuses));}catch(...){}collective.require_local_success(bool(restored));require(bool(restored),"current snapshot missing");auto parts=schema.unpack(std::move(*restored));require(parts.size()==18,"restored full sections missing");
  for(size_t section=0;section<parts.size();++section){auto& expected=plain[4][section];require(parts[section].bit_count()==expected.size()*8,"restored section size");for(size_t bit=0;bit<expected.size()*8;++bit){auto* raw=parts[section].local_bytes().data()+16*bit;require(raw[0]==((expected[bit/8]>>(7-bit%8))&1),"restored fixture evaluation wrong");for(size_t i=1;i<16;++i)require(raw[i]==0,"restored fixture evaluation high bits wrong");}}
  require(plain[2][9]==plain[4][9]&&plain[2][10]==plain[4][10],"earlier unrelated outbox lost");passed=true;
 }else throw std::runtime_error("unknown ledger fixture mode");
 }catch(const std::exception& error){std::cerr<<"account ledger stage="<<stage<<" diagnostic="<<error.what()<<"\n";throw;} };
 bool cleaned=ErasedHostCall::run(run);if(passed&&cleaned){std::cout<<"ACCOUNT_LEDGER {\"passed\":true,\"mode\":\""<<mode<<"\",\"sections\":18,\"conversations\":2,\"quorum\":4,\"public_fixture_only\":true}\n";return 0;}std::cerr<<"account ledger category=phase\n";return 1;}
