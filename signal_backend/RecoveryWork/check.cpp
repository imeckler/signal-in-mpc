// PUBLIC DISPOSABLE member-key/evidence tests. No Signal/share import/restore.
#include "Evidence.h"
#include <filesystem>
#include <fstream>
#include <iostream>
#include <functional>
#include <sys/wait.h>
using namespace signal_mpc::recovery;
size_t checks=0;
void check(bool b){require(b,"recovery evidence check failed");++checks;}
void rejected(const std::function<void()>& f){try{f();}catch(const std::exception&){++checks;return;}throw std::runtime_error("recovery rejection missing");}
int main(){try{
 char temporary[]="/tmp/signal-recovery-evidence-XXXXXX";auto path=::mkdtemp(temporary);require(path,"fixture directory failed");std::filesystem::path dir(path);
 struct Remove{std::filesystem::path p;~Remove(){std::filesystem::remove_all(p);}}remove{dir};
 std::array<std::unique_ptr<Signer>,5> keys;Epoch epoch{};epoch.number=7;epoch.genesis.fill(11);
 for(unsigned i=0;i<5;++i){Digest seed;seed.fill(i+1);keys[i]=std::make_unique<Signer>(seed);epoch.members[i]=keys[i]->public_key();}
 Digest context;context.fill(13);Proposal proposal{};proposal.phase=Phase::Commit;proposal.slot=1;proposal.context=context;proposal.parent=epoch.genesis;proposal.attempt.fill(14);proposal.manifest.fill(15);
 for(unsigned i=0;i<5;++i)proposal.bundles[i].fill(i+20);
 std::vector<Vote> votes;
 for(unsigned i=0;i<5;++i){
  auto file=(dir/(std::to_string(i)+".journal")).string();Vote first;
  {VoteJournal journal(file,epoch,context,i,*keys[i]);first=journal.vote(proposal);check(journal.count()==1);check(journal.vote(proposal).signature==first.signature);}
  {VoteJournal journal(file,epoch,context,i,*keys[i]);check(journal.count()==1);check(journal.vote(proposal).signature==first.signature);}
  votes.push_back(first);
 }
 check(certificate(epoch,proposal,votes));
 // Every4of5 quorum accepted; every≤3 distinct subset rejected.
 for(unsigned mask=0;mask<32;++mask){std::vector<Vote> selected;for(unsigned i=0;i<5;++i)if(mask&(1u<<i))selected.push_back(votes[i]);check(certificate(epoch,proposal,selected)==(__builtin_popcount(mask)>=4));}
 auto duplicates=votes;duplicates[4]=duplicates[0];check(!certificate(epoch,proposal,duplicates));
 auto corrupted=votes;corrupted[0].signature[8]^=1;check(!certificate(epoch,proposal,corrupted));
 auto wrong_id=votes;wrong_id[0].party=5;check(!certificate(epoch,proposal,wrong_id));
 auto changed=proposal;changed.attempt[0]^=1;check(!certificate(epoch,changed,votes));
 changed=proposal;changed.phase=Phase::Reserve;check(!certificate(epoch,changed,votes));
 changed=proposal;changed.bundles[4][0]^=1;check(!certificate(epoch,changed,votes));
 auto other=epoch;other.number++;check(!certificate(other,proposal,votes));
 other=epoch;other.members[3]=other.members[4];rejected([&]{certificate(other,proposal,votes);});
 // A conflicting vote is refused after an actual close/reopen. The instance
 // then poisons, so callers cannot continue after a failed persistence action.
 {VoteJournal journal((dir/"0.journal").string(),epoch,context,0,*keys[0]);changed=proposal;changed.manifest[0]^=1;
  rejected([&]{journal.vote(changed);});rejected([&]{journal.vote(proposal);});}
 {VoteJournal journal((dir/"0.journal").string(),epoch,context,0,*keys[0]);check(journal.vote(proposal).signature==votes[0].signature);}
 // Actual process exit without C++ cleanup after durable voting, then reopen.
 auto reserved=proposal;reserved.phase=Phase::Reserve;reserved.slot=2;reserved.attempt.fill(77);
 auto child=::fork();require(child>=0,"fixture fork failed");
 if(child==0){try{VoteJournal journal((dir/"0.journal").string(),epoch,context,0,*keys[0]);journal.vote(reserved);::_exit(0);}catch(...){::_exit(1);}}
 int child_status=0;check(::waitpid(child,&child_status,0)==child&&WIFEXITED(child_status)&&WEXITSTATUS(child_status)==0);
 {VoteJournal journal((dir/"0.journal").string(),epoch,context,0,*keys[0]);check(journal.count()==2);
  Digest challenge;challenge.fill(98);auto status=journal.status(challenge);check(status.highest_slot==2);check(verify_status(epoch,context,challenge,status));
  auto wrong=challenge;wrong[0]^=1;check(!verify_status(epoch,context,wrong,status));status.highest_slot=1;check(!verify_status(epoch,context,challenge,status));
  check(journal.vote(reserved).signature==keys[0]->sign(reserved.encode(epoch)));
  auto conflict=reserved;conflict.bundles[0][0]^=1;rejected([&]{journal.vote(conflict);});rejected([&]{journal.status(challenge);});
 }
 // Full signer-set intersection check for every2fault assignment. No3of5 safety claim.
 for(unsigned a=0;a<32;++a)for(unsigned b=0;b<32;++b)for(unsigned bad=0;bad<32;++bad)
  if(__builtin_popcount(a)>=4&&__builtin_popcount(b)>=4&&__builtin_popcount(bad)<=2)check((a&b&~bad&31)!=0);
 check((7u&28u&~4u&31)==0); // Two3-member sets can intersect only at corrupt member2.
 auto original=dir/"1.journal";
 std::filesystem::copy_file(original,dir/"torn.journal");std::filesystem::resize_file(dir/"torn.journal",std::filesystem::file_size(original)-1);
 rejected([&]{VoteJournal j((dir/"torn.journal").string(),epoch,context,1,*keys[1]);});
 std::filesystem::copy_file(original,dir/"altered.journal");{std::fstream f(dir/"altered.journal",std::ios::in|std::ios::out|std::ios::binary);f.seekg(-10,std::ios::end);char c;f.read(&c,1);c^=1;f.seekp(-10,std::ios::end);f.write(&c,1);}
 rejected([&]{VoteJournal j((dir/"altered.journal").string(),epoch,context,1,*keys[1]);});
 rejected([&]{VoteJournal j(original.string(),epoch,context,0,*keys[0]);});
 std::filesystem::create_symlink(original,dir/"symlink.journal");rejected([&]{VoteJournal j((dir/"symlink.journal").string(),epoch,context,1,*keys[1]);});
 {VoteJournal held(original.string(),epoch,context,1,*keys[1]);rejected([&]{VoteJournal j(original.string(),epoch,context,1,*keys[1]);});}
 std::cout<<checks<<" recovery signature/journal/intersection checks passed\n";return 0;
 }catch(const std::exception& e){std::cerr<<e.what()<<'\n';return 1;}}
