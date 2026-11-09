#include "ShardCheckpoint.h"
#include <filesystem>
#include <iostream>
using namespace signal_mpc::recovery;using namespace signal_mpc::recovery::sharded;
static unsigned checks=0;void check(bool x){require(x,"directory regression");++checks;}
template<class F>void rejects(F f){bool rejected=false;try{f();}catch(...){rejected=true;}check(rejected);}
int main(int argc,char**argv){require(argc==2,"test directory required");std::filesystem::create_directories(argv[1]);CiphertextStore nodes(argv[1]),bodies(argv[1]);auto domain=hash(label("PUBLIC-NEW-SHARDED-FIXTURE-NO-ACCOUNT-STATE"));Directory tree(nodes,domain);Digest root=tree.genesis();auto schema=hash(label("PUBLIC-SHARD-SCHEMA")),program=hash(label("PUBLIC-VALIDATOR-NOT-PRIVATE-MPC"));unsigned validations=0;auto validate=[&](const auto&,const Leaf&){++validations;return program;};auto cipher=bodies.put(Bytes(123,81));Leaf value{0,1,123,cipher,schema,{}};
 uint64_t two_read=0,two_write=0,large_read=0,large_write=0;Digest saved{};
 for(unsigned i=0;i<1000;++i){value.key=i;root=tree.replace(root,value,validate);if(i==1){auto before_read=tree.read_bytes,before_write=tree.written_bytes;auto change=value;change.key=0;change.generation=2;auto next=tree.replace(root,change,validate);two_read=tree.read_bytes-before_read;two_write=tree.written_bytes-before_write;check(tree.lookup(root,0)->generation==1);check(tree.lookup(next,0)->generation==2);saved=root;}}
 auto before_read=tree.read_bytes,before_write=tree.written_bytes;value.key=0;value.generation=2;auto next=tree.replace(root,value,validate);large_read=tree.read_bytes-before_read;large_write=tree.written_bytes-before_write;
 check(two_write==large_write);check(two_read==large_read);check(tree.lookup(next,999)->ciphertext==cipher);check(tree.lookup(root,0)->generation==1);check(tree.lookup(next,0)->generation==2);check(tree.lookup(saved,1)->generation==1);check(!tree.lookup(saved,999));
 rejects([&]{tree.replace(next,value,validate);});value.generation=3;rejects([&]{tree.replace(next,value,[](auto&,auto&){return Digest{};});});Directory other(nodes,hash(label("OTHER-DOMAIN")));rejects([&]{other.lookup(next,0);});rejects([&]{nodes.get(next,1);});
 // Actual durable journals/signatures, full lineage and changed-shard adapter.
 Epoch epoch{};epoch.number=1;epoch.genesis=hash(label("FRESH-SHARD-GENESIS"));std::vector<std::unique_ptr<Signer>> signers;
 for(unsigned i=0;i<5;++i){Digest seed{};seed.fill(i+42);signers.push_back(std::make_unique<Signer>(seed));epoch.members[i]=signers.back()->public_key();}
 auto context=hash(label("FRESH-SHARD-CONTEXT")),manifest=hash(label("PUBLIC-NOT-NATIVE-PROGRAM"));VoteJournal journal(std::string(argv[1])+"/journal",epoch,context,0,*signers[0]);Directory fresh(nodes,hash(label("CHECKPOINT-DIRECTORY")));Checkpoint local(fresh,bodies,journal,epoch,context,manifest,0);
 auto certify=[&](Phase phase,uint64_t slot,const CertifiedPhase* parent){value.key=7;value.generation=(slot-1)*2+(phase==Phase::Reserve?1:2);local.stage({value},validate);auto digest=local.persist(phase,slot);Proposal proposal{phase,slot,context,parent?parent->proposal.digest(epoch):epoch.genesis,hash(label("ATTEMPT")),manifest,{}};proposal.bundles.fill(digest);std::vector<Vote> votes;votes.push_back(local.vote(proposal,parent));for(unsigned i=1;i<5;++i)votes.push_back({i,signers[i]->sign(proposal.encode(epoch))});CertifiedPhase cert{proposal,votes};check(certificate(epoch,proposal,votes));return cert;};
 auto reserve=certify(Phase::Reserve,1,nullptr);auto commit=certify(Phase::Commit,1,&reserve);check(journal.count()==2);Checkpoint restart(fresh,bodies,journal,epoch,context,manifest,0);restart.restore_root(commit);check(restart.root()==commit.proposal.bundles[0]);
 // A stale generation or missing ciphertext fails before journal voting.
 auto count=journal.count();value.generation=1;restart.stage({value},validate);rejects([&]{restart.persist(Phase::Reserve,2);});check(restart.failed()&&journal.count()==count);
 std::cout<<"{\"passed\":true,\"checks\":"<<checks<<",\"two_slots\":{\"directory_read_bytes\":"<<two_read<<",\"directory_write_bytes\":"<<two_write<<"},\"thousand_slots\":{\"directory_read_bytes\":"<<large_read<<",\"directory_write_bytes\":"<<large_write<<"},\"changed_ciphertext_bytes\":123,\"private_semantic_validation\":false,\"actual_journal\":true}\n";
}
