#include "CertifiedArchiveGate.h"
#include <iostream>
using namespace signal_mpc::recovery;
int main(){
 std::array<std::unique_ptr<Signer>,5> keys;Epoch e{7,{},hash(label("genesis"))};
 for(unsigned i=0;i<5;++i){Digest seed{};seed[0]=i+1;keys[i]=std::make_unique<Signer>(seed);e.members[i]=keys[i]->public_key();}
 auto d=[](const char* x){return hash(label(x));};auto context=d("account"),manifest=d("programs"),schema=d("schema"),sharing=d("sharing"),challenge=d("fresh-challenge");
 auto certify=[&](Proposal p){CertifiedPhase c{p,{}};for(unsigned i=0;i<4;++i)c.votes.push_back({i,keys[i]->sign(p.encode(e))});return c;};
 Proposal p{Phase::Reserve,3,context,d("previous-ack"),d("attempt"),manifest,{}};
 for(unsigned i=0;i<5;++i)p.bundles[i]=d(("intent"+std::to_string(i)).c_str());auto reserve=certify(p);
 p.phase=Phase::Commit;p.parent=reserve.proposal.digest(e);for(unsigned i=0;i<5;++i)p.bundles[i]=d(("poststate-outbox"+std::to_string(i)).c_str());auto commit=certify(p);
 p.phase=Phase::Acknowledge;p.parent=commit.proposal.digest(e);auto ack=certify(p);
 std::vector<Status> statuses;for(unsigned i=0;i<4;++i){Status s{i,3,context,challenge,d("journal"),{}};s.signature=keys[i]->sign(s.message(e));statuses.push_back(s);}
 CertifiedArchiveGate gate(e,context,manifest,schema,sharing);unsigned checks=0;
 auto run=[&](auto r,auto c,auto a,auto ss,auto own,bool accepted){bool ok=false;try{auto x=gate.authorize(2,4096,reserve.proposal.parent,r,c,a,challenge,ss,own);ok=x.schema==schema&&x.sharing_epoch==sharing&&x.membership==e.digest()&&x.party==2&&x.slot==3;}catch(const std::runtime_error&){}require(ok==accepted,"phase regression");++checks;};
 auto own=commit.proposal.bundles[2];run(reserve,commit,ack,statuses,own,true);
 auto bad=commit;bad.proposal.parent=d("wrong-parent");bad=certify(bad.proposal);run(reserve,bad,ack,statuses,own,false);
 bad=reserve;bad.proposal.attempt=d("other-attempt");bad=certify(bad.proposal);run(bad,commit,ack,statuses,own,false);
 bad=ack;bad.proposal.bundles[2]=d("replacement");bad=certify(bad.proposal);run(reserve,commit,bad,statuses,own,false);
 bad=commit;bad.votes.pop_back();run(reserve,bad,ack,statuses,own,false);
 bad=commit;bad.votes[3]=bad.votes[0];run(reserve,bad,ack,statuses,own,false);
 run(reserve,commit,ack,statuses,d("other-ciphertext"),false);
 auto ss=statuses;ss[0].highest_slot=4;ss[0].signature=keys[0]->sign(ss[0].message(e));run(reserve,commit,ack,ss,own,false);
 ss=statuses;ss[0].challenge=d("old-challenge");ss[0].signature=keys[0]->sign(ss[0].message(e));run(reserve,commit,ack,ss,own,false);
 ss=statuses;ss[3]=ss[0];run(reserve,commit,ack,ss,own,false);
 ss=statuses;ss.pop_back();run(reserve,commit,ack,ss,own,false);
 bad=ack;bad.proposal.manifest=d("other-programs");bad=certify(bad.proposal);run(reserve,commit,bad,statuses,own,false);
 bad=reserve;bad.proposal.phase=Phase::Commit;bad=certify(bad.proposal);run(bad,commit,ack,statuses,own,false);
 std::cout<<checks<<" phase/domain checks passed\n";
}
