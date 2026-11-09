#include "ResponseLeases.h"
#include <iostream>
using namespace signal_mpc::recovery;using namespace signal_mpc::recovery::sharded;
int main(){Epoch epoch{};epoch.number=1;epoch.genesis=hash(label("NEW-LEASE-FIXTURE"));std::vector<std::unique_ptr<Signer>> keys;
 for(unsigned i=0;i<5;++i){Digest seed{};seed.fill(141+i);keys.push_back(std::make_unique<Signer>(seed));epoch.members[i]=keys.back()->public_key();}
 auto context=hash(label("CONTEXT")),manifest=hash(label("MANIFEST")),boot=hash(label("FRESH-JOINT-BOOT-FIXTURE"));ResponseLeases leases(epoch,context,manifest,boot);unsigned checks=0;
 auto rejects=[&](auto action){bool rejected=false;try{action();}catch(...){rejected=true;}require(rejected,"lease regression");++checks;};
 auto commit=[&](uint64_t n){Proposal p{Phase::Commit,n,context,epoch.genesis,context,manifest,{}};CertifiedPhase c{p,{}};for(unsigned i=0;i<5;++i)c.votes.push_back({i,keys[i]->sign(p.encode(epoch))});return c;};
 for(uint64_t n=1;n<=12;++n){size_t slot=n%3==0?1:0;unsigned cell=(n-1)%4;uint64_t ticket=(uint64_t(1)<<63)+n;auto cert=commit(n);leases.install(slot,ticket,cell,cert);rejects([&]{leases.install(slot,ticket+90,(cell+1)%4,cert);});require(leases.complete(slot,ticket)==cell,"lease routing");++checks;rejects([&]{leases.complete(slot,ticket);});}
 // A repeated old ACK cannot acknowledge the new occupant of the reused cell.
 auto cert=commit(20);auto ticket=(uint64_t(1)<<63)+20;leases.install(0,ticket,0,cert);rejects([&]{leases.complete(0,(uint64_t(1)<<63)+1);});require(leases.complete(0,ticket)==0,"stale ACK consumed current occupant");++checks;
 rejects([&]{leases.install(0,ticket+1,0,commit(19));});auto bad=commit(21);bad.votes[0].signature[0]^=1;bad.votes[1].signature[0]^=1;rejects([&]{leases.install(0,ticket+2,0,bad);});ResponseLeases fresh(epoch,context,manifest,hash(label("NEXT-BOOT")));rejects([&]{fresh.complete(0,ticket);});std::cout<<"completion leases passed "<<checks<<" checks\n";
}
