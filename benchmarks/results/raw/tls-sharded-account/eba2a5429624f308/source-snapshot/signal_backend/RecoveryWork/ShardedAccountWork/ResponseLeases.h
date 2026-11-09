#pragma once
#include "../EvidenceCodec.h"
namespace signal_mpc::recovery::sharded {
// Public opaque completion leases only; never private request IDs. Each install
// is bound to the actual signed Commit and fresh joint boot context.
class ResponseLeases {
 struct Pending {unsigned cell;uint64_t generation;Digest head,boot;};
 Epoch epoch_;Digest context_,manifest_,boot_;
 std::map<std::pair<size_t,uint64_t>,Pending> pending_;
 std::map<std::pair<size_t,unsigned>,uint64_t> generations_;
public:
 ResponseLeases(Epoch epoch,Digest context,Digest manifest,Digest boot):epoch_(epoch),context_(context),manifest_(manifest),boot_(boot){require(boot!=Digest{},"completion boot context absent");}
 void require_idle(size_t slot)const{for(auto& [key,value]:pending_)require(key.first!=slot,"conversation already pending");}
 void install(size_t slot,uint64_t ticket,unsigned cell,const CertifiedPhase& commit){require_idle(slot);require(ticket&&cell<4&&commit.proposal.phase==Phase::Commit&&commit.proposal.context==context_&&commit.proposal.manifest==manifest_&&certificate(epoch_,commit.proposal,commit.votes),"completion certified domain");
  auto generation=commit.proposal.slot;auto key=std::make_pair(slot,cell);require(generation>generations_[key],"completion reused generation");
  require(pending_.emplace(std::make_pair(slot,ticket),Pending{cell,generation,commit.proposal.digest(epoch_),boot_}).second,"completion lease collision");generations_[key]=generation;
 }
 unsigned complete(size_t slot,uint64_t ticket){auto found=pending_.find({slot,ticket});require(found!=pending_.end()&&found->second.boot==boot_&&found->second.head!=Digest{}&&generations_.at({slot,found->second.cell})==found->second.generation,"stale completion lease/generation");auto cell=found->second.cell;pending_.erase(found);return cell;}
 void clear()noexcept{pending_.clear();generations_.clear();}
};
}
