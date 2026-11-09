#pragma once
#include "ShardDirectory.h"
#include "../AccountCheckpointCoordinator.h"
namespace signal_mpc::recovery::sharded {
// Caller starts from the fresh current head; returned generation is the last
// actual Commit changing this conversation, not its per-conversation send count.
inline std::optional<CertifiedPhase> latest_send(Directory& directory,AccountCheckpointCoordinator& coordinator,const CertifiedPhase& head,size_t slot,unsigned party){require(party<5&&slot<UINT64_MAX,"sharded provenance public bounds");auto commit=head;
  for(size_t count=0;count<1000000;++count){auto reserve=coordinator.ancestry_certificate(commit.proposal.parent);require(reserve.proposal.phase==Phase::Reserve&&reserve.proposal.slot==commit.proposal.slot&&reserve.proposal.attempt==commit.proposal.attempt,"sharded send ancestry");
   auto after=directory.lookup(commit.proposal.bundles[party],slot+1);auto before=directory.lookup(reserve.proposal.bundles[party],slot+1);require(bool(after)==bool(before),"sharded commit-only registration/deletion");if(!after)return std::nullopt;
   if(after->generation!=before->generation){require(before->generation!=UINT64_MAX&&after->generation==before->generation+1,"sharded send generation ancestry");return commit;}
   if(commit.proposal.slot==1)return std::nullopt;commit=coordinator.ancestry_certificate(reserve.proposal.parent);require(commit.proposal.phase==Phase::Commit&&commit.proposal.slot+1==reserve.proposal.slot,"sharded prior commit link");
  }throw std::runtime_error("sharded ancestry bound");
 }
}
