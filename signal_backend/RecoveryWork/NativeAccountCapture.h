#pragma once
#include "LocalAccountCheckpoint.h"
#include "NativeOwnShareArchive.h"
#include "SessionWork/ErasedHostCall.h"
#include <functional>
namespace signal_mpc::recovery {
// Concrete native full-schema capture. It copies LOCAL evaluations only;
// plaintext account bytes and interpolated keys never exist here.
class NativeAccountCapture {
 LocalAccountCheckpoint& checkpoint_;uint64_t bits_;unsigned party_;
 std::function<Player&()> player_;
public:
 NativeAccountCapture(LocalAccountCheckpoint& checkpoint,const AccountSchemaV1& schema,unsigned party,std::function<Player&()> player)
 :checkpoint_(checkpoint),bits_(schema.bits()),party_(party),player_(std::move(player)){require(party<5&&bool(player_),"native account capture configuration");}
 LocalAccountCheckpoint::Prepared persist(Phase phase,uint64_t slot,const std::vector<const tls_mpc_worker::Bits*>& sections){
  require(tls_mpc_worker::ErasedHostCall::active(),"native account capture requires erased host call");auto& player=player_();
  require(player.num_players()==5&&unsigned(player.my_num())==party_&&ShamirOptions::s().threshold==2&&gf2n_long::degree()==128,"native account capture runtime domain");
  require(sections.size()>=11&&sections.size()<=4+7*64,"native account section count");uint64_t total=0;
  for(auto* section:sections){require(section&&section->size()>0&&section->size()<=bits_-total,"native account section capacity");NativeOwnShareArchive::require_cells(*section);total+=section->size();}
  require(total==bits_,"native account total capacity");
  std::vector<QuarantinedEvaluations> local;local.reserve(sections.size());
  for(auto* section:sections){SecretBytes bytes(section->size()*16);
   for(size_t i=0;i<section->size();++i)detail::encode_own_evaluation(bytes.data()+16*i,static_cast<const gf2n_long&>((*section)[i][0].get_regs()[0]));
   local.emplace_back(std::move(bytes));
  }
  // Actual schema pack enforces every section's width/order before encryption.
  auto prepared=checkpoint_.persist(phase,slot,std::move(local));require(prepared.domain().party==party_,"native account checkpoint owner mismatch");return prepared;
 }
};
}
