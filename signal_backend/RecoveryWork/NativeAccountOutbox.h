#pragma once
#include "AccountLayoutV2.h"
namespace signal_mpc::recovery {
class NativeAccountOutbox {
public:
 using Bits=tls_mpc_worker::Bits;
 struct Pending {Bits computed_resumability,typed_payload,expected_id;};
 static Pending evaluate(const OwnedAccountV2& account,size_t slot,size_t ordinal,Bits computed_account_validity,
   Machine<tls_mpc_worker::Share>& machine,tls_mpc_worker::Worker& worker,const tls_mpc_worker::PinnedPrograms& pinned){
  require(ordinal<4&&computed_account_validity.size()==8,"account outbox policy profile");
  auto input=std::move(computed_account_validity);auto& queue=account.conversation(slot,15);auto& dispositions=account.conversation(slot,16);input.insert(input.end(),queue.begin(),queue.end());input.insert(input.end(),dispositions.begin(),dispositions.end());NativeOwnShareArchive::require_cells(input);auto output=worker.allocate(1302*8);
  std::vector<FunctionArgument> args={{1,input.function_argument()},{1,output.function_argument()}};auto name="signal_private_account_outbox_v1_o"+std::to_string(ordinal);pinned.verify_function(name,args);FunctionArgument ignored;machine.run_function(name,ignored,args);
  return {Bits(output.begin(),output.begin()+8),Bits(output.begin()+8,output.begin()+1294*8),Bits(output.begin()+1294*8,output.end())};
 }
};
}
