#pragma once
#include "../NativeOwnShareArchive.h"
namespace signal_mpc::recovery::sharded {
class NativeReusableOutbox {
public:
 using Bits=tls_mpc_worker::Bits;
 struct Result {Bits computed_validity,queue,dispositions;};
 static Result replace(unsigned ordinal,Bits computed_upstream_validity,const Bits& queue,const Bits& dispositions,
  Bits actual_new_cell,const Bits& expected_public_certificate_generation,
  Machine<tls_mpc_worker::Share>& machine,tls_mpc_worker::Worker& worker,const tls_mpc_worker::PinnedPrograms& pinned){
  require(ordinal<4&&computed_upstream_validity.size()==8&&queue.size()==5240*8&&dispositions.size()==32&&actual_new_cell.size()==1310*8&&expected_public_certificate_generation.size()==64,"reusable outbox dimensions");
  auto input=std::move(computed_upstream_validity);for(auto* bytes:std::array<const Bits*,4>{&queue,&dispositions,&actual_new_cell,&expected_public_certificate_generation})input.insert(input.end(),bytes->begin(),bytes->end());NativeOwnShareArchive::require_cells(input);
  auto output=worker.allocate(5245*8);std::vector<FunctionArgument> args={{1,input.function_argument()},{1,output.function_argument()}};
  auto name="signal_private_reusable_outbox_v1_o"+std::to_string(ordinal);pinned.verify_function(name,args);FunctionArgument ignored;machine.run_function(name,ignored,args);
  return{Bits(output.begin(),output.begin()+8),Bits(output.begin()+8,output.begin()+5241*8),Bits(output.begin()+5241*8,output.end())};
 }
};
}
