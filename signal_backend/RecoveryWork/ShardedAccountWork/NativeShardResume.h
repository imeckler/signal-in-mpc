#pragma once
#include "../NativeOwnShareArchive.h"
namespace signal_mpc::recovery::sharded {
class NativeShardResume {
public:
 using Bits=tls_mpc_worker::Bits;struct Pending{Bits computed_resumability,typed_payload,expected_id;};
 static Pending evaluate(unsigned ordinal,const Bits& queue,const Bits& dispositions,const Bits& generation,Bits validity,
 Machine<tls_mpc_worker::Share>& machine,tls_mpc_worker::Worker& worker,const tls_mpc_worker::PinnedPrograms& pinned){
  require(ordinal<4&&queue.size()==5240*8&&dispositions.size()==32&&generation.size()==64&&validity.size()==8,"shard resume dimensions");
  for(auto* part:std::array<const Bits*,3>{&queue,&dispositions,&generation})validity.insert(validity.end(),part->begin(),part->end());NativeOwnShareArchive::require_cells(validity);auto output=worker.allocate(1302*8);
  std::vector<FunctionArgument> args={{1,validity.function_argument()},{1,output.function_argument()}};auto name="signal_private_shard_resume_v1_o"+std::to_string(ordinal);pinned.verify_function(name,args);FunctionArgument ignored;machine.run_function(name,ignored,args);
  return{Bits(output.begin(),output.begin()+8),Bits(output.begin()+8,output.begin()+1294*8),Bits(output.begin()+1294*8,output.end())};
 }
};
}
