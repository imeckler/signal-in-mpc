#pragma once
#include "../NativeOwnShareArchive.h"
namespace signal_mpc::recovery::sharded {
class NativeShardRoute {
public:
 using Bits=tls_mpc_worker::Bits;
 struct Result{Bits validity,pending,blocked,typed_payload,expected_id;};
 static Result evaluate(unsigned ordinal,const Bits& queue,const Bits& dispositions,const Bits& generation,Bits validity,
 Machine<tls_mpc_worker::Share>& machine,tls_mpc_worker::Worker& worker,const tls_mpc_worker::PinnedPrograms& pinned){
  require(ordinal<4&&queue.size()==5240*8&&dispositions.size()==32&&generation.size()==64&&validity.size()==8,"shard routing dimensions");
  for(auto* part:std::array<const Bits*,3>{&queue,&dispositions,&generation})validity.insert(validity.end(),part->begin(),part->end());NativeOwnShareArchive::require_cells(validity);auto output=worker.allocate(1304*8);
  std::vector<FunctionArgument> args={{1,validity.function_argument()},{1,output.function_argument()}};auto name="signal_private_shard_route_v1_o"+std::to_string(ordinal);pinned.verify_function(name,args);FunctionArgument ignored;machine.run_function(name,ignored,args);
  return{Bits(output.begin(),output.begin()+8),Bits(output.begin()+8,output.begin()+16),Bits(output.begin()+16,output.begin()+24),Bits(output.begin()+24,output.begin()+1296*8),Bits(output.begin()+1296*8,output.end())};
 }
};
}
