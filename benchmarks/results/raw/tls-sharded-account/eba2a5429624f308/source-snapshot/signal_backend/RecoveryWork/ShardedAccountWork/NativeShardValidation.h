#pragma once
#include "../NativeOwnShareArchive.h"
namespace signal_mpc::recovery::sharded {
class NativeShardValidation {
public:
 using Bits=tls_mpc_worker::Bits;
 static Bits evaluate(bool conversation,Bits global,const Bits& body,
  Machine<tls_mpc_worker::Share>& machine,tls_mpc_worker::Worker& worker,const tls_mpc_worker::PinnedPrograms& pinned){
  require(global.size()==8306*8&&body.size()==(conversation?12611*8:0),"shard validation dimensions");
  global.insert(global.end(),body.begin(),body.end());NativeOwnShareArchive::require_cells(global);auto output=worker.allocate(8);
  std::vector<FunctionArgument> args={{1,global.function_argument()},{1,output.function_argument()}};
  auto name=std::string("signal_private_shard_validate_v1_")+(conversation?"conversation":"global");pinned.verify_function(name,args);FunctionArgument ignored;machine.run_function(name,ignored,args);return output;
 }
 static Digest program_identity(bool conversation,const Digest& manifest){auto bytes=label("SIGNAL-SHARD-VALIDATOR-PINNED-V1");append(bytes,manifest);auto name=label(conversation?"signal_private_shard_validate_v1_conversation-sbv:[167336x1]-sbv:[8x1]":"signal_private_shard_validate_v1_global-sbv:[66448x1]-sbv:[8x1]");bytes.insert(bytes.end(),name.begin(),name.end());return hash(bytes);}
};
}
