#pragma once
#include "NativeWorker.h"
namespace signal_mpc {
// Embedding-only unopened UTF8 text input. Caller admits the builder-computed
// validity, payload(kind||80) and identical timestamp into the normal registry.
// Never replace the returned validity with a supplied success constant.
class NativeTextNotification {
 Machine<tls_mpc_worker::Share>& machine_;tls_mpc_worker::Worker& allocation_;
 const tls_mpc_worker::PinnedPrograms& pinned_;
public:
 NativeTextNotification(Machine<tls_mpc_worker::Share>& machine,tls_mpc_worker::Worker& allocation,
  const tls_mpc_worker::PinnedPrograms& pinned):machine_(machine),allocation_(allocation),pinned_(pinned){}
 tls_mpc_worker::Bits evaluate(tls_mpc_worker::Bits input){
  if(input.size()!=472)throw std::runtime_error("text notification input size mismatch");
  auto output=allocation_.allocate(720);
  std::vector<FunctionArgument> args={{1,input.function_argument()},{1,output.function_argument()}};
  const std::string name="signal_private_text_notification_48_80";
  pinned_.verify_function(name,args);FunctionArgument ignored;machine_.run_function(name,ignored,args);return output;
 }
};
}
