#pragma once
// Internal pure coherence validator only. No provider/Session admission or RPC.
#include "NativeOwnShareArchive.h"
namespace signal_mpc::recovery {
class NativeRecordAdmission {
 Machine<tls_mpc_worker::Share>& machine_;tls_mpc_worker::Worker& worker_;const tls_mpc_worker::PinnedPrograms& pinned_;
public:
 static constexpr size_t input_bytes=6686;
 NativeRecordAdmission(Machine<tls_mpc_worker::Share>& machine,tls_mpc_worker::Worker& worker,const tls_mpc_worker::PinnedPrograms& pinned)
 :machine_(machine),worker_(worker),pinned_(pinned){}
 // snapshot5550 || selected525 || service611. All values remain OwnedBits.
 // This actual pinned function initializes the fresh Machine's VM owners;
 // it is not an uninitialized-epoch retirement bypass or supplied-validity API.
 tls_mpc_worker::Bits evaluate(tls_mpc_worker::Bits state){
  if(state.size()!=8*input_bytes)throw std::runtime_error("record admission dimensions");
  NativeOwnShareArchive::require_cells(state);auto valid=worker_.allocate(8);
  std::vector<FunctionArgument> args={{1,state.function_argument()},{1,valid.function_argument()}};
  pinned_.verify_function("signal_private_record_admit_v1",args);FunctionArgument ignored;machine_.run_function("signal_private_record_admit_v1",ignored,args);
  return valid; // Must propagate to the real account/provider gate; never open keys.
 }
};
}
