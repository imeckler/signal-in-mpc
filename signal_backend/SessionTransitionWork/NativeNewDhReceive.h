#pragma once
#include "NativeWorker.h"
#include "NativeComputedDh.h"
namespace signal_mpc {
// Internal candidate: retained state525 || incoming identity32 || local identity32
// || validity/BE16-length/wire-cap256. Output computed validity1 || selected
// state525 || private plaintext BE16-length/cap80. All arrays remain shared.
// The embedding must persist the selected state, retire old computation traces,
// and keep the application result gated. This is not a full SessionRecord store.
class NativeNewDhReceive {
 Machine<tls_mpc_worker::Share>& machine_;
 tls_mpc_worker::Worker& allocation_;
 const tls_mpc_worker::PinnedPrograms& pinned_;
public:
 NativeNewDhReceive(Machine<tls_mpc_worker::Share>& machine,
  tls_mpc_worker::Worker& allocation,const tls_mpc_worker::PinnedPrograms& pinned)
  :machine_(machine),allocation_(allocation),pinned_(pinned){}
 tls_mpc_worker::Bits evaluate(tls_mpc_worker::Bits input){
  if(input.size()!=6784)throw std::runtime_error("private new-DH receive dimensions");
  // These slices are host-owned share copies, never reconstructed bytes.
  auto slice=[](const tls_mpc_worker::Bits& bits,size_t offset,size_t count){
   if(offset>bits.size()/8||count>bits.size()/8-offset)throw std::runtime_error("receive share slice");
   return tls_mpc_worker::Bits(bits.begin()+offset*8,bits.begin()+(offset+count)*8);
  };
  auto append=[](auto& target,const auto& source){target.insert(target.end(),source.begin(),source.end());};
  auto run=[&](const std::string& name,tls_mpc_worker::Bits argument,size_t output_bits){
   auto result=allocation_.allocate(output_bits);
   std::vector<FunctionArgument> args={{1,argument.function_argument()},{1,result.function_argument()}};
   pinned_.verify_function(name,args);FunctionArgument ignored;machine_.run_function(name,ignored,args);return result;
  };
  auto wire=slice(input,589,259);
  auto summary=run("signal_private_new_dh_summary_256_5",wire,600);
  auto dh_input=slice(input,32,32);append(dh_input,slice(summary,1,32));
  NativeComputedDh dh(machine_,allocation_,pinned_);
  auto computed=dh.prepare(std::move(dh_input));
  auto bound=slice(input,0,589);append(bound,computed);append(bound,wire);append(bound,summary);
  if(bound.size()!=8408)throw std::runtime_error("receive bound share dimensions");
  return run("signal_private_new_dh_crypto_256_5",std::move(bound),4864);
 }
};
}
