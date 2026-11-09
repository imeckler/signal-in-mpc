#pragma once
// Internal candidate. Fixed pinned function only; no raw DH, public input import,
// opening, RPC registration or provider admission. Compile/proof still pending.
#include "NativeWorker.h"
#include "../VariableServiceWork/VariableShape.h"
namespace signal_mpc::recovery {
class NativeRecordBinding {
 using Bits=tls_mpc_worker::Bits;
 Machine<tls_mpc_worker::Share>& machine_;tls_mpc_worker::Worker& allocation_;const tls_mpc_worker::PinnedPrograms& pinned_;
 static Bits slice(const Bits& b,size_t offset,size_t count){if(b.size()%8||offset>b.size()/8||count>b.size()/8-offset)throw std::runtime_error("record binding slice");return Bits(b.begin()+offset*8,b.begin()+(offset+count)*8);}
 static void append(Bits& target,const Bits& source){target.insert(target.end(),source.begin(),source.end());}
public:
 static constexpr size_t snapshot_bytes=5550,service_input_bytes=611,producer_prefix_bytes=81;
 struct Bound {Bits service_result,selected_state,snapshot;};
 NativeRecordBinding(Machine<tls_mpc_worker::Share>& machine,tls_mpc_worker::Worker& allocation,const tls_mpc_worker::PinnedPrograms& pinned):machine_(machine),allocation_(allocation),pinned_(pinned){}
 bool same_domain(const NativeRecordBinding& other)const{return &machine_==&other.machine_ && &allocation_==&other.allocation_ && &pinned_==&other.pinned_;}
 Bound apply(Bits snapshot,const VariableShape& shape,Bits actual_call,Bits actual_service_result){
  if(snapshot.size()!=8*snapshot_bytes||actual_call.size()!=8*service_input_bytes||shape.certificate_bytes()!=260||shape.plaintext_bytes()!=80||shape.chunk_bytes()!=0||shape.address_bytes()!=0||actual_service_result.size()!=shape.output_bytes()*8)throw std::runtime_error("record binding dimensions/profile");
  append(snapshot,actual_call);append(snapshot,slice(actual_service_result,0,81));auto output=allocation_.allocate(8*(81+525+5550));
  std::vector<FunctionArgument> args={{1,snapshot.function_argument()},{1,output.function_argument()}};
  pinned_.verify_function("signal_private_record_bind_v1",args);FunctionArgument ignored;machine_.run_function("signal_private_record_bind_v1",ignored,args);
  auto prefix=slice(output,0,81);std::copy(prefix.begin(),prefix.end(),actual_service_result.begin());
  // Remaining ciphertext stays shared. Computed status0 must reach TLS's
  // authenticated terminal gate before any wire can be reconstructed.
  return{std::move(actual_service_result),slice(output,81,525),slice(output,606,5550)};
 }
};
}
