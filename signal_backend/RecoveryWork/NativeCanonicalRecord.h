#pragma once
// Internal candidate only. No RPC entrypoint, public share import, opens or
// provider activation. Actual receive/service outputs stay move-owned shares.
#include "NativeWorker.h"
#include "../VariableServiceWork/VariableShape.h"
namespace signal_mpc::recovery {
class NativeCanonicalRecord {
 Machine<tls_mpc_worker::Share>& machine_;tls_mpc_worker::Worker& allocation_;const tls_mpc_worker::PinnedPrograms& pinned_;
 using Bits=tls_mpc_worker::Bits;
 static Bits slice(const Bits& b,size_t offset,size_t bytes){
  if(b.size()%8||offset>b.size()/8||bytes>b.size()/8-offset)throw std::runtime_error("canonical record slice");
  return Bits(b.begin()+offset*8,b.begin()+(offset+bytes)*8);
 }
 static void append(Bits& to,const Bits& from){to.insert(to.end(),from.begin(),from.end());}
public:
 static constexpr size_t snapshot_bytes=5550,selected_bytes=525;
 struct Selected {Bits status,selected,snapshot;};
 NativeCanonicalRecord(Machine<tls_mpc_worker::Share>& machine,tls_mpc_worker::Worker& allocation,const tls_mpc_worker::PinnedPrograms& pinned)
 :machine_(machine),allocation_(allocation),pinned_(pinned){}
private:
 Selected run(const std::string& mode,Bits snapshot,Bits prefix){
  const auto n=mode=="send"?81u:608u;
  if(snapshot.size()!=snapshot_bytes*8||prefix.size()!=n*8)throw std::runtime_error("canonical record input dimensions");
  append(snapshot,prefix);auto output=allocation_.allocate(8*(1+selected_bytes+snapshot_bytes));
  std::vector<FunctionArgument> args={{1,snapshot.function_argument()},{1,output.function_argument()}};
  const auto name="signal_private_record_"+mode+"_v1";pinned_.verify_function(name,args);FunctionArgument ignored;machine_.run_function(name,ignored,args);
  return{slice(output,0,1),slice(output,1,selected_bytes),slice(output,1+selected_bytes,snapshot_bytes)};
 }
public:
 Selected apply_receive(Bits snapshot,Bits actual_receive){return run("receive",std::move(snapshot),std::move(actual_receive));}
 Selected apply_send(Bits snapshot,const VariableShape& shape,Bits actual_service){
  if(shape.certificate_bytes()!=260||shape.plaintext_bytes()!=80||shape.chunk_bytes()!=0||shape.address_bytes()!=0||actual_service.size()!=8*shape.output_bytes())throw std::runtime_error("canonical record service profile");
  return run("send",std::move(snapshot),slice(actual_service,0,81));
 }
};
}
