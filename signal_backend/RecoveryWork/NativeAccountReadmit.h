#pragma once
#include "NativeAccountAdmission.h"
#include "ImportV2Work/RawFieldReadmitV2.h"
#include "SessionWork/NativeLifecycle.h"
namespace signal_mpc::recovery {
// Full-schema checked import using the already tested partial-import lifecycle.
// Caller must first authorize/load the exact current certified ciphertext. This
// does not manufacture account provenance or interpret a private validity mask.
class NativeAccountReadmit {
 using Bits=tls_mpc_worker::Bits;
 struct Completion {size_t& count;~Completion(){++count;}};
 struct Helper {Completion completion;import_v2::RawFieldReadmitV2 input;Helper(size_t& count,Player& player):completion{count},input(player){}};
public:
 struct Imported {
  OwnedAccountV2 account;Bits computed_validity;uint64_t import_host,retirement_host;size_t helpers_destroyed;
 };
 static Imported run(AccountLayoutV2 layout,QuarantinedEvaluations raw,ShareDomain domain,
   Machine<tls_mpc_worker::Share>& machine,tls_mpc_worker::Worker& worker,
   const tls_mpc_worker::PinnedPrograms& pinned){
  using tls_mpc_worker::ErasedHostCall;
  require(!ErasedHostCall::active(),"account readmission must own both host barriers");
  require(domain.bit_count==layout.schema().bits()&&raw.bit_count()==domain.bit_count,"account readmission full schema dimensions");
  std::optional<OwnedAccountV2> account;Bits validity,flat;size_t destroyed=0;uint64_t imported=0,retired=0;
  bool success=ErasedHostCall::run([&]{imported=ErasedHostCall::generation();try{
   {Helper helper(destroyed,machine.get_player());
    flat.reserve(domain.bit_count);
    for(size_t offset=0;offset<domain.bit_count;offset+=4096){size_t count=std::min<size_t>(4096,domain.bit_count-offset);SecretBytes local(count*16);std::memcpy(local.data(),raw.local_bytes().data()+offset*16,count*16);auto block=domain;block.bit_count=count;
     auto values=helper.input.values_candidate(QuarantinedEvaluations(std::move(local)),block,worker);flat.insert(flat.end(),std::make_move_iterator(values.begin()),std::make_move_iterator(values.end()));}
   }
   require(destroyed==1,"account helper destruction incomplete");
   // Destroy authenticated raw local evaluations before any VM retirement.
   raw=QuarantinedEvaluations(SecretBytes(0));
   std::vector<Bits> sections;size_t at=0;
   auto take=[&](size_t bytes){size_t end=at+8*bytes;require(end<=flat.size(),"account section split bounds");sections.emplace_back(std::make_move_iterator(flat.begin()+at),std::make_move_iterator(flat.begin()+end));at=end;};
   for(unsigned tag=1;tag<=4;++tag)take(layout.global_width(tag));
   for(unsigned slot=0;slot<layout.conversations();++slot)for(unsigned tag=10;tag<=16;++tag)take(layout.conversation_width(tag));
   require(at==flat.size(),"account section split trailing cells");flat.clear();account.emplace(layout,std::move(sections));
   NativeAccountAdmission validator(machine,worker,pinned);validity=validator.evaluate(*account);
  }catch(...){flat.clear();account.reset();validity.clear();raw=QuarantinedEvaluations(SecretBytes(0));throw;}});
  require(success&&destroyed==1&&account&&ErasedHostCall::completed(imported),"account import/coherence host failed");
  // Existing actual validator initialized the VM; no empty anchor/retire(false).
  bool renewed=ErasedHostCall::run([&]{tls_mpc_worker::NativeLifecycle lifecycle(machine);lifecycle.renew_epoch();retired=ErasedHostCall::generation();require(!lifecycle.application_allowed(),"account epoch host barrier bypass");});
  require(renewed&&retired>imported&&ErasedHostCall::completed(retired),"account retirement host failed");
  return {std::move(*account),std::move(validity),imported,retired,destroyed};
 }
};
}
