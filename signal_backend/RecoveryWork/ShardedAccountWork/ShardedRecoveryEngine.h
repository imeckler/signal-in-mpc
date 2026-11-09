#pragma once
#include "ShardPersistence.h"
#include "SendProvenance.h"
#include "ShardedDurableOwner.h"
#include "NativeShardReadmit.h"
#include "../AccountAdmission.h"
namespace signal_mpc::recovery::sharded {
// Active-working-set candidate. Idle, pending and rejected-blocked routing is
// explicitly disclosed only after complete authenticated private validation.
class Engine {
 using Bits=tls_mpc_worker::Bits;using Session=tls_mpc_worker::Session;using Collective=tls_mpc_worker::Collective;
 static Bits copy(const Bits& b){return{b.begin(),b.end()};}
 static Bits slice(const Bits& b,size_t offset,size_t size){require((offset+size)*8<=b.size(),"sharded engine slice");return{b.begin()+offset*8,b.begin()+(offset+size)*8};}
 static std::string hex(const Digest& d){std::string s;for(auto b:d){s+="0123456789abcdef"[b>>4];s+="0123456789abcdef"[b&15];}return s;}

public:
 struct Config {
  std::unique_ptr<Persistence::Config> persistence;std::vector<size_t> active_slots;
  std::function<std::vector<std::unique_ptr<tls_mpc_worker::PrivateInputBuilder>>(size_t,Session&,Collective&,unsigned)> inputs;
  Config():persistence(std::make_unique<Persistence::Config>()){}
 };
 struct Recovered {std::shared_ptr<Persistence> persistence;std::unique_ptr<Config> config;std::optional<NativeShardReadmit::Imported> imported;AccountCheckpointCoordinator::CurrentHead current;std::map<size_t,std::optional<CertifiedPhase>> sends;unsigned party;Digest head;};
 static std::unique_ptr<AuthorizedRestoredAccount> resolve(std::unique_ptr<Config> config,
  Machine<tls_mpc_worker::Share>& machine,tls_mpc_worker::Worker& worker,tls_mpc_worker::PinnedPrograms& pinned,Collective& collective,unsigned party){
  using tls_mpc_worker::ErasedHostCall;require(!ErasedHostCall::active()&&config&&config->persistence&&party<5,"sharded resolver context");
  std::shared_ptr<Persistence> persistence;std::optional<AccountCheckpointCoordinator::CurrentHead> current;std::vector<NativeShardReadmit::Raw> raw;std::map<size_t,std::optional<CertifiedPhase>> sends;
  bool loaded=ErasedHostCall::run([&]{bool ready=false;try{require(!config->active_slots.empty()&&config->active_slots.size()<=4,"sharded working set bounds");for(size_t i=0;i<config->active_slots.size();++i)require(config->active_slots[i]<UINT64_MAX&&(i==0||config->active_slots[i-1]<config->active_slots[i]),"sharded slot order");persistence=std::make_shared<Persistence>(std::move(config->persistence),machine,pinned,collective,party,true);ready=true;}catch(...){}collective.require_local_success(ready);require(ready,"sharded persistence setup failed");
   current.emplace(persistence->coordinator.recover_current());require(current->commit&&current->reservation,"sharded committed current head absent");auto head=current->commit->proposal.digest(persistence->epoch());auto inventory=label("SIGNAL-SHARDED-RECOVERY-WORKING-SET-V1");append(inventory,head);append(inventory,current->challenge);for(auto slot:config->active_slots)u64(inventory,slot);auto agreed=hash(inventory);collective.agree_program("sharded-active-working-set-v1",tls_mpc_worker::PublicBytes(agreed.begin(),agreed.end()));
   persistence->local.restore_root(*current->commit);
   // Resolve public provenance before local loads, so every party follows the
   // same ancestry network sequence even when one local shard is unavailable.
   for(auto slot:config->active_slots)sends.emplace(slot,latest_send(persistence->directory,persistence->coordinator,*current->commit,slot,party));
   ready=false;try{auto root=persistence->local.root();auto global=persistence->directory.lookup(root,0);require(bool(global),"sharded global unavailable");raw.push_back({0,persistence->capture.load_quarantined(*global,false),0});
    for(auto slot:config->active_slots){auto leaf=persistence->directory.lookup(root,slot+1);require(bool(leaf),"sharded conversation unavailable");raw.push_back({slot+1,persistence->capture.load_quarantined(*leaf,true),(sends.at(slot)?sends.at(slot)->proposal.slot:0)});}
    ready=true;
   }catch(...){raw.clear();}collective.require_local_success(ready);require(ready,"sharded authorized ciphertext load failed");
   // Bind the fresh input transcript separately from the authenticated archive.
   for(auto& item:raw){auto domain=label("SIGNAL-SHARDED-CHECKED-READMIT-V1");append(domain,head);append(domain,current->challenge);u64(domain,item.key);u64(domain,item.quarantine.archive_domain.slot);append(domain,item.quarantine.archive_domain.schema);item.quarantine.archive_domain.schema=hash(domain);}
  });
  require(loaded&&persistence&&current&&raw.size()==config->active_slots.size()+1,"sharded authorized load failed");auto imported=NativeShardReadmit::run(std::move(raw),machine,worker,pinned);require(imported.helpers_destroyed==1&&imported.conversations.size()==config->active_slots.size(),"sharded readmit completion prerequisites");
  auto state=std::make_shared<Recovered>();state->persistence=persistence;state->config=std::move(config);state->current=std::move(*current);state->sends=std::move(sends);state->party=party;state->head=state->current.commit->proposal.digest(persistence->epoch());auto imported_host=imported.import_host,retired_host=imported.retirement_host;state->imported.emplace(std::move(imported));
  auto build=[state](Session& session,Collective& fresh,unsigned who){require(who==state->party&&state->imported,"sharded authorization consumed");auto& p=*state->persistence;auto validity=copy(state->imported->validity);auto pending=std::move(state->imported->pending);auto routing=std::move(state->imported->routing);
   auto owner=std::shared_ptr<DurableOwner>(new DurableOwner(DurableOwner::RestoreTag{},state->persistence,p.coordinator,p.local,p.directory,p.capture,session,p.epoch(),p.config().context,p.manifest(),state->current.challenge,std::move(state->imported->global),std::move(state->imported->conversations),state->current,who));state->imported.reset();
   tls_mpc_worker::MuxProviderAdmission admission;admission.restored_account=true;admission.credentials=slice(owner->global(),0,38);admission.computed_credential_validity=copy(validity);admission.restored_request_cursor=slice(owner->global(),8298,8);admission.computed_cursor_validity=copy(validity);
   std::vector<uint64_t> leases;
   for(auto slot:state->config->active_slots){auto send=state->sends.at(slot);auto route=routing.at(slot);std::cerr<<"SHARDED_ROUTE slot="<<slot<<" route="<<(route==2?"blocked":route==1?"pending":"idle")<<"\n";uint64_t lease=0;unsigned ordinal=0;
    if(route==1){require(bool(send),"pending outbox has no send provenance");ordinal=(send->proposal.slot-1)%4;auto material=label("SIGNAL-SHARDED-RESTORED-LEASE-V1");append(material,state->head);append(material,state->current.challenge);u64(material,slot);u64(material,ordinal);u64(material,send->proposal.slot);append(material,send->proposal.digest(p.epoch()));auto digest=hash(material);lease=read64(digest.data())|(uint64_t(1)<<63);require(std::find(leases.begin(),leases.end(),lease)==leases.end(),"sharded resume lease collision");leases.push_back(lease);owner->register_authorized_resume(slot,lease,ordinal,*send);}

    auto fence=p.config().directory+"/fence-"+hex(state->head)+"-"+hex(state->current.challenge)+"-"+std::to_string(slot);auto conversation=std::make_unique<tls_mpc_worker::NativeConversation>(session,fresh,VariableShape(260,80,false,false),slice(owner->conversation(slot),5619,611),fence,owner,slot);
    std::vector<std::unique_ptr<tls_mpc_worker::PrivateInputBuilder>> inputs;if(route!=2&&state->config->inputs)inputs=state->config->inputs(slot,session,fresh,who);tls_mpc_worker::ConversationAdmission row{std::move(conversation),copy(validity),std::move(inputs),{}};if(route==1){auto& saved=pending.at(slot);row.pending_outboxes.push_back({lease,std::move(saved.typed_payload),std::move(saved.expected_id),std::move(saved.computed_resumability),1290});}row.blocked=route==2;admission.conversations.push_back(std::move(row));
   }state->config->inputs={};return admission;
  };
  return std::unique_ptr<AuthorizedRestoredAccount>(new AuthorizedRestoredAccount(std::move(build),party,state->head,state->current.challenge,imported_host,retired_host));
 }
};
}
