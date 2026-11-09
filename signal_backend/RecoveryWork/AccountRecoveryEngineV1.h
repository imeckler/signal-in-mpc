#pragma once
#include "AccountAdmission.h"
#include "NativeAccountReadmit.h"
#include "AccountDurableOwnerV1.h"
#include <filesystem>
namespace signal_mpc::recovery {
// Candidate c1 established-account engine. Trusted embedding supplies local
// archive/signing keys and their authenticated five-peer epoch mapping; there
// is no RPC/share/plaintext import. Full fresh/prekey/SPQR/skipped semantics and
// crash recovery of unresolved frozen reservations remain required work.
class AccountRecoveryEngineV1 {
 using Bits=tls_mpc_worker::Bits;using Session=tls_mpc_worker::Session;using Collective=tls_mpc_worker::Collective;
 static Bits copy(const Bits& value){return {value.begin(),value.end()};}
 static std::string hex(const Digest& digest){std::string text;const char* table="0123456789abcdef";for(auto byte:digest){text+=table[byte>>4];text+=table[byte&15];}return text;}
public:
 struct Config {
  Epoch epoch;Digest context,archive_sharing_domain,signing_seed;std::array<unsigned char,64> local_storage_key;
  std::string local_directory;
  // Embedding-only input builders. The normal RPC accepts opaque handles only.
  std::function<std::vector<std::unique_ptr<tls_mpc_worker::PrivateInputBuilder>>(Session&,Collective&,unsigned)> inputs;
  ~Config(){OPENSSL_cleanse(signing_seed.data(),signing_seed.size());OPENSSL_cleanse(local_storage_key.data(),local_storage_key.size());}
 };
private:
 struct Persistence {
  std::shared_ptr<Config> config;AccountLayoutV2 layout{1};Digest manifest;Signer signer;OwnShareBox box;CiphertextStore files;PublicCheckpointStore certificates;VoteJournal journal;LocalAccountCheckpoint checkpoint;NativeAccountCapture capture;AccountCheckpointCoordinator coordinator;
  Persistence(std::shared_ptr<Config> cfg,unsigned party,Machine<tls_mpc_worker::Share>& machine,const tls_mpc_worker::PinnedPrograms& pinned,Collective& collective)
  :config(std::move(cfg)),manifest{},signer(config->signing_seed),box(config->local_storage_key),files(config->local_directory+"/shares"),certificates(config->local_directory+"/certificates"),journal(config->local_directory+"/votes.journal",config->epoch,config->context,party,signer),checkpoint(config->epoch,layout.schema(),config->context,digest(pinned),config->archive_sharing_domain,layout.encoding(),party,box,files,journal),capture(checkpoint,layout.schema(),party,[&machine]()->Player&{return machine.get_player();}),coordinator(config->epoch,config->context,digest(pinned),party,capture,checkpoint,journal,certificates,collective,[&machine]()->Player&{return machine.get_player();}){manifest=digest(pinned);}
  static Digest digest(const tls_mpc_worker::PinnedPrograms& pinned){Digest result;std::copy_n(pinned.digest().begin(),32,result.begin());return result;}
 };
 struct Recovered {
  std::shared_ptr<Persistence> persistence;std::shared_ptr<AccountDurableOwnerV1> owner;Bits validity;
  std::optional<NativeAccountOutbox::Pending> pending;Digest head,boot;size_t ordinal;unsigned party;
 };
public:
 static std::unique_ptr<AuthorizedRestoredAccount> resolve(std::shared_ptr<Config> config,
   Machine<tls_mpc_worker::Share>& machine,tls_mpc_worker::Worker& worker,tls_mpc_worker::PinnedPrograms& pinned,Collective& collective,unsigned party){
  using tls_mpc_worker::ErasedHostCall;
  require(!ErasedHostCall::active()&&config&&party<5,"account engine resolver context");
  std::shared_ptr<Persistence> persistence;std::optional<AccountCheckpointCoordinator::CurrentHead> current;std::optional<QuarantinedEvaluations> raw;
  bool loaded=ErasedHostCall::run([&]{
   bool ready=false;try{
    require(std::filesystem::is_directory(config->local_directory+"/shares")&&std::filesystem::is_directory(config->local_directory+"/certificates"),"account restore directory absent");
    persistence=std::make_shared<Persistence>(config,party,machine,pinned,collective);ready=true;
   }catch(...){}collective.require_local_success(ready);require(ready,"account engine persistence setup failed");
   current.emplace(persistence->coordinator.recover_current());require(current->commit&&current->reservation&&current->commit->proposal.slot>=1&&current->commit->proposal.slot<=4,"account engine requires committed c1 bounded profile");
   ready=false;try{raw.emplace(persistence->checkpoint.load_committed(party,persistence->layout.schema().bits(),current->reservation->proposal.parent,*current->reservation,*current->commit,current->challenge,current->statuses));ready=true;}catch(...){}
   collective.require_local_success(ready);require(ready,"account engine current ciphertext unavailable");
  });
  require(loaded&&persistence&&current&&raw,"account engine authorized current-head load failed");
  auto head=current->commit->proposal.digest(config->epoch);auto ordinal=current->commit->proposal.slot-1;
  auto schema=label("SIGNAL-ACCOUNT-FULL-READMIT-V2/CCD128");append(schema,persistence->layout.encoding());append(schema,head);append(schema,current->challenge);
  // This transcript domain is separate from the already authenticated archive
  // header. Stored masks/preprocessing/TLS state are never re-used or imported.
  ShareDomain domain{party,config->epoch.number,current->commit->proposal.slot,persistence->layout.schema().bits(),config->context,config->epoch.digest(),persistence->manifest,hash(schema),config->archive_sharing_domain};
  auto imported=NativeAccountReadmit::run(persistence->layout,std::move(*raw),domain,machine,worker,pinned,ordinal,true);raw.reset();
  require(imported.pending&&imported.helpers_destroyed==1,"account engine resume policy/helper prerequisite");
  auto state=std::make_shared<Recovered>();state->persistence=persistence;state->owner=std::make_shared<AccountDurableOwnerV1>(persistence,persistence->coordinator,std::move(imported.account),current->commit->proposal.slot);state->validity=std::move(imported.computed_validity);state->pending=std::move(imported.pending);state->head=head;state->boot=current->challenge;state->ordinal=ordinal;state->party=party;
  auto build=[state](Session& session,Collective& fresh_collective,unsigned who){
   require(who==state->party&&state->pending,"account engine factory consumed/misowned");auto& owner=*state->owner;owner.attach_fresh_session(session);auto& snapshot=owner.snapshot();
   tls_mpc_worker::MuxProviderAdmission admission;admission.restored_account=true;admission.credentials=copy(snapshot.global(1));admission.computed_credential_validity=copy(state->validity);admission.restored_request_cursor=copy(snapshot.global(4));admission.computed_cursor_validity=copy(state->validity);
   auto material=label("SIGNAL-RESTORED-OUTBOX-LEASE-V1");append(material,state->head);append(material,state->boot);u64(material,0);u64(material,state->ordinal);auto hash_value=hash(material);uint64_t lease=read64(hash_value.data())|(uint64_t(1)<<63);
   auto fence=state->persistence->config->local_directory+"/fence-"+hex(state->head)+"-"+hex(state->boot)+"-0";
   auto conversation=std::make_unique<tls_mpc_worker::NativeConversation>(session,fresh_collective,VariableShape(260,80,false,false),copy(snapshot.conversation(0,12)),fence,state->owner,0);
   owner.register_resume(0,lease,state->ordinal);std::vector<std::unique_ptr<tls_mpc_worker::PrivateInputBuilder>> inputs;
   auto& configured=state->persistence->config->inputs;if(configured)inputs=configured(session,fresh_collective,who);configured={};
   tls_mpc_worker::ConversationAdmission row{std::move(conversation),copy(state->validity),std::move(inputs),{}};
   row.pending_outboxes.push_back({lease,std::move(state->pending->typed_payload),std::move(state->pending->expected_id),std::move(state->pending->computed_resumability),1290});state->pending.reset();admission.conversations.push_back(std::move(row));return admission;
  };
  return std::unique_ptr<AuthorizedRestoredAccount>(new AuthorizedRestoredAccount(std::move(build),party,head,current->challenge,imported.import_host,imported.retirement_host));
 }
};
}
