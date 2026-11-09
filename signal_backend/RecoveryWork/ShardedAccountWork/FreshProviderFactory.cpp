// Explicit NEW PUBLIC disposable fixture. Never linked by default worker.
#include "../../../handshake_backend/WebSocketWork/MuxProviderCoordinator.h"
#include "../../../handshake_backend/WebSocketWork/NativeTextInput.h"
#include "ShardPersistence.h"
#include "ShardedDurableOwner.h"
#include "FreshFixture.h"
#include <cstdlib>
namespace tls_mpc_worker {
MuxProviderFactory make_mux_provider_factory(){return [](Session& session,Collective& collective,unsigned party){
 using namespace signal_mpc::recovery;using namespace signal_mpc::recovery::sharded;
 auto share=[&](const PublicBytes& bytes){return session.share_public_constants(bytes);};
 std::shared_ptr<Persistence> persistence;bool ready=false;
 try{const char* root=std::getenv("TLS_SHARDED_ACCOUNT_ROOT");public_require(root&&*root,"fresh sharded fixture archive root absent");auto config=std::make_unique<Persistence::Config>();config->epoch.number=1;config->epoch.genesis=signal_mpc::recovery::hash(label("NEW-SHARDED-ACCOUNT-FIXTURE-GENESIS-SEEDS91-97"));
  for(unsigned p=0;p<5;++p){Digest seed{};seed.fill(p+191);Signer signer(seed);config->epoch.members[p]=signer.public_key();}config->signing_seed.fill(party+191);config->context=signal_mpc::recovery::hash(label("NEW-SHARDED-ACCOUNT-FIXTURE-CONTEXT-SEEDS91-97"));config->sharing=signal_mpc::recovery::hash(label("NEW-SHARDED-ACCOUNT-FIXTURE-SHARING-SEEDS91-97"));for(size_t i=0;i<64;++i)config->storage_key[i]=i+party*11+91;config->directory=std::string(root)+"/"+std::to_string(party);persistence=std::make_shared<Persistence>(std::move(config),session,collective,party);ready=true;
 }catch(...){persistence.reset();}
 collective.require_local_success(ready);public_require(ready,"fresh shard persistence setup rejected");auto current=persistence->coordinator.recover_current();public_require(!current.commit&&!current.reservation,"fresh fixture refuses previous account");
 auto random=collective.public_random();Digest boot{};std::copy_n(random.begin(),32,boot.begin());auto global=share(FreshFixture::global());std::map<size_t,Bits> active;for(size_t slot=0;slot<2;++slot)active.emplace(slot,share(FreshFixture::conversation(slot)));
 auto context=signal_mpc::recovery::hash(label("NEW-SHARDED-ACCOUNT-FIXTURE-CONTEXT-SEEDS91-97"));auto owner=std::make_shared<DurableOwner>(persistence,persistence->coordinator,persistence->local,persistence->directory,persistence->capture,session,persistence->epoch(),context,persistence->manifest(),boot,Bits(global.begin(),global.end()),std::move(active),current);
 MuxProviderAdmission result;result.fresh_durable_account=true;result.credentials=Bits(global.begin(),global.begin()+38*8);result.computed_credential_validity=share({255});result.restored_request_cursor=Bits(global.begin()+8298*8,global.end());result.computed_cursor_validity=share({255});
 const char* root=std::getenv("TLS_SHARDED_ACCOUNT_ROOT");
 for(size_t slot=0;slot<2;++slot){ConversationAdmission row;row.computed_validity=share({255});row.conversation=std::make_unique<NativeConversation>(session,collective,signal_mpc::VariableShape(260,80,false,false),share(FreshFixture::service(slot)),std::string(root)+"/"+std::to_string(party)+"/fresh-conversation-"+std::to_string(slot),owner,slot);
  for(size_t round=0;round<6;++round)row.inputs.push_back(std::make_unique<NativeTextInput>(share(FreshFixture::text(slot,round)),share({255})));result.conversations.push_back(std::move(row));}
 return result;
};}
}
