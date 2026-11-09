// Explicit fixture resolver. Actual current-head/import/retirement capability;
// no default provider or JSON/share-import entry point.
#include "ShardedRecoveryEngine.h"
#include "FixtureConfig.h"
#include "FreshFixture.h"
#include "../../../handshake_backend/WebSocketWork/NativeTextInput.h"
#include <cstdlib>
namespace tls_mpc_worker {
signal_mpc::recovery::AccountRecoveryResolver make_account_recovery_resolver(){
 return [](Machine<Share>& machine,Worker& worker,PinnedPrograms& pinned,Collective& collective,unsigned party){
  using namespace signal_mpc::recovery;using namespace signal_mpc::recovery::sharded;
  std::unique_ptr<signal_mpc::recovery::sharded::Engine::Config> config;
  bool ready=ErasedHostCall::run([&]{bool local=false;try{const char* root=std::getenv("TLS_SHARDED_ACCOUNT_ROOT");public_require(root&&*root,"sharded fixture archive root absent");config=std::make_unique<signal_mpc::recovery::sharded::Engine::Config>();config->persistence=fixture_config(root,party);config->active_slots={0,1};config->inputs=[](size_t slot,Session& session,Collective&,unsigned){
    std::vector<std::unique_ptr<PrivateInputBuilder>> inputs;for(size_t round=1;round<6;++round)inputs.push_back(std::make_unique<NativeTextInput>(session.share_public_constants(FreshFixture::text(slot,round)),session.share_public_constants({255})));return inputs;};local=true;
   }catch(...){config.reset();}collective.require_local_success(local);public_require(local,"sharded fixture key load failed");});
  public_require(ready&&config,"sharded fixture setup host incomplete");return signal_mpc::recovery::sharded::Engine::resolve(std::move(config),machine,worker,pinned,collective,party);
 };
}
}
