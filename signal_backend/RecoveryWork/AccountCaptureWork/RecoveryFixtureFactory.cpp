// Explicit disposable fixture factory only. No share/plaintext import RPC.
#include "PublicAccountFixture.h"
#include "WebSocketWork/NativeTextInput.h"
#include <cstdlib>
namespace tls_mpc_worker {
signal_mpc::recovery::AccountRecoveryResolver make_account_recovery_resolver(){
 const char* environment=std::getenv("TLS_ACCOUNT_ARCHIVE_ROOT");if(!environment||!*environment)return {};std::string root=environment;
 return [root](Machine<Share>& machine,Worker& worker,PinnedPrograms& pinned,Collective& collective,unsigned party){
  std::shared_ptr<signal_mpc::recovery::AccountRecoveryEngineV1::Config> config;
  bool initialized=ErasedHostCall::run([&]{bool ready=false;try{
  config=signal_mpc::recovery::public_account_fixture(root,party);
  config->inputs=[](Session& session,Collective&,unsigned){
   const std::string text="Restored conversation: hello again!";PublicBytes input{255,0,static_cast<unsigned char>(text.size())};input.insert(input.end(),text.begin(),text.end());input.resize(51,0);uint64_t timestamp=1900000000019ULL;for(int i=7;i>=0;--i)input.push_back((timestamp>>(i*8))&255);
   std::vector<std::unique_ptr<PrivateInputBuilder>> result;result.push_back(std::make_unique<NativeTextInput>(session.share_public_constants(input),session.share_public_constants({255})));return result;
  };
  ready=true;}catch(...){config.reset();}
  try{collective.require_local_success(ready);public_require(ready,"account fixture config initialization failed");}catch(...){config.reset();throw;}
  });public_require(initialized&&bool(config),"account fixture key host initialization failed");
  return signal_mpc::recovery::AccountRecoveryEngineV1::resolve(std::move(config),machine,worker,pinned,collective,party);
 };
}
}
