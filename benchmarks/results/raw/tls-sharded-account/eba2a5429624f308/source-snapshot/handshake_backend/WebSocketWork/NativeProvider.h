#pragma once
#include "NativeSession.h"
#include "NativeCollective.h"
#include "PrivateProviderRegistry.h"
#include "../signal_backend/VariableServiceWork/PrivateProvider.h"
namespace tls_mpc_worker {
using ProviderRegistry=PrivateProviderRegistry<Bits>;
// Same-worker adapter; admitted shares are moved from a trusted embedding, not
// decoded from network/CLI data. Bootstrap authentication is an external duty.
class NativeProvider final : public ProviderRegistry::Provider {
    Session& session;Collective& collective;
    signal_mpc::PrivateProvider<Bits> provider;
public:
    NativeProvider(Session& session,Collective& collective,signal_mpc::UpgradeShape upgrade,
      Bits credentials,signal_mpc::VariableShape shape,Bits initial,const std::string& fence_slot)
      :session(session),collective(collective),provider(upgrade,std::move(credentials),shape,std::move(initial),fence_slot) {}
    ProviderRegistry::Upgrade upgrade(Bits nonce) override {
        auto output=provider.upgrade(std::move(nonce),[&](const auto& shape,Bits input){return session.evaluate_upgrade(shape,std::move(input));});
        return{std::move(output),provider.upgrade_shape().output_bytes()};
    }
    void upgrade_complete() override {provider.upgrade_complete();}
    ProviderRegistry::Produced produce(Bits payload,Bits timestamp) override {
        bool joined=false;
        try {
            auto output=provider.produce(std::move(payload),std::move(timestamp),[&](const auto& shape,Bits input){
                joined=true;collective.require_local_success(true);return session.evaluate_variable(shape,std::move(input));});
            return{output.ticket,std::move(output.payload),std::move(output.request_id),provider.shape().frame_capacity()};
        }catch(...){if(!joined){joined=true;collective.require_local_success(false);}throw;}
    }
    ProviderRegistry::Produced produce_with_request_id(Bits payload,Bits timestamp,Bits id) override {
        bool joined=false;
        try {
            auto output=provider.produce_with_request_id(std::move(payload),std::move(timestamp),std::move(id),[&](const auto& shape,Bits input){
                joined=true;collective.require_local_success(true);return session.evaluate_variable(shape,std::move(input));});
            return{output.ticket,std::move(output.payload),std::move(output.request_id),provider.shape().frame_capacity()};
        }catch(...){if(!joined){joined=true;collective.require_local_success(false);}throw;}
    }
    void response_complete(uint64_t ticket) override {provider.response_complete(ticket);}
    void close() noexcept override {provider.close();}
};
inline ProviderRegistry::Hooks provider_hooks(Session& session,std::function<void()> terminal) {
    return {
      [&](Bits payload,Bits validity){return session.retain_validated_upgrade(std::move(payload),std::move(validity));},
      [&](Bits payload,size_t capacity){return session.retain_private_result(std::move(payload),capacity);},
      [&](Bits producer,Bits upstream){return session.combine_private_validity(std::move(producer),std::move(upstream));},
      [&](Bits id){session.expect_websocket_response(std::move(id));},
      [&]{session.checkpoint_private_computation();},std::move(terminal)};
}
}
