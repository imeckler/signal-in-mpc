#pragma once
#include "NativeProvider.h"
#include <openssl/sha.h>
#include <openssl/evp.h>
namespace tls_mpc_worker {
struct ProviderInput {Bits payload,timestamp,computed_validity;};
struct ProviderAdmission {
    std::unique_ptr<ProviderRegistry::Provider> provider;
    Bits credential_validity,state_validity;
    std::vector<ProviderInput> inputs;
};
// Factory only moves already authenticated same-worker state. It must not
// perform private VM work before collective admission readiness. There is no
// automatic factory or RPC/CLI plaintext/share deserializer.
using ProviderFactory=std::function<ProviderAdmission(Session&,Collective&,unsigned)>;
ProviderFactory make_provider_factory();
class ProviderCoordinator {
    Session& session;Collective& collective;ProviderFactory factory;
    std::unique_ptr<ProviderRegistry> registry;
    std::vector<uint64_t> input_handles;
    uint64_t state_handle=0;bool initialized=false,upgrade_started=false,upgraded=false,closed=false;
    PublicBytes nonce;
    static PublicBytes accept(const PublicBytes& nonce) {
        public_require(nonce.size()==16,"invalid public WebSocket nonce");
        unsigned char key[25]={},digest[20],encoded[29]={};EVP_EncodeBlock(key,nonce.data(),16);
        std::string material(reinterpret_cast<char*>(key),24);material+="258EAFA5-E914-47DA-95CA-C5AB0DC85B11";
        SHA1(reinterpret_cast<const unsigned char*>(material.data()),material.size(),digest);
        EVP_EncodeBlock(encoded,digest,20);return PublicBytes(encoded,encoded+28);
    }
public:
    ProviderCoordinator(Session& session,Collective& collective,ProviderFactory factory,PublicBytes public_nonce)
      :session(session),collective(collective),factory(std::move(factory)),nonce(std::move(public_nonce)) {}
    void initialize(unsigned party,std::function<void()> terminal) {
        public_require(!initialized&&!closed,"provider initialization repeated");initialized=true;
        collective.agree_provider_availability(bool(factory));
        registry=std::make_unique<ProviderRegistry>(provider_hooks(session,std::move(terminal)));
        if(!factory)return; // Explicit absence: no state/payload handles exist.
        bool joined=false;
        try {
            auto admission=factory(session,collective,party);
            state_handle=registry->admit(std::move(admission.provider),std::move(admission.credential_validity),std::move(admission.state_validity));
            for(auto& input:admission.inputs)input_handles.push_back(registry->admit_input(
                std::move(input.payload),std::move(input.timestamp),std::move(input.computed_validity)));
            factory={};joined=true;collective.require_local_success(true);
        }catch(...){factory={};if(!joined){joined=true;collective.require_local_success(false);}close();throw;}
    }
    PublicBytes catalogue() const {
        public_require(initialized&&!closed,"provider catalogue unavailable");
        PublicBytes out;put_number(out,state_handle,8);put_number(out,input_handles.size(),2);
        for(auto id:input_handles)put_number(out,id,8);return out;
    }
    ProviderRegistry::Receipt upgrade(uint64_t state) {
        public_require(initialized&&!closed&&registry&&state==state_handle&&state&&!upgrade_started,"private provider upgrade unavailable");
        upgrade_started=true;session.start_websocket(accept(nonce));
        return registry->upgrade(state,session.share_public_constants(nonce));
    }
    ProviderRegistry::Receipt produce(uint64_t state,uint64_t input) {
        public_require(initialized&&!closed&&registry&&state==state_handle&&upgraded,"private provider send unavailable");
        return registry->produce(state,input);
    }
    // Invoke in a NEW erased host call after process_websocket's barrier.
    void authenticated_receipt(const PublicBytes& receipt) {
        public_require(initialized&&!closed&&registry&&receipt.size()>=3,"invalid private provider receipt");
        size_t count=receipt[2];public_require(count<=4&&receipt.size()==3+11*count,"invalid WebSocket receipt shape");
        for(size_t i=0;i<count;++i)if(receipt[3+11*i]==8){close();return;}
        if(receipt[0]&&!upgraded){registry->authenticated_upgrade_complete();upgraded=true;}
        if(receipt[1])registry->authenticated_response_complete();
    }
    void close() noexcept {closed=true;factory={};input_handles.clear();if(registry){registry->close();registry.reset();}}
};
}
