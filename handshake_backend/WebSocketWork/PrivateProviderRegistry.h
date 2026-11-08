#pragma once
#include <algorithm>
#include <cstdint>
#include <functional>
#include <map>
#include <memory>
#include <stdexcept>
#include <utility>
namespace tls_mpc_worker {
// Internal embedding API. No method decodes shares/plaintext from an RPC.
// The caller supplies same-worker owned Bits from its authenticated bootstrap
// or another private computation. This API does not establish that provenance.
template<class Bits> class PrivateProviderRegistry {
public:
    struct Produced {uint64_t ticket;Bits payload,request_id;size_t capacity;};
    struct Upgrade {Bits payload;size_t capacity;};
    class Provider {
    public:
        virtual ~Provider()=default;
        virtual Upgrade upgrade(Bits public_nonce)=0;
        virtual void upgrade_complete()=0;
        virtual Produced produce(Bits payload,Bits timestamp)=0;
        virtual Produced produce_with_request_id(Bits,Bits,Bits) {
            throw std::runtime_error("private provider connection ID binding unavailable");
        }
        virtual void response_complete(uint64_t ticket)=0;
        virtual void close() noexcept=0;
    };
    struct Hooks {
        std::function<uint64_t(Bits,Bits)> retain_validated_upgrade;
        std::function<uint64_t(Bits,size_t)> retain_private;
        // Both inputs are actual computed private flags. The pinned gate must
        // return255 exactly when both equal255; nothing is opened here.
        std::function<Bits(Bits,Bits)> combine_validity;
        std::function<void(Bits)> expect_response;
        std::function<void()> checkpoint;
        std::function<void()> terminal;
    };
    struct Receipt {uint64_t handle;size_t capacity;};
private:
    struct Input {Bits payload,timestamp,validity;};
    Hooks hooks;std::unique_ptr<Provider> provider;
    std::map<uint64_t,Input> inputs;
    Bits credential_validity,state_validity;
    uint64_t next_input=1,ticket=0;
    bool upgrade_reserved=false,upgraded=false,pending=false,closed=false;
    static void require(bool ok,const char* reason){if(!ok)throw std::runtime_error(reason);}
    void live() const {require(!closed,"private provider registry closed");}
    void fail() noexcept {close();try{hooks.terminal();}catch(...){}}
public:
    explicit PrivateProviderRegistry(Hooks hooks):hooks(std::move(hooks)) {
        require(bool(this->hooks.retain_validated_upgrade)&&bool(this->hooks.retain_private)&&
          bool(this->hooks.combine_validity)&&bool(this->hooks.expect_response)&&
          bool(this->hooks.checkpoint)&&bool(this->hooks.terminal),"incomplete private provider hooks");
    }
    ~PrivateProviderRegistry(){close();}
    PrivateProviderRegistry(const PrivateProviderRegistry&)=delete;
    PrivateProviderRegistry& operator=(const PrivateProviderRegistry&)=delete;
    // First profile: exactly one opaque provider/state slot per connection.
    uint64_t admit(std::unique_ptr<Provider> selected,Bits computed_credential_validity,Bits computed_state_validity) {
        live();require(!provider&&bool(selected)&&computed_credential_validity.size()==8&&computed_state_validity.size()==8,"private provider admission unavailable");
        provider=std::move(selected);credential_validity=std::move(computed_credential_validity);
        state_validity=std::move(computed_state_validity);return 1;
    }
    uint64_t admit_input(Bits payload,Bits timestamp,Bits computed_validity) {
        live();require(provider&&timestamp.size()==64&&computed_validity.size()==8&&
          payload.size()%8==0&&payload.size()<=16384*8&&inputs.size()<64&&next_input,
          "invalid private provider input admission");
        auto id=next_input++;inputs.emplace(id,Input{std::move(payload),std::move(timestamp),std::move(computed_validity)});return id;
    }
    Receipt upgrade(uint64_t state_handle,Bits public_nonce) {
        try {
            live();require(state_handle==1&&provider&&!upgrade_reserved&&public_nonce.size()==128,"private upgrade unavailable");
            auto result=provider->upgrade(std::move(public_nonce));
            require(result.capacity<=16384&&result.payload.size()==result.capacity*8,"invalid private upgrade dimensions");
            upgrade_reserved=true;auto id=hooks.retain_validated_upgrade(std::move(result.payload),std::move(credential_validity));
            hooks.checkpoint();return{id,result.capacity};
        }catch(...){fail();throw;}
    }
    void authenticated_upgrade_complete() {
        try {live();require(provider&&upgrade_reserved&&!upgraded,"unsolicited private upgrade acknowledgement");
            provider->upgrade_complete();upgraded=true;
        }catch(...){fail();throw;}
    }
    Receipt produce(uint64_t state_handle,uint64_t input_handle) {
        try {
            live();require(state_handle==1&&provider&&upgraded&&!pending,"private send unavailable");
            auto found=inputs.find(input_handle);require(found!=inputs.end(),"unknown or consumed private input handle");
            auto input=std::move(found->second);inputs.erase(found);
            auto result=provider->produce(std::move(input.payload),std::move(input.timestamp));
            // The provider has already committed selected state. Any subsequent
            // failure poisons the connection; no input/ticket is retried.
            pending=true;ticket=result.ticket;
            require(ticket&&result.capacity<=16384&&result.payload.size()==8*(result.capacity+3)&&result.request_id.size()==64,
              "invalid private provider result dimensions");
            Bits status(result.payload.begin(),result.payload.begin()+8);
            auto input_accepted=hooks.combine_validity(Bits(state_validity),std::move(input.validity));
            auto accepted=hooks.combine_validity(std::move(status),std::move(input_accepted));
            require(accepted.size()==8,"invalid private producer validity gate");
            std::move(accepted.begin(),accepted.end(),result.payload.begin());
            auto id=hooks.retain_private(std::move(result.payload),result.capacity);
            hooks.expect_response(std::move(result.request_id));hooks.checkpoint();return{id,result.capacity};
        }catch(...){fail();throw;}
    }
    // Called only by the internal coordinator after authenticated private
    // correlation+2xx and the receive host barrier, never by an ACK RPC.
    void authenticated_response_complete() {
        try {live();require(provider&&pending,"unsolicited private response acknowledgement");
            provider->response_complete(ticket);pending=false;ticket=0;
        }catch(...){fail();throw;}
    }
    void close() noexcept {
        closed=true;pending=false;ticket=0;inputs.clear();credential_validity.clear();state_validity.clear();
        if(provider){provider->close();provider.reset();}
    }
};
}
