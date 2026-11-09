#pragma once
#include "NativeProvider.h"
#include "../signal_backend/VariableServiceWork/VariableSendBatch.h"
namespace tls_mpc_worker {
// A conversation on an independently authenticated connection. Credential
// provenance and account association are supplied by the embedding admission;
// this adapter never performs or fabricates an HTTP upgrade acknowledgement.
class NativeConversation {
    Session& session;Collective& collective;
    signal_mpc::VariableShape shape;
    signal_mpc::VariableSendStore<Bits> store;
    enum class Phase {admitted,active,producing,pending,closed};
    Phase phase=Phase::admitted;
public:
    using Produced=ProviderRegistry::Produced;
    NativeConversation(Session& session,Collective& collective,signal_mpc::VariableShape shape,
      Bits established,const std::string& authoritative_fence)
      :session(session),collective(collective),shape(shape),store(shape,std::move(established),authoritative_fence){}
    ~NativeConversation(){close();}
    NativeConversation(const NativeConversation&)=delete;
    NativeConversation& operator=(const NativeConversation&)=delete;
    std::string public_profile()const{return shape.descriptor();}
    void authenticated_connection_ready(){
        try{public_require(phase==Phase::admitted,"conversation activation rejected");phase=Phase::active;}
        catch(...){close();throw;}
    }
    Produced produce(Bits payload,Bits timestamp,Bits assigned_id){
        bool joined=false;
        try{
            public_require(phase==Phase::active,"conversation send unavailable");phase=Phase::producing;
            auto result=store.produce_with_request_id(std::move(payload),std::move(timestamp),std::move(assigned_id),
              [&](const auto& selected,Bits input){joined=true;collective.require_local_success(true);
                  return session.evaluate_variable(selected,std::move(input));});
            public_require(phase==Phase::producing,"conversation evaluation interrupted");phase=Phase::pending;
            return{result.ticket,std::move(result.payload),std::move(result.request_id),shape.frame_capacity()};
        }catch(...){close();if(!joined){joined=true;collective.require_local_success(false);}throw;}
    }
    struct BatchRequest {NativeConversation* conversation;Bits payload,timestamp,request_id;};
    static std::vector<Produced> produce_batch(std::vector<BatchRequest> requests){
        bool joined=false;NativeConversation* first=requests.empty()?nullptr:requests.front().conversation;
        auto abort_all=[&]()noexcept{for(auto& request:requests)if(request.conversation)request.conversation->close();};
        try{
            public_require(first&&requests.size()<=4,"conversation batch unavailable");
            for(size_t i=0;i<requests.size();++i){auto* owner=requests[i].conversation;
                public_require(owner&&owner->phase==Phase::active&& &owner->session==&first->session&&
                    &owner->collective==&first->collective&&owner->public_profile()==first->public_profile(),"conversation batch ownership rejected");
                for(size_t j=0;j<i;++j)public_require(requests[j].conversation!=owner,"duplicate batch conversation");}
            std::vector<signal_mpc::BatchSendRequest<Bits>> inputs;inputs.reserve(requests.size());
            for(auto& request:requests){request.conversation->phase=Phase::producing;
                inputs.push_back({&request.conversation->store,std::move(request.payload),std::move(request.timestamp),std::move(request.request_id)});}
            auto results=signal_mpc::produce_batch_with_checkpoint<Bits>(std::move(inputs),
                [&](const auto&,const auto&){joined=true;first->collective.require_local_success(true);},
                [&](const auto& shapes,std::vector<Bits> values){return first->session.evaluate_variable_batch(shapes,std::move(values));},
                [](const auto&,const auto&){}); // Existing nonrecovering admission; no durability claim.
            for(auto& request:requests)public_require(request.conversation->phase==Phase::producing,"conversation batch interrupted");
            std::vector<Produced> output;output.reserve(results.size());
            for(size_t i=0;i<results.size();++i){auto& result=results[i];requests[i].conversation->phase=Phase::pending;
                output.push_back({result.ticket,std::move(result.payload),std::move(result.request_id),requests[i].conversation->shape.frame_capacity()});}
            return output;
        }catch(...){abort_all();if(first&&!joined){joined=true;first->collective.require_local_success(false);}throw;}
    }
    void authenticated_response_complete(uint64_t ticket){
        try{public_require(phase==Phase::pending,"conversation response unavailable");store.response_complete(ticket);phase=Phase::active;}
        catch(...){close();throw;}
    }
    void close()noexcept{phase=Phase::closed;store.close();}
};
}
