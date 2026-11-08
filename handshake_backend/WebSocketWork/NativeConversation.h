#pragma once
#include "NativeProvider.h"
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
    void authenticated_response_complete(uint64_t ticket){
        try{public_require(phase==Phase::pending,"conversation response unavailable");store.response_complete(ticket);phase=Phase::active;}
        catch(...){close();throw;}
    }
    void close()noexcept{phase=Phase::closed;store.close();}
};
}
