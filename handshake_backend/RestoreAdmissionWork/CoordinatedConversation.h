#pragma once
#include "../../signal_backend/VariableServiceWork/VariableSendBatch.h"
#include <functional>
namespace tls_mpc_worker {
// Trusted account owner only; no RPC can supply these hooks. Reserve binds
// all frozen intents and cursor in one certificate; bind handles actual output.
template<class Bits> class DurableConversationHooksT {
public:
    using Store=signal_mpc::VariableSendStore<Bits>;
    virtual ~DurableConversationHooksT()=default;
    virtual void reserve(const std::vector<size_t>& slots,const std::vector<signal_mpc::VariableShape>& shapes,
        const std::vector<typename Store::Staged>& staged,const Bits& current_cursor,const Bits& final_cursor,uint64_t lease)=0;
    virtual std::vector<Bits> bind(const std::vector<size_t>& slots,
        const std::vector<signal_mpc::VariableShape>& shapes,std::vector<Bits> actual_outputs)=0;
    virtual void commit(const std::vector<size_t>& slots,const std::vector<signal_mpc::VariableShape>& shapes,
        const std::vector<typename Store::Candidate>& candidates)=0;
    virtual void response_complete(size_t slot,uint64_t ticket)=0;
    virtual void close()noexcept=0;
};
// A conversation on an independently authenticated connection. Credential
// provenance and account association are supplied by the embedding admission;
// this adapter never performs or fabricates an HTTP upgrade acknowledgement.
template<class Bits,class Session,class Collective> class CoordinatedConversation {
    using DurableConversationHooks=DurableConversationHooksT<Bits>;
    static void public_require(bool ok,const char* reason){if(!ok)throw std::runtime_error(reason);}
    Session& session;Collective& collective;
    signal_mpc::VariableShape shape;
    signal_mpc::VariableSendStore<Bits> store;
    enum class Phase {admitted,active,resume_ready,producing,pending,closed};
    Phase phase=Phase::admitted;
    std::shared_ptr<DurableConversationHooks> account;size_t account_slot=0;uint64_t resume_ticket=0;bool resumed_pending=false;
public:
    struct Produced {uint64_t ticket;Bits payload,request_id;size_t capacity;};
    CoordinatedConversation(Session& session,Collective& collective,signal_mpc::VariableShape shape,
      Bits established,const std::string& authoritative_fence)
      :session(session),collective(collective),shape(shape),store(shape,std::move(established),authoritative_fence){}
    CoordinatedConversation(Session& session,Collective& collective,signal_mpc::VariableShape shape,
      Bits established,const std::string& authoritative_fence,
      std::shared_ptr<DurableConversationHooks> authorized_account,size_t slot)
      :CoordinatedConversation(session,collective,shape,std::move(established),authoritative_fence){
        public_require(bool(authorized_account),"missing durable account owner");account=std::move(authorized_account);account_slot=slot;
    }
    bool durable()const{return bool(account);}
    bool same_durable_account(const CoordinatedConversation& other)const{return account&&account==other.account;}
    size_t durable_slot()const{public_require(bool(account),"durable slot unavailable");return account_slot;}
    ~CoordinatedConversation(){close();}
    CoordinatedConversation(const CoordinatedConversation&)=delete;
    CoordinatedConversation& operator=(const CoordinatedConversation&)=delete;
    std::string public_profile()const{return shape.descriptor();}
    void authenticated_connection_ready(){
        try{public_require(phase==Phase::admitted,"conversation activation rejected");phase=resume_ticket?Phase::resume_ready:Phase::active;}
        catch(...){close();throw;}
    }
    size_t frame_capacity()const{return shape.frame_capacity();}
    void admit_pending_outbox(uint64_t ticket){
        try{public_require(account&&phase==Phase::admitted&&!resume_ticket&&ticket,"pending outbox admission rejected");resume_ticket=ticket;}
        catch(...){close();throw;}
    }
    void resume_pending_outbox(uint64_t ticket){
        bool joined=false;
        try{public_require(account&&phase==Phase::resume_ready&&resume_ticket==ticket,"pending outbox lease rejected");
            phase=Phase::pending;resumed_pending=true;joined=true;collective.require_local_success(true);
        }catch(...){close();if(!joined)collective.require_local_success(false);throw;}
    }
    Produced produce(Bits payload,Bits timestamp,Bits assigned_id){
        auto results=produce_batch({BatchRequest{this,std::move(payload),std::move(timestamp),std::move(assigned_id)}});
        return std::move(results.front());
    }
    struct BatchRequest {CoordinatedConversation* conversation;Bits payload,timestamp,request_id;};
    static std::vector<Produced> produce_batch(std::vector<BatchRequest> requests){
        bool joined=false;CoordinatedConversation* first=requests.empty()?nullptr:requests.front().conversation;
        auto abort_all=[&]()noexcept{for(auto& request:requests)if(request.conversation)request.conversation->close();};
        try{
            public_require(first&&requests.size()<=4,"conversation batch unavailable");
            for(size_t i=0;i<requests.size();++i){auto* owner=requests[i].conversation;
                public_require(owner&&owner->phase==Phase::active&& &owner->session==&first->session&&
                    &owner->collective==&first->collective&&owner->public_profile()==first->public_profile()&&owner->account==first->account,"conversation batch ownership rejected");
                for(size_t j=0;j<i;++j)public_require(requests[j].conversation!=owner&&(!owner->account||requests[j].conversation->account_slot!=owner->account_slot),"duplicate batch conversation");}
            std::vector<signal_mpc::BatchSendRequest<Bits>> inputs;inputs.reserve(requests.size());
            for(auto& request:requests){request.conversation->phase=Phase::producing;
                inputs.push_back({&request.conversation->store,std::move(request.payload),std::move(request.timestamp),std::move(request.request_id)});}
            std::vector<size_t> slots;for(auto& request:requests)slots.push_back(request.conversation->account_slot);
            auto results=signal_mpc::produce_batch_with_checkpoint<Bits>(std::move(inputs),
                [&](const auto& shapes,const auto& staged){
                    joined=true;first->collective.require_local_success(true);
                    if(first->account)first->session.commit_private_request_ids([&](const Bits& current,const Bits& final,uint64_t lease,size_t count){
                        public_require(count==staged.size(),"account cursor range mismatch");
                        first->account->reserve(slots,shapes,staged,current,final,lease);
                    });
                },
                [&](const auto& shapes,std::vector<Bits> values){
                    std::vector<Bits> outputs;
                    if(shapes.size()==1)outputs.push_back(first->session.evaluate_variable(shapes.front(),std::move(values.front())));
                    else outputs=first->session.evaluate_variable_batch(shapes,std::move(values));
                    if(first->account)outputs=first->account->bind(slots,shapes,std::move(outputs));
                    return outputs;
                },
                [&](const auto& shapes,const auto& candidates){if(first->account)first->account->commit(slots,shapes,candidates);});
            for(auto& request:requests)public_require(request.conversation->phase==Phase::producing,"conversation batch interrupted");
            std::vector<Produced> output;output.reserve(results.size());
            for(size_t i=0;i<results.size();++i){auto& result=results[i];requests[i].conversation->phase=Phase::pending;
                output.push_back({result.ticket,std::move(result.payload),std::move(result.request_id),requests[i].conversation->shape.frame_capacity()});}
            return output;
        }catch(...){abort_all();if(first&&!joined){joined=true;first->collective.require_local_success(false);}throw;}
    }
    void authenticated_response_complete(uint64_t ticket){
        try{public_require(phase==Phase::pending,"conversation response unavailable");if(resumed_pending)public_require(ticket==resume_ticket,"restored response lease rejected");
            if(account)account->response_complete(account_slot,ticket);
            if(!resumed_pending)store.response_complete(ticket);
            resumed_pending=false;resume_ticket=0;phase=Phase::active;}
        catch(...){close();throw;}
    }
    void close()noexcept{phase=Phase::closed;resume_ticket=0;resumed_pending=false;store.close();if(account)account->close();}
};
}
