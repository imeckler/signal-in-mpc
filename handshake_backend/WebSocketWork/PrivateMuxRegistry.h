#pragma once
#include <array>
#include <cstdint>
#include <utility>
#include <map>
#include <memory>
#include <functional>
#include <stdexcept>
#include <type_traits>
namespace tls_mpc_worker {
// Internal only: authenticated connection activation and completion events come
// from the coordinator after receive cleanup. No public ACK/ID import exists.
template<class Bits,class Conversation> class PrivateMuxRegistry {
public:
    struct Receipt {uint64_t handle;size_t capacity;};
    struct Hooks {
        std::function<Bits()> reserve_id;
        std::function<Bits(Bits,Bits)> combine;
        std::function<void(size_t,Bits,Bits)> expect;
        std::function<uint64_t(Bits,size_t)> retain;
        std::function<void()> checkpoint,terminal;
        std::function<Bits(Bits,Bits,size_t)> remask_outbox={};
        std::function<void(Bits)> require_private_status={};
    };
private:
    template<class C,class=void>struct HasDurable : std::false_type {};
    template<class C>struct HasDurable<C,std::void_t<decltype(std::declval<const C&>().durable())>> : std::true_type {};
    static bool durable(const Conversation& conversation){if constexpr(HasDurable<Conversation>::value)return conversation.durable();else return false;}
    struct Entry {std::unique_ptr<Conversation> conversation;Bits validity;bool pending=false;};
    struct Input {uint64_t owner;Bits payload,timestamp,validity;};
    struct Pending {uint64_t owner=0,ticket=0;};
    struct Outbox {uint64_t owner,ticket;Bits payload,request_id,validity;size_t capacity;};
    Hooks hooks;Bits credentials;std::map<uint64_t,Entry> entries;std::map<uint64_t,Input> inputs;
    std::map<uint64_t,Outbox> outboxes;uint64_t next_outbox=1;
    std::array<Pending,4> pending{};uint64_t next_input=1;bool active=false,closed=false;
    static void require(bool ok,const char* reason){if(!ok)throw std::runtime_error(reason);}
    void live()const{require(!closed,"private mux registry closed");}
    void fail()noexcept{close();try{hooks.terminal();}catch(...){}}
public:
    PrivateMuxRegistry(Hooks hooks,Bits computed_credential_validity):hooks(std::move(hooks)),credentials(std::move(computed_credential_validity)){
        require(credentials.size()==8&&this->hooks.reserve_id&&this->hooks.combine&&this->hooks.expect&&this->hooks.retain&&this->hooks.checkpoint&&this->hooks.terminal,"incomplete private mux admission");
    }
    ~PrivateMuxRegistry(){close();}
    PrivateMuxRegistry(const PrivateMuxRegistry&)=delete;
    PrivateMuxRegistry& operator=(const PrivateMuxRegistry&)=delete;
    uint64_t admit(std::unique_ptr<Conversation> conversation,Bits validity){
        try{live();require(!active&&conversation&&validity.size()==8&&entries.size()<4,"conversation admission rejected");
            require(!durable(*conversation)||bool(hooks.require_private_status),"durable status gate unavailable");
            auto id=entries.size()+1;entries.emplace(id,Entry{std::move(conversation),std::move(validity)});return id;
        }catch(...){fail();throw;}
    }
    uint64_t admit_input(uint64_t owner,Bits payload,Bits timestamp,Bits validity){
        try{live();require(!active&&entries.count(owner)&&payload.size()%8==0&&payload.size()<=16384*8&&timestamp.size()==64&&validity.size()==8&&inputs.size()<64&&next_input,"private conversation input rejected");
            auto id=next_input++;inputs.emplace(id,Input{owner,std::move(payload),std::move(timestamp),std::move(validity)});return id;
        }catch(...){fail();throw;}
    }
    uint64_t admit_outbox(uint64_t owner,uint64_t fresh_lease,Bits payload,Bits expected_id,Bits computed_resumability,size_t capacity){
        try{live();auto found=entries.find(owner);
            require(!active&&found!=entries.end()&&bool(hooks.remask_outbox)&&fresh_lease&&next_outbox&&outboxes.size()<4&&
                capacity==found->second.conversation->frame_capacity()&&capacity<=16384&&payload.size()==8*(capacity+3)&&expected_id.size()==64&&computed_resumability.size()==8,
                "restored outbox admission rejected");
            found->second.conversation->admit_pending_outbox(fresh_lease);
            auto handle=next_outbox++;outboxes.emplace(handle,Outbox{owner,fresh_lease,std::move(payload),std::move(expected_id),std::move(computed_resumability),capacity});return handle;
        }catch(...){fail();throw;}
    }
    Receipt resume_outbox(uint64_t owner,uint64_t outbox_handle){
        try{live();auto found=entries.find(owner);auto saved=outboxes.find(outbox_handle);
            require(active&&found!=entries.end()&&!found->second.pending&&saved!=outboxes.end()&&saved->second.owner==owner,"restored outbox resume rejected");
            size_t slot=0;while(slot<4&&pending[slot].owner)++slot;require(slot<4,"restored outbox queue full");
            auto outbox=std::move(saved->second);outboxes.erase(saved); // One-shot handle, including on uncertainty.
            found->second.conversation->resume_pending_outbox(outbox.ticket);
            found->second.pending=true;pending[slot]={owner,outbox.ticket};
            auto valid=hooks.combine(Bits(credentials),Bits(found->second.validity));valid=hooks.combine(std::move(valid),std::move(outbox.validity));
            auto encoded=hooks.remask_outbox(std::move(outbox.payload),std::move(valid),outbox.capacity);
            require(encoded.size()==8*(outbox.capacity+3),"restored outbox remask dimensions");
            Bits computed(encoded.begin(),encoded.begin()+8);
            hooks.expect(slot,std::move(outbox.request_id),std::move(computed));
            auto handle=hooks.retain(std::move(encoded),outbox.capacity);hooks.checkpoint();return{handle,outbox.capacity};
        }catch(...){fail();throw;}
    }
    void authenticated_connection_ready(){
        try{live();require(!active&&!entries.empty(),"private connection activation rejected");
            for(auto& item:entries)item.second.conversation->authenticated_connection_ready();active=true;
        }catch(...){fail();throw;}
    }
    Receipt produce(uint64_t owner,uint64_t input_handle){
        try{
            live();auto found=entries.find(owner);auto input_it=inputs.find(input_handle);
            require(active&&found!=entries.end()&&!found->second.pending&&input_it!=inputs.end()&&input_it->second.owner==owner,"private conversation send rejected");
            size_t slot=0;while(slot<4&&pending[slot].owner)++slot;require(slot<4,"private connection queue full");
            if(durable(*found->second.conversation)){
                auto accepted=hooks.combine(Bits(credentials),Bits(found->second.validity));
                accepted=hooks.combine(std::move(accepted),Bits(input_it->second.validity));
                require(accepted.size()==8,"invalid durable upstream validity");hooks.require_private_status(std::move(accepted));
            }
            auto input=std::move(input_it->second);inputs.erase(input_it);
            // Burn the global reservation before any producer state transition.
            auto id=hooks.reserve_id();require(id.size()==64,"invalid private ID reservation");auto expected=id;
            found->second.pending=true;pending[slot].owner=owner;
            auto result=found->second.conversation->produce(std::move(input.payload),std::move(input.timestamp),std::move(id));
            require(result.ticket&&result.capacity<=16384&&result.payload.size()==8*(result.capacity+3)&&result.request_id.size()==64,"invalid conversation result");
            pending[slot].ticket=result.ticket;
            Bits status(result.payload.begin(),result.payload.begin()+8);
            auto validity=hooks.combine(Bits(credentials),Bits(found->second.validity));
            validity=hooks.combine(std::move(validity),std::move(input.validity));validity=hooks.combine(std::move(validity),std::move(status));
            require(validity.size()==8,"invalid private validity gate");
            // Admission authenticates the computed validity before any normal
            // application record can be retained. Correlate the assigned ID.
            hooks.expect(slot,std::move(expected),Bits(validity));
            std::move(validity.begin(),validity.end(),result.payload.begin());
            auto handle=hooks.retain(std::move(result.payload),result.capacity);hooks.checkpoint();return{handle,result.capacity};
        }catch(...){fail();throw;}
    }
    std::vector<Receipt> produce_batch(const std::vector<std::pair<uint64_t,uint64_t>>& requests){
        try{
            live();require(active&&!requests.empty()&&requests.size()<=4,"private mux batch unavailable");
            std::vector<size_t> slots;
            for(size_t slot=0;slot<4;++slot)if(!pending[slot].owner)slots.push_back(slot);
            require(slots.size()>=requests.size(),"private batch queue full");
            for(size_t i=0;i<requests.size();++i){auto [owner,handle]=requests[i];auto found=entries.find(owner);auto input=inputs.find(handle);
                require(found!=entries.end()&&!found->second.pending&&input!=inputs.end()&&input->second.owner==owner,"private batch admission rejected");
                for(size_t j=0;j<i;++j)require(requests[j].first!=owner&&requests[j].second!=handle,"duplicate private batch conversation/input");}
            bool recovering=false;for(auto request:requests)recovering=recovering||durable(*entries.at(request.first).conversation);
            if(recovering){
                auto accepted=Bits(credentials);
                for(auto request:requests){accepted=hooks.combine(std::move(accepted),Bits(entries.at(request.first).validity));
                    accepted=hooks.combine(std::move(accepted),Bits(inputs.at(request.second).validity));}
                require(accepted.size()==8,"invalid durable batch upstream validity");hooks.require_private_status(std::move(accepted));
            }
            std::vector<Input> admitted;std::vector<Bits> expected;std::vector<typename Conversation::BatchRequest> batch;
            for(size_t i=0;i<requests.size();++i){auto [owner,handle]=requests[i];auto found=inputs.find(handle);admitted.push_back(std::move(found->second));inputs.erase(found);
                auto id=hooks.reserve_id();require(id.size()==64,"invalid private batch ID");expected.push_back(id);
                entries.at(owner).pending=true;pending[slots[i]].owner=owner;
                batch.push_back({entries.at(owner).conversation.get(),std::move(admitted.back().payload),std::move(admitted.back().timestamp),std::move(id)});}
            auto results=Conversation::produce_batch(std::move(batch));require(results.size()==requests.size(),"invalid private batch result count");
            for(size_t i=0;i<results.size();++i){auto& result=results[i];require(result.ticket&&result.capacity<=16384&&result.payload.size()==8*(result.capacity+3)&&result.request_id.size()==64,"invalid private batch result");pending[slots[i]].ticket=result.ticket;}
            std::vector<Receipt> receipts;receipts.reserve(results.size());
            for(size_t i=0;i<results.size();++i){auto& result=results[i];auto& entry=entries.at(requests[i].first);
                Bits status(result.payload.begin(),result.payload.begin()+8);
                auto valid=hooks.combine(Bits(credentials),Bits(entry.validity));valid=hooks.combine(std::move(valid),std::move(admitted[i].validity));valid=hooks.combine(std::move(valid),std::move(status));
                require(valid.size()==8,"invalid private batch validity");hooks.expect(slots[i],std::move(expected[i]),Bits(valid));
                std::move(valid.begin(),valid.end(),result.payload.begin());receipts.push_back({hooks.retain(std::move(result.payload),result.capacity),result.capacity});}
            hooks.checkpoint();return receipts; // Nothing released until whole batch barrier succeeds.
        }catch(...){fail();throw;}
    }
    uint64_t authenticated_response_complete(size_t slot){
        try{live();require(active&&slot<4&&pending[slot].owner&&pending[slot].ticket,"stale private completion slot");
            auto selected=pending[slot];auto& entry=entries.at(selected.owner);require(entry.pending,"private completion ownership rejected");
            entry.conversation->authenticated_response_complete(selected.ticket);entry.pending=false;pending[slot]={};return selected.owner;
        }catch(...){fail();throw;}
    }
    void close()noexcept{closed=true;active=false;inputs.clear();outboxes.clear();credentials.clear();pending.fill({});
        for(auto& item:entries)item.second.conversation->close();entries.clear();}
};
}
