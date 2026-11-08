#pragma once
#include <array>
#include <cstdint>
#include <utility>
#include <map>
#include <memory>
#include <functional>
#include <stdexcept>
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
    };
private:
    struct Entry {std::unique_ptr<Conversation> conversation;Bits validity;bool pending=false;};
    struct Input {uint64_t owner;Bits payload,timestamp,validity;};
    struct Pending {uint64_t owner=0,ticket=0;};
    Hooks hooks;Bits credentials;std::map<uint64_t,Entry> entries;std::map<uint64_t,Input> inputs;
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
            auto id=entries.size()+1;entries.emplace(id,Entry{std::move(conversation),std::move(validity)});return id;
        }catch(...){fail();throw;}
    }
    uint64_t admit_input(uint64_t owner,Bits payload,Bits timestamp,Bits validity){
        try{live();require(!active&&entries.count(owner)&&payload.size()%8==0&&payload.size()<=16384*8&&timestamp.size()==64&&validity.size()==8&&inputs.size()<64&&next_input,"private conversation input rejected");
            auto id=next_input++;inputs.emplace(id,Input{owner,std::move(payload),std::move(timestamp),std::move(validity)});return id;
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
    uint64_t authenticated_response_complete(size_t slot){
        try{live();require(active&&slot<4&&pending[slot].owner&&pending[slot].ticket,"stale private completion slot");
            auto selected=pending[slot];auto& entry=entries.at(selected.owner);require(entry.pending,"private completion ownership rejected");
            entry.conversation->authenticated_response_complete(selected.ticket);entry.pending=false;pending[slot]={};return selected.owner;
        }catch(...){fail();throw;}
    }
    void close()noexcept{closed=true;active=false;inputs.clear();credentials.clear();pending.fill({});
        for(auto& item:entries)item.second.conversation->close();entries.clear();}
};
}
