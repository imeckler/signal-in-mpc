#pragma once
#include "NativeWorker.h"
#include <algorithm>
#include <array>
#include <fstream>
namespace tls_mpc_worker {
// Four opaque correlation slots. Only authenticated completion slot numbers
// leave the circuit; IDs, status codes, lengths and response content stay shared.
class NativeChatMux {
    Worker& worker;Bits state;std::array<bool,4> occupied{};bool closed=false;
    static constexpr size_t state_bytes=982,slot_offset=933,queue_offset=977;
    void live() const {public_require(!closed,"private response mux closed");}
public:
    struct Event {Bits body,body_reset,header;};
    template<class PublicBits> NativeChatMux(Worker& worker,const PinnedPrograms& pinned,PublicBits&& share):worker(worker) {
        const std::string path="Worker-Public/chat-mux-initial.bin";pinned.verify_public(path);
        std::ifstream stream(path,std::ios::binary);PublicBytes initial((std::istreambuf_iterator<char>(stream)),{});
        public_require(initial.size()==state_bytes,"invalid pinned mux codec");state=share(initial);
    }
    bool pending() const {return std::any_of(occupied.begin(),occupied.end(),[](bool value){return value;});}
    template<class PublicBits,class Release> void admit(size_t slot,Bits id,Bits computed_validity,PublicBits&& share,Release&& release) {
        try {
            live();public_require(slot<4&&!occupied[slot]&&id.size()==64&&computed_validity.size()==8,"private response slot unavailable");
            Bits input(state);auto index=share(PublicBytes{static_cast<uint8_t>(slot)});
            input.insert(input.end(),index.begin(),index.end());input.insert(input.end(),id.begin(),id.end());
            input.insert(input.end(),computed_validity.begin(),computed_validity.end());
            state=worker.binary("tls-chat-mux-admit-4",std::move(input),state_bytes*8);
            public_require(release(Bits(state.begin(),state.begin()+8))==PublicBytes{255},"private response admission rejected");occupied[slot]=true;
        }catch(...){close();throw;}
    }
    Event step(Bits active,Bits beginning,Bits ending,Bits byte) {
        try {
            live();for(const auto* part:{&active,&beginning,&ending,&byte})public_require(part->size()==8,"invalid mux byte dimensions");
            Bits input(state);for(const auto* part:{&active,&beginning,&ending,&byte})input.insert(input.end(),part->begin(),part->end());
            auto out=worker.binary("tls-chat-mux-byte-4096-4",std::move(input),8*(state_bytes+3));
            state=Bits(out.begin(),out.begin()+8*state_bytes);
            auto field=[&](size_t i){return Bits(out.begin()+8*i,out.begin()+8*(i+1));};
            return{field(state_bytes),field(state_bytes+1),field(state_bytes+2)};
        }catch(...){close();throw;}
    }
    // Call only after authenticated frame validity. No caller may acknowledge
    // a provider until its enclosing receive host cleanup barrier has passed.
    template<class Release,class PublicBits> PublicBytes finish_chunk(Release&& release,PublicBits&& share) {
        try {
            live();public_require(release(Bits(state.begin(),state.begin()+8))==PublicBytes{255},"private response/correlation rejected");
            auto queue=release(Bits(state.begin()+8*queue_offset,state.end()));
            public_require(queue.size()==5&&queue[0]<=4,"invalid private response completion queue");
            std::array<bool,4> seen{};PublicBytes result;
            for(size_t i=0;i<4;++i){
                auto code=queue[i+1];if(i>=queue[0]){public_require(code==0,"noncanonical response queue");continue;}
                public_require(code>=1&&code<=4&&occupied[code-1]&&!seen[code-1],"stale/duplicate response completion");
                seen[code-1]=true;result.push_back(code-1);
            }
            for(auto slot:result){auto zero=share(PublicBytes(11,0));std::move(zero.begin(),zero.end(),state.begin()+8*(slot_offset+11*slot));occupied[slot]=false;}
            auto zero=share(PublicBytes(5,0));std::move(zero.begin(),zero.end(),state.begin()+8*queue_offset);return result;
        }catch(...){close();throw;}
    }
    void close() noexcept {closed=true;state.clear();occupied.fill(false);}
};
}
