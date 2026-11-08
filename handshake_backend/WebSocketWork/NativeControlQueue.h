#pragma once
#include "NativeWorker.h"
#include <array>
#include <fstream>
namespace tls_mpc_worker {
class NativeControlQueue {
    Worker& worker;Bits state;bool closed=false,ready=false;size_t announced=0;
    std::array<bool,4> taken{};
public:
    template<class PublicBits> NativeControlQueue(Worker& worker,const PinnedPrograms& pinned,PublicBits&& share):worker(worker) {
        const std::string path="Worker-Public/websocket-control-initial.bin";pinned.verify_public(path);
        std::ifstream stream(path,std::ios::binary);PublicBytes initial((std::istreambuf_iterator<char>(stream)),{});
        public_require(initial.size()==636,"invalid pinned control state");state=share(initial);
    }
    void step(Bits data,Bits done,Bits opcode,Bits byte) {
        try {
            public_require(!closed&&!ready&&data.size()==8&&done.size()==8&&opcode.size()==8&&byte.size()==8,"invalid control byte request");
            Bits input;input.insert(input.end(),state.begin(),state.end());
            for(const auto* field:{&data,&done,&opcode,&byte})input.insert(input.end(),field->begin(),field->end());
            state=worker.binary("tls-websocket-control-collect",std::move(input),636*8);
        } catch(...) {close();throw;}
    }
    // Explicit protocol metadata declassification, after the frame layer's
    // authenticated validity gate. Actual control lengths/payloads stay shared.
    template<class Release> PublicBytes finish_chunk(Release&& release) {
        try {
            public_require(!closed&&!ready,"terminal/pending control queue");
            Bits valid(state.begin(),state.begin()+8);
            public_require(release(valid)==PublicBytes{255},"private controls rejected");
            Bits metadata(state.begin()+127*8,state.begin()+132*8);
            auto out=release(metadata);public_require(out.size()==5&&out[0]<=4,"invalid control queue metadata");
            announced=out[0];
            for(size_t i=0;i<4;++i)public_require(i<announced?(out[i+1]==8||out[i+1]==10):out[i+1]==0,"invalid private control kind");
            ready=true;taken.fill(false);return PublicBytes(out.begin()+1,out.begin()+1+announced);
        } catch(...) {close();throw;}
    }
    template<class PublicBits> Bits take(size_t index,PublicBits&& share) {
        try {
            public_require(!closed&&ready&&index<announced&&!taken[index],"invalid/replayed control response");taken[index]=true;
            Bits input(state.begin(),state.begin()+8);auto high=share(PublicBytes{0});input.insert(input.end(),high.begin(),high.end());
            input.insert(input.end(),state.begin()+8*(132+index),state.begin()+8*(133+index));
            input.insert(input.end(),state.begin()+8*(128+index),state.begin()+8*(129+index));
            input.insert(input.end(),state.begin()+8*(136+125*index),state.begin()+8*(136+125*(index+1)));
            // The pinned wrapper generates32 fresh joint mask bits in the VM.
            return worker.binary("tls-websocket-control-encode-125",std::move(input),134*8);
        } catch(...) {close();throw;}
    }
    template<class PublicBits> void clear_queued(PublicBits&& share) {
        public_require(!closed&&ready,"control queue not drained");
        for(size_t i=0;i<announced;++i)public_require(taken[i],"unconsumed private control response");
        Bits next(state.begin(),state.begin()+127*8);auto zero=share(PublicBytes(509,0));next.insert(next.end(),zero.begin(),zero.end());
        state=std::move(next);ready=false;announced=0;taken.fill(false);
    }
    void close() noexcept {closed=true;state.clear();ready=false;announced=0;taken.fill(false);}
};
}
