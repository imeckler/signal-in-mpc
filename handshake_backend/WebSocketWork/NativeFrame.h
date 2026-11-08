#pragma once
#include "NativeWorker.h"
#include <fstream>
namespace tls_mpc_worker {
class NativeFrame {
    Worker& worker;size_t capacity;Bits state,status;bool closed=false;
public:
    struct Event {Bits data,control,message_start,frame_done,message_done,control_done;};
    template<class PublicBits> NativeFrame(Worker& worker,const PinnedPrograms& pinned,size_t capacity,PublicBits&& share)
      :worker(worker),capacity(capacity) {
        public_require(capacity<=65535,"invalid public frame profile");
        auto path="Worker-Public/tls-websocket-frame-"+std::to_string(capacity)+"-initial.bin";
        pinned.verify_public(path);std::ifstream stream(path,std::ios::binary);
        PublicBytes initial((std::istreambuf_iterator<char>(stream)),{});
        public_require(initial.size()==26,"invalid pinned frame state");state=share(initial);
    }
    Event step(Bits active,Bits byte) {
        try {
            public_require(!closed&&active.size()==8&&byte.size()==8,"invalid frame byte request");
            Bits input;input.insert(input.end(),state.begin(),state.end());
            input.insert(input.end(),active.begin(),active.end());input.insert(input.end(),byte.begin(),byte.end());
            auto out=worker.binary("tls-websocket-frame-"+std::to_string(capacity),std::move(input),264);
            auto field=[&](size_t i){return Bits(out.begin()+8*i,out.begin()+8*(i+1));};
            status=field(0);Event event{field(1),field(2),field(3),field(4),field(5),field(6)};
            state=Bits(out.begin()+56,out.end());return event;
        } catch(...) {close();throw;}
    }
    template<class Release> void finish_chunk(Release&& release) {
        try {public_require(!closed&&status.size()==8&&release(status)==PublicBytes{255},"WebSocket frame rejected");}
        catch(...) {close();throw;}
    }
    void close() noexcept {closed=true;state.clear();status.clear();}
};
}
