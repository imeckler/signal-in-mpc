#pragma once
#include "NativeWorker.h"
#include <fstream>
namespace tls_mpc_worker {
class NativeFrame {
    Worker& worker;size_t capacity;Bits state,status;bool closed=false,messages_allowed=true;
public:
    struct Event {Bits data,control,message_start,frame_done,message_done,control_done,control_kind;};
    template<class PublicBits> NativeFrame(Worker& worker,const PinnedPrograms& pinned,size_t capacity,PublicBits&& share)
      :worker(worker),capacity(capacity) {
        public_require(capacity<=65535,"invalid public frame profile");
        auto path="Worker-Public/tls-websocket-frame-v2-"+std::to_string(capacity)+"-initial.bin";
        pinned.verify_public(path);std::ifstream stream(path,std::ios::binary);
        PublicBytes initial((std::istreambuf_iterator<char>(stream)),{});
        public_require(initial.size()==26,"invalid pinned frame state");state=share(initial);
    }
    Event step(Bits active,Bits byte) {
        try {
            public_require(!closed&&active.size()==8&&byte.size()==8,"invalid frame byte request");
            Bits input;input.insert(input.end(),state.begin(),state.end());
            input.insert(input.end(),active.begin(),active.end());input.insert(input.end(),byte.begin(),byte.end());
            auto stem=messages_allowed?"tls-websocket-frame-v2-":"tls-websocket-frame-idle-v2-";
            auto out=worker.binary(stem+std::to_string(capacity),std::move(input),272);
            auto field=[&](size_t i){return Bits(out.begin()+8*i,out.begin()+8*(i+1));};
            status=field(0);Event event{field(1),field(2),field(3),field(4),field(5),field(6),field(7)};
            state=Bits(out.begin()+64,out.end());return event;
        } catch(...) {close();throw;}
    }
    void allow_messages(bool allowed) {public_require(!closed,"terminal frame policy");messages_allowed=allowed;}
    template<class Release> void finish_chunk(Release&& release) {
        try {public_require(!closed&&status.size()==8&&release(status)==PublicBytes{255},"WebSocket frame rejected");}
        catch(...) {close();throw;}
    }
    void close() noexcept {closed=true;state.clear();status.clear();}
};
}
