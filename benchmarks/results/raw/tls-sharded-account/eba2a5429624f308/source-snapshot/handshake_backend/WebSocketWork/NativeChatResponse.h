#pragma once
#include "NativeWorker.h"
#include <fstream>
namespace tls_mpc_worker {
// First integration profile: exactly one expected opaque request ID. A future
// multiplexed embedding must maintain bounded private correlation slots and
// per-conversation ordering; this class is not a connection throughput policy.
class NativeChatResponse {
    Worker& worker;size_t capacity;Bits state,status;bool closed=false;
public:
    static constexpr size_t state_bytes=932,expected_offset=891;
    struct Event {Bits body,body_reset,header;};
    struct Result {bool complete,successful;};
    template<class PublicBits> NativeChatResponse(Worker& worker,const PinnedPrograms& pinned,
      size_t capacity,Bits expected,PublicBits&& share):worker(worker),capacity(capacity) {
        public_require(capacity<=65535&&expected.size()==64,"invalid private response profile/ID");
        auto path="Worker-Public/tls-chat-response-"+std::to_string(capacity)+"-initial.bin";
        pinned.verify_public(path);std::ifstream stream(path,std::ios::binary);
        PublicBytes initial((std::istreambuf_iterator<char>(stream)),{});
        public_require(initial.size()==state_bytes+4&&size_t(initial[0])*256+initial[1]==state_bytes&&
          size_t(initial[2])*256+initial[3]==expected_offset,"invalid pinned chat codec");
        state=share(PublicBytes(initial.begin()+4,initial.end()));
        for(size_t i=0;i<64;++i)state[8*expected_offset+i]=std::move(expected[i]);
    }
    Event step(Bits active,Bits beginning,Bits ending,Bits byte) {
        try {
            public_require(!closed&&active.size()==8&&beginning.size()==8&&ending.size()==8&&byte.size()==8,"invalid chat byte request");
            Bits input;input.insert(input.end(),state.begin(),state.end());
            for(const auto* field:{&active,&beginning,&ending,&byte})input.insert(input.end(),field->begin(),field->end());
            auto out=worker.binary("tls-chat-response-"+std::to_string(capacity),std::move(input),8*(state_bytes+6));
            status=Bits(out.begin(),out.begin()+24);
            auto field=[&](size_t i){return Bits(out.begin()+8*i,out.begin()+8*(i+1));};
            Event event{field(3),field(4),field(5)};
            state=Bits(out.begin()+48,out.end());return event;
        } catch(...) {close();throw;}
    }
    // Explicit declassification: valid/correlated, message-complete and 2xx.
    // No request ID, numeric status, body/header bytes or lengths are opened.
    template<class Release> Result finish_chunk(Release&& release) {
        try {
            public_require(!closed&&status.size()==24,"missing private response status");
            auto result=release(status);
            public_require(result.size()==3&&result[0]==255&&(result[1]==0||result[1]==255)&&
              (result[2]==0||result[2]==255)&&(result[1]==255||result[2]==0),"private response/correlation rejected");
            return {result[1]==255,result[2]==255};
        } catch(...) {close();throw;}
    }
    void close() noexcept {closed=true;state.clear();status.clear();}
};
}
