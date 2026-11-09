#pragma once
#include "NativeUpgradeResponse.h"
#include "NativeFrame.h"
#include "NativeControlQueue.h"
#include "NativeChatMux.h"
#include <memory>
namespace tls_mpc_worker {
// Four bounded outstanding opaque slots, one stream parser. Completion slot
// metadata is released only after authenticated frame and correlation validity.
class NativeWebSocketMux {
    Worker& worker;
    std::unique_ptr<NativeUpgradeResponse> upgrade;
    NativeFrame frame;NativeControlQueue controls;
    NativeChatMux response;
    bool upgraded=false,closed=false;
public:
    struct Control {unsigned kind;Bits payload;};
    struct Result {bool upgraded;PublicBytes completed_slots;std::vector<Control> controls;};
    template<class PublicBits> NativeWebSocketMux(Worker& worker,const PinnedPrograms& pinned,
      const PublicBytes& accept,PublicBits&& share):worker(worker),
      upgrade(new NativeUpgradeResponse(worker,pinned,accept,share)),
      frame(worker,pinned,4096,share),controls(worker,pinned,share),response(worker,pinned,share) {frame.allow_messages(false);}
    template<class PublicBits,class Release> void expect(size_t slot,Bits id,Bits validity,PublicBits&& share,Release&& release) {
        public_require(!closed&&upgraded,"WebSocket correlation admission unavailable");
        response.admit(slot,std::move(id),std::move(validity),share,release);frame.allow_messages(true);
    }
    template<class Release,class PublicBits> Result feed(PrivatePayload chunk,Release&& release,PublicBits&& share) {
        try {
            public_require(!closed&&chunk.capacity>0&&chunk.capacity<=128,"unsupported WebSocket receive profile");
            auto consume=[&](Bits byte,Bits active) {
                auto event=frame.step(std::move(active),Bits(byte));
                controls.step(std::move(event.control),std::move(event.control_done),std::move(event.control_kind),Bits(byte));
                if(response.pending())response.step(std::move(event.data),std::move(event.message_start),std::move(event.message_done),std::move(byte));
            };
            if(upgrade) {
                upgraded=upgrade->feed(std::move(chunk),release,consume);
                if(upgraded){upgrade->close();upgrade.reset();}
            } else {
                chunk.validate_shape();Bits input(chunk.validity);
                input.insert(input.end(),chunk.private_length.begin(),chunk.private_length.end());
                auto masks=worker.binary("tls-websocket-activity-"+std::to_string(chunk.capacity),std::move(input),8*(chunk.capacity+1));
                public_require(release(Bits(masks.begin(),masks.begin()+8))==PublicBytes{255},"invalid private receive chunk");
                for(size_t i=0;i<chunk.capacity;++i)consume(Bits(chunk.data.begin()+8*i,chunk.data.begin()+8*(i+1)),
                  Bits(masks.begin()+8*(i+1),masks.begin()+8*(i+2)));
            }
            frame.finish_chunk(release);PublicBytes completed;
            if(response.pending())completed=response.finish_chunk(release,share);
            frame.allow_messages(response.pending());
            auto kinds=controls.finish_chunk(release);Result result{upgraded,std::move(completed),{}};
            for(size_t i=0;i<kinds.size();++i){result.controls.push_back({kinds[i],controls.take(i,share)});if(kinds[i]==8)closed=true;}
            controls.clear_queued(share);
            // Only the encoded close reply escapes. Drop parser, correlation
            // and partial-control state before the caller's retirement barrier.
            if(closed){if(upgrade){upgrade->close();upgrade.reset();}response.close();frame.close();controls.close();}
            return result;
        } catch(...) {close();throw;}
    }
    void close() noexcept {
        closed=true;if(upgrade){upgrade->close();upgrade.reset();}
        response.close();frame.close();controls.close();
    }
};
}
