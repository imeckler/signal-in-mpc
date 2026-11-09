#pragma once
#include "NativeUpgradeResponse.h"
#include "NativeFrame.h"
#include "NativeControlQueue.h"
#include "NativeChatResponse.h"
#include <memory>
namespace tls_mpc_worker {
// Bounded first integration profile. Correlation IDs and all payload bytes stay
// shared. Public decisions are upgrade/response completion and control kinds.
class NativeWebSocket {
    Worker& worker;const PinnedPrograms& pinned;
    std::unique_ptr<NativeUpgradeResponse> upgrade;
    NativeFrame frame;NativeControlQueue controls;
    std::unique_ptr<NativeChatResponse> response;
    bool upgraded=false,closed=false;
public:
    struct Control {unsigned kind;Bits payload;};
    struct Result {bool upgraded,response_complete;std::vector<Control> controls;};
    template<class PublicBits> NativeWebSocket(Worker& worker,const PinnedPrograms& pinned,
      const PublicBytes& accept,PublicBits&& share):worker(worker),pinned(pinned),
      upgrade(new NativeUpgradeResponse(worker,pinned,accept,share)),
      frame(worker,pinned,4096,share),controls(worker,pinned,share) {frame.allow_messages(false);}
    template<class PublicBits> void expect(Bits id,PublicBits&& share) {
        public_require(!closed&&upgraded&&!response,"WebSocket response slot unavailable");
        response.reset(new NativeChatResponse(worker,pinned,4096,std::move(id),share));
        frame.allow_messages(true);
    }
    template<class Release,class PublicBits> Result feed(PrivatePayload chunk,Release&& release,PublicBits&& share) {
        try {
            public_require(!closed&&chunk.capacity>0&&chunk.capacity<=128,"unsupported WebSocket receive profile");
            auto consume=[&](Bits byte,Bits active) {
                auto event=frame.step(std::move(active),Bits(byte));
                controls.step(std::move(event.control),std::move(event.control_done),std::move(event.control_kind),Bits(byte));
                if(response)response->step(std::move(event.data),std::move(event.message_start),std::move(event.message_done),std::move(byte));
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
            frame.finish_chunk(release);bool complete=false;
            if(response) {
                auto decision=response->finish_chunk(release);
                public_require(!decision.complete||decision.successful,"service response rejected");
                complete=decision.complete;
                if(complete){response->close();response.reset();frame.allow_messages(false);}
            }
            auto kinds=controls.finish_chunk(release);Result result{upgraded,complete,{}};
            for(size_t i=0;i<kinds.size();++i){result.controls.push_back({kinds[i],controls.take(i,share)});if(kinds[i]==8)closed=true;}
            controls.clear_queued(share);return result;
        } catch(...) {close();throw;}
    }
    void close() noexcept {
        closed=true;if(upgrade){upgrade->close();upgrade.reset();}
        if(response){response->close();response.reset();}frame.close();controls.close();
    }
};
}
