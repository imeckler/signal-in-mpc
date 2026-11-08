#pragma once
#include "NativeWorker.h"
#include <fstream>
#include <functional>
namespace tls_mpc_worker {
// Internal same-worker byte machine. Frame processing consumes the returned
// shared activity mask together with the original private byte. Only public
// protocol validity/completion may be authenticated/released at chunk boundaries.
class NativeUpgradeResponse {
    Worker& worker;
    Bits state,expected,status;
    size_t slots=0;
    bool completed=false,closed=false;
public:
    static constexpr size_t state_bytes=180;
    template<class PublicBits>
    NativeUpgradeResponse(Worker& worker,const PinnedPrograms& pinned,const PublicBytes& accept,PublicBits&& share)
        :worker(worker) {
        public_require(accept.size()==28,"invalid public WebSocket accept shape");
        const std::string path="Worker-Public/websocket-initial-state.bin";
        pinned.verify_public(path);std::ifstream input(path,std::ios::binary);
        PublicBytes initial((std::istreambuf_iterator<char>(input)),{});
        public_require(initial.size()==state_bytes,"invalid pinned upgrade state shape");
        state=share(initial);expected=share(accept);
    }
    Bits step(Bits active,Bits byte) {
        try {
        public_require(!closed&&active.size()==8&&byte.size()==8,"invalid upgrade byte request");
        // Count public work slots, never the actual private header length. The
        // 64KiB pre-upgrade profile permits ordinary/padded TLS record chunks.
        public_require(completed||slots<65536,"upgrade public work budget exhausted");++slots;
        Bits input;input.insert(input.end(),state.begin(),state.end());
        input.insert(input.end(),expected.begin(),expected.end());
        input.insert(input.end(),active.begin(),active.end());input.insert(input.end(),byte.begin(),byte.end());
        auto out=worker.binary("tls-websocket-upgrade-byte",std::move(input),8*(state_bytes+3));
        status=Bits(out.begin(),out.begin()+16);
        Bits forwarded(out.begin()+16,out.begin()+24);
        state=Bits(out.begin()+24,out.end());return forwarded;
        } catch(...) {close();throw;}
    }
    template<class Release> bool finish_chunk(Release&& release) {
        public_require(!closed&&status.size()==16,"missing upgrade status");
        try {
            auto result=release(status);
            public_require(result.size()==2&&result[0]==255&&(result[1]==0||result[1]==255),"WebSocket upgrade rejected");
            public_require(!completed||result[1]==255,"WebSocket upgrade completion regressed");
            completed=result[1]==255;return completed;
        } catch(...) {close();throw;}
    }
    void close() noexcept {closed=true;state.clear();expected.clear();status.clear();}
};
}
