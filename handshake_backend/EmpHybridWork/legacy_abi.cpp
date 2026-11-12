// The legacy library behind engine_abi.h (REORGANIZATION_PLAN.md stage S8): today's
// `Worker::dispatch` for the operations that are not the shell's, until each one moves to a
// Lean script (S9-S16; this file is deleted in S16).
//
// FACTORED, NOT COPIED. The sequencing code is tls_worker_v3.cpp's own `Worker`, included
// below unchanged, so the tls-worker-fixture-v3 / tls-worker-sh-fixture-v3 binaries and this
// library run the same source. What this file leaves out is the shell, which the Rust worker
// (node_worker/) now is: the pipe loop, the environment, the server socket and SOCKS, the
// record forwarding, the exchange (39) and the connection table's sockets. Those operations
// are refused here (`legacy_operation`), so their C++ code, though compiled in with the rest
// of tls_worker_v3.cpp, cannot be reached through the ABI.
//
// One known redundancy until tls_worker_v3.cpp may change (design note in node_worker/src/lib.rs):
// `Worker::dispatch` begins every request with its own agreement on the Boolean engine's
// channel. The Rust shell has already agreed the same request on the control link, so a
// forwarded operation is agreed twice (one extra message delay each). Both agreements hash the
// same frame; neither changes what is computed.
//
// Compiled only as part of engine_abi.cpp (one translation unit; see there).
#ifndef EMP_HYBRID_ENGINE_ABI_TU
#error "legacy_abi.cpp is compiled as part of engine_abi.cpp"
#endif
// Everything tls_worker_v3.cpp includes, first: the `main` rename below must reach that file's
// own text only, never a header.
#include "service_kernels.h"
#include "big_stack.h"
#include "peer_link.h"
#include <cerrno>
#include <csignal>
#include <chrono>
#include <iostream>
#include <deque>
#include <netdb.h>
#include <poll.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <unistd.h>
// tls_worker_v3.cpp's entry point becomes an ordinary function that nothing calls.
#define main emp_hybrid_tls_worker_v3_entry_unused
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-function"
#include "tls_worker_v3.cpp"
#pragma clang diagnostic pop
#undef main

namespace engine_abi {
// The operations this library serves: 1-7 (handshake), 12-16 (records, keys), 30, 32, 33,
// 36-38 and 40-66 (contacts, account, receive, refresh, send), 80, 81 (ceremony).
// Not here: the shell's 8, 9, 10, 11, 17, 39, 90, 91 (Rust), and the retired fixture and
// private-profile operations 18-29, 31, 34, 35 and the TEST producer, which no one forwards.
inline bool legacy_operation(uint8_t code){
    return (code>=1&&code<=7)||(code>=12&&code<=16)||code==30||code==32||code==33||(code>=36&&code<=38)||
           (code>=40&&code<=66)||code==80||code==81;
}
struct LegacyState {
    std::string session;emp_hybrid::TlsKernels kernels;emp_hybrid::ServiceKernels service;Worker worker;
    LegacyState(ea_session&s,const ea_legacy_config&c)
        :session(c.session),kernels(*s.mpc,*s.field,*s.channel,s.party,c.cache_script?c.cache_script:""),service(kernels),
         worker{s.party,*s.io,*s.channel,kernels,session}{
        // As tls_worker_v3.cpp's `run`, in its order: the first conversion masks, then the settings.
        kernels.prepare();
        worker.peer_wait_ms=c.peer_wait_seconds*1000;
        kernels.ladder_agreement=c.ladder_agreement!=0;kernels.typed_open=c.typed_open!=0;
        worker.service=&service;service.hinted=c.hinted!=0;
    }
};
void LegacyDeleter::operator()(LegacyState*state)const{delete state;}
LegacyState&legacy(ea_session*s){need(s&&s->legacy,"legacy library not open");return *s->legacy;}
}

extern "C" {
int ea_legacy_open(ea_session*s,const ea_legacy_config*config){
    using namespace engine_abi;
    return guard([&]{
        need(s&&config&&config->session&&!s->legacy,"legacy arguments");
        need(config->peer_wait_seconds>=0&&config->peer_wait_seconds<=86400,"peer wait");
        // Strict mode (kernel.h, CIRCUIT_MANIFEST) is decided by the kernel cache from the
        // environment. The production library refuses to run without it: no kernel can then
        // ever be produced on demand. (The unpinned path stays compiled in, unreachable.)
        const bool require=config->require_pinned!=0||!engine_abi_test_build;
        auto state=std::make_unique<LegacyState>(*s,*config);
        need(!require||state->kernels.cache.pinned(),"strict circuit loading required: CIRCUIT_MANIFEST is not set");
        s->legacy.reset(state.release());
    });
}
int ea_legacy_dispatch(ea_session*s,uint8_t code,uint64_t sequence,const uint8_t*payload,size_t len,ea_bytes*out){
    using namespace engine_abi;
    return guard([&]{
        need(out&&(len==0||payload),"dispatch arguments");out->data=nullptr;out->len=0;
        need(legacy_operation(code),"not a legacy operation");
        auto reply=legacy(s).worker.call(code,sequence,std::vector<uint8_t>(payload,payload+len));
        if(!reply.empty()){
            out->data=static_cast<uint8_t*>(std::malloc(reply.size()));need(out->data!=nullptr,"reply allocation");
            std::memcpy(out->data,reply.data(),reply.size());out->len=reply.size();
        }
    });
}
int ea_legacy_select(ea_session*s,uint64_t index){
    using namespace engine_abi;
    return guard([&]{need(index<64,"connection index");legacy(s).worker.select(size_t(index));});
}
int ea_legacy_reset(ea_session*s){
    using namespace engine_abi;
    return guard([&]{
        // Operation 91 without its socket half (the Rust shell checked that the connection was
        // reported closed): only a retired connection is replaced, by a fresh one.
        auto&w=legacy(s).worker;need(w.service&&w.server<0&&w.phase==Worker::Phase::retired,"reset connection");
        Worker::Connection fresh;w.exchange(fresh);
    });
}
int ea_legacy_abort(ea_session*s){
    using namespace engine_abi;
    return guard([&]{auto&state=legacy(s);state.kernels.abort();state.worker.drop_connections();});
}
}   // extern "C"
