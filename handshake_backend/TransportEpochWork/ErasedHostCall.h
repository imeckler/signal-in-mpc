#pragma once
#include "Tools/ErasingThreadStack.h"
#include <openssl/crypto.h>
#include <type_traits>
#include <cstdlib>

namespace tls_mpc_worker {
// Serialize heap-owned MPC state in the caller. Every host action, including
// bootstrap/destruction, runs on a fresh owned stack. Reply only after run()
// returns: thread-local destructors and complete stack erasure precede it.
class ErasedHostCall {
    static inline thread_local bool active_=false;
public:
    static bool active() noexcept {return active_;}
    template<class F> static bool run(F&& operation) {
        if(active_)throw std::runtime_error("nested erased host call");
        using Function=std::remove_reference_t<F>;
        struct Job {
            Function* operation; bool failed=false;
            static void* entry(void* pointer) {
                auto& job=*static_cast<Job*>(pointer);
                active_=true;
                try {(*job.operation)();} catch(...) {job.failed=true;}
                OPENSSL_thread_stop();
                active_=false;
                return nullptr;
            }
        } job{&operation};
        ErasingThreadStack stack;
        pthread_t thread;
        if(stack.start(&thread,Job::entry,&job))
            throw std::runtime_error("cannot start erased host call");
        // Never unmap a possibly running thread's stack after a failed join.
        if(pthread_join(thread,nullptr))std::abort();
        return !job.failed;
    }
};
}
