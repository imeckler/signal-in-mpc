#pragma once
#include "Tools/ErasingThreadStack.h"
#include <openssl/crypto.h>
#include <type_traits>
#include <cstdlib>
#include <mutex>
#include <atomic>
#include <cstdint>

namespace tls_mpc_worker {
// Serialize heap-owned MPC state in the caller. Every host action, including
// bootstrap/destruction, runs on a fresh owned stack. Reply only after run()
// returns: thread-local destructors and complete stack erasure precede it.
class ErasedHostCall {
    static inline thread_local uint64_t current_=0;
    static inline std::atomic<uint64_t> completed_{0};
    static inline uint64_t next_=0;
    static inline std::mutex exclusive_;
public:
    static bool active() noexcept {return current_!=0;}
    static uint64_t generation() noexcept {return current_;}
    static bool completed(uint64_t generation) noexcept {return generation && completed_.load()>=generation;}
    template<class F> static bool run(F&& operation) {
        if(active())throw std::runtime_error("nested erased host call");
        std::lock_guard<std::mutex> lock(exclusive_);
        if(next_==UINT64_MAX)throw std::runtime_error("host call generation exhausted");
        using Function=std::remove_reference_t<F>;
        struct Job {
            Function* operation; uint64_t generation; bool failed=false;
            static void* entry(void* pointer) {
                auto& job=*static_cast<Job*>(pointer);
                current_=job.generation;
                try {(*job.operation)();} catch(...) {job.failed=true;}
                OPENSSL_thread_stop();
                current_=0;
                return nullptr;
            }
        } job{&operation,++next_};
        {
        ErasingThreadStack stack;
        pthread_t thread;
        if(stack.start(&thread,Job::entry,&job))
            throw std::runtime_error("cannot start erased host call");
        // Never unmap a possibly running thread's stack after a failed join.
        if(pthread_join(thread,nullptr))std::abort();
        } // Entire stack mapping is wiped before publishing completion.
        completed_.store(job.generation);
        return !job.failed;
    }
};
}
