#pragma once
#include <gmp.h>
#include <sodium.h>
#include <cstring>
#include <cstdlib>
#include <mutex>
#include <atomic>
#include <algorithm>

namespace tls_mpc_worker {
// Install on the exclusive startup thread, before starting MPC threads. No
// GMP objects may already own allocated storage at installation (GMP API
// precondition). The captured policy supplies raw allocation; no headers are
// added. Do not replace GMP hooks again after install.
class SecureGmp {
    static inline void* (*previous_allocate)(size_t)=nullptr;
    static inline void* (*previous_reallocate)(void*,size_t,size_t)=nullptr;
    static inline void (*previous_free)(void*,size_t)=nullptr;
    static inline std::once_flag once;
    static void* allocate(size_t n) {
        auto result=previous_allocate(n);
        if(!result) std::abort(); // GMP callbacks must never return failure.
        return result;
    }
    static void release(void* p,size_t n) {
        if(p) {
            sodium_memzero(p,n); ++wiped_allocations; wiped_bytes+=n;
            previous_free(p,n);
        }
    }
    static void* reallocate(void* p,size_t old_size,size_t new_size) {
        auto replacement=allocate(new_size);
        if(p && replacement) std::memcpy(replacement,p,std::min(old_size,new_size));
        release(p,old_size);
        return replacement;
    }
public:
    static inline std::atomic<size_t> wiped_allocations{0},wiped_bytes{0};
    static void install_before_threads() {
        std::call_once(once,[] {
            mp_get_memory_functions(&previous_allocate,&previous_reallocate,&previous_free);
            mp_set_memory_functions(allocate,reallocate,release);
        });
    }
    static bool installed() {
        void* (*a)(size_t); void* (*r)(void*,size_t,size_t); void (*f)(void*,size_t);
        mp_get_memory_functions(&a,&r,&f);
        return a==allocate && r==reallocate && f==release;
    }
};
}
