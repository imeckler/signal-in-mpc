#include "LifecycleWork/SecureGmp.h"
#include "Tools/ErasingThreadStack.h"
#include <pthread.h>
#include <array>
#include <iostream>
#include <cstring>
#include <cstdlib>

namespace {
struct Allocation { void* ptr=nullptr; size_t size=0; };
std::array<Allocation,4096> allocations;
size_t inspected=0;
void require(bool ok) { if(!ok) { std::cerr<<"owned storage check failed\n"; std::abort(); } }
void* observe_allocate(size_t n) {
    auto p=std::malloc(n?n:1);require(p);
    for(auto& a:allocations)if(!a.ptr) { a={p,n};return p; }
    std::abort();
}
void observe_free(void* p,size_t n) {
    for(auto& a:allocations)if(a.ptr==p) {
        require(a.size==n);
        for(size_t i=0;i<n;++i)require(static_cast<unsigned char*>(p)[i]==0);
        a={};++inspected;std::free(p);return;
    }
    std::abort();
}
void* observe_reallocate(void*,size_t,size_t) { std::abort(); }
void* worker(void* arg) {
    auto& s=*static_cast<ErasingThreadStack*>(arg);
    volatile unsigned char marker[4096];
    for(size_t i=0;i<sizeof(marker);++i)marker[i]=0xa5;
    auto address=reinterpret_cast<uintptr_t>(&marker[0]);
    auto begin=reinterpret_cast<uintptr_t>(s.data);
    require(address>=begin && address+sizeof(marker)<=begin+s.size);
    return nullptr;
}
}
int main() {
    mp_set_memory_functions(observe_allocate,observe_reallocate,observe_free);
    tls_mpc_worker::SecureGmp::install_before_threads();
    require(tls_mpc_worker::SecureGmp::installed());
    mpz_t value;mpz_init2(value,512);mpz_setbit(value,100);
    mpz_realloc2(value,8192);require(mpz_tstbit(value,100));
    mpz_realloc2(value,256);require(mpz_tstbit(value,100));
    gmp_randstate_t random;gmp_randinit_default(random);gmp_randseed_ui(random,42);
    mpz_urandomb(value,random,4096);gmp_randclear(random);mpz_clear(value);
    require(inspected>5);
    for(auto a:allocations)require(!a.ptr);
    auto before=ErasingThreadStack::wiped_stacks.load();
    {
        ErasingThreadStack stack;
        memset(stack.data,0xa5,stack.size);
        pthread_attr_t attr;require(pthread_attr_init(&attr)==0);
        require(pthread_attr_setstack(&attr,stack.data,stack.size)==0);
        pthread_t thread;require(pthread_create(&thread,&attr,worker,&stack)==0);
        require(pthread_attr_destroy(&attr)==0);require(pthread_join(thread,nullptr)==0);
        stack.erase();
        for(size_t i=0;i<stack.size;++i)require(static_cast<unsigned char*>(stack.data)[i]==0);
    }
    require(ErasingThreadStack::wiped_stacks==before+1);
    std::cout<<"owned storage passed: "<<inspected<<" GMP releases inspected before free; grow/shrink preserve live value; actual joined owned stack fully zero\n";
}
