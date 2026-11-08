// Public synthetic field payloads only. Inspect allocation bytes BEFORE free;
// never dereference a destroyed object or read an allocation after deallocation.
#include "NativeWorker.h"
#include <cstring>
#include <memory>
#include <span>
#include <iostream>
using Prime=tls_mpc_worker::Field;
using Arithmetic=tls_mpc_worker::Share;
using Part=tls_mpc_worker::Bit::part_type;
using Limbs=modp_<4>;
using ByteSpan=std::span<unsigned char>;
static size_t inspected=0,nonzero=0,deallocations=0,failures=0;

static ByteSpan payload(Prime& x) {
    return {reinterpret_cast<unsigned char*>(x.get_ptr()),Prime::N_BYTES};
}
static ByteSpan payload(Arithmetic& x) {return payload(static_cast<Prime&>(x));}
static ByteSpan payload(gf2n_long& x) {
    return {static_cast<unsigned char*>(const_cast<void*>(x.get_ptr())),gf2n_long::N_BYTES};
}
static ByteSpan payload(Part& x) {return payload(static_cast<gf2n_long&>(x));}
static ByteSpan payload(Limbs& x) {
    return {reinterpret_cast<unsigned char*>(const_cast<mp_limb_t*>(x.get())),sizeof(mp_limb_t)*4};
}
static void inspect(ByteSpan bytes) noexcept {
    ++inspected;
    for(auto x:bytes)if(x){++nonzero;break;}
}
template<class T> static void fill(T& x) {auto b=payload(x);std::memset(b.data(),0xa5,b.size());}
template<class T> static void unchanged(T& x) {
    for(auto b:payload(x))if(b!=0xa5)throw std::runtime_error("live copy changed");
}

template<class T> struct ThrowCopy {
    T value;
    static inline int before_failure=-1;
    ThrowCopy()=default;
    ThrowCopy(const ThrowCopy& other):value(other.value) {
        if(before_failure==0)throw std::runtime_error("injected member-copy failure");
        if(before_failure>0)--before_failure;
    }
    ThrowCopy& operator=(const ThrowCopy&)=default;
};
template<class T> static ByteSpan payload(ThrowCopy<T>& x) {return payload(x.value);}

// Fill unused allocation slots with public zeros so the observer can examine
// all payload slots at deallocation, including never-constructed capacity.
// Offsets are measured on a live value; no dead-object method is invoked.
template<class T> struct ObservedAllocator {
    using value_type=T;
    static std::pair<size_t,size_t> layout() {
        T live;auto bytes=payload(live);
        return {bytes.data()-reinterpret_cast<unsigned char*>(&live),bytes.size()};
    }
    ObservedAllocator()=default;
    template<class U> ObservedAllocator(const ObservedAllocator<U>&){}
    T* allocate(size_t n) {
        auto p=std::allocator<T>{}.allocate(n);
        std::memset(static_cast<void*>(p),0,n*sizeof(T));return p;
    }
    void deallocate(T* p,size_t n) noexcept {
        auto [offset,width]=layout();auto raw=reinterpret_cast<unsigned char*>(p);
        for(size_t i=0;i<n;++i)inspect({raw+i*sizeof(T)+offset,width});
        ++deallocations;std::allocator<T>{}.deallocate(p,n);
    }
    template<class U> bool operator==(const ObservedAllocator<U>&)const{return true;}
};

template<class T> static void check_type() {
    T original;fill(original);
    using V=std::vector<T,ObservedAllocator<T>>;
    {
        V values(9,original);
        values.reserve(65); // Old allocation inspected after destruction.
        for(auto& x:values)unchanged(x);
    }
    // End each vector immediately after the mutation: discarded slots remain
    // untouched until the deallocation observer checks them. The observer runs
    // after libc++ removes its container annotations but BEFORE the allocation
    // is freed. No reading poisoned spare capacity or disabling ASan checks.
    {V v(9,original);v.pop_back();for(auto& x:v)unchanged(x);}
    {V v(9,original);v.resize(3);for(auto& x:v)unchanged(x);}
    {V v(9,original);v.assign(1,original);unchanged(v[0]);}
    {V v(9,original);v.clear();}
    {V v(9,original);V replacement(2,original);v=std::move(replacement);for(auto& x:v)unchanged(x);}
    {V v(9,original);v.resize(1);v.shrink_to_fit();unchanged(v[0]);}
    unchanged(original);
    using F=ThrowCopy<T>;
    std::vector<F> source(8);for(auto& x:source)fill(x);
    for(int stop=0;stop<8;++stop) {
        F::before_failure=stop;
        try {
            std::vector<F,ObservedAllocator<F>> target(source.begin(),source.end());
            throw std::logic_error("injection did not occur");
        } catch(const std::runtime_error&) {++failures;}
        F::before_failure=-1;
        for(auto& x:source)unchanged(x);
    }
}

int main(int argc,char** argv) {
    bool baseline=argc==2&&std::string(argv[1])=="baseline";
    check_type<Limbs>();check_type<Prime>();check_type<Arithmetic>();
    check_type<gf2n_long>();check_type<Part>();
    if((baseline?nonzero==0:nonzero!=0)||failures!=40)
        throw std::runtime_error("field destruction cleanup expectation failed");
    std::cout<<(baseline?"baseline retained payloads":"candidate payload cleanup passed")
             <<": "<<inspected<<" inspected slots; "<<nonzero<<" nonzero; "
             <<deallocations<<" allocations; "<<failures<<" copy failures\n";
}
