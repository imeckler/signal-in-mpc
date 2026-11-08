// Public deterministic seed patterns; inspect allocated storage before release.
#include "Tools/random.h"
#include <array>
#include <cstring>
#include <iostream>
#include <new>

static void require(bool ok) { if(!ok) throw std::runtime_error("PRNG lifecycle check failed"); }
static size_t align_to(size_t n,size_t alignment) { return (n+alignment-1)/alignment*alignment; }
int main() {
    std::array<octet,SEED_SIZE> first,second;
    first.fill(0xa5); second.fill(0x3c);
    PRNG old,fresh;old.SetSeed(first.data());fresh.SetSeed(second.data());
    for(size_t i=0;i<7;++i)old.get_bit();
    old.SetSeed(second.data());
    for(size_t i=0;i<256;++i)require(old.get_bit()==fresh.get_bit());
    std::array<octet,1024> a,b;
    old.get_octets(a.data(),a.size());fresh.get_octets(b.data(),b.size());require(a==b);
    PRNG copy(old);
    for(size_t i=0;i<100;++i) require(copy.get_word()==old.get_word());
    old.erase_state();require(!old.is_initialized());
    bool rejected=false; try { old.get_uchar(); } catch(const std::runtime_error&) { rejected=true; }
    require(rejected);
    for(size_t i=0;i<SEED_SIZE;++i)require(old.get_seed()[i]==0);
    // Exact pinned header layout: seed, aligned counter and random caches,
    // optional AES implementation selector, then both key schedules.
    alignas(PRNG) std::array<octet,sizeof(PRNG)> storage;
    storage.fill(0xa5);
    auto p=new(storage.data()) PRNG;
    auto offset=p->get_seed()-storage.data();
    p->SetSeed(first.data());p->get_octets(a.data(),a.size());p->get_bit();
    auto zero=[&](size_t start,size_t size) {
        require(start+size<=storage.size());
        for(size_t i=start;i<start+size;++i)require(storage[i]==0);
    };
    p->~PRNG();
    constexpr size_t rand_size=10*CALL_SIZE;
    zero(offset,SEED_SIZE);
    size_t state=align_to(offset+SEED_SIZE,16);
    zero(state,rand_size);zero(state+rand_size,rand_size);
#ifdef USE_AES
    size_t schedules=state+2*rand_size;
#if defined(__AES__) || !defined(__x86_64__)
    ++schedules; // public implementation-selection flag is not secret payload
#endif
    schedules=align_to(schedules,alignof(uint));
    zero(schedules,44*sizeof(uint));
    zero(align_to(schedules+44*sizeof(uint),16),176);
#endif
    std::cout<<"PRNG lifetime passed: reseed cache reset; copy stream preserved; seed/counters/random/both schedules zero in allocated storage\n";
}
