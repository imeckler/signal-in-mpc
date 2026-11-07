#include "GC/TinierSecret.h"
#include <cstdint>
#include <iostream>
#include <stdexcept>
static uint64_t next(uint64_t& s) {
    s+=0x9e3779b97f4a7c15ULL; auto z=s;
    z=(z^(z>>30))*0xbf58476d1ce4e5b9ULL;
    z=(z^(z>>27))*0x94d049bb133111ebULL;
    return z^(z>>31);
}
static void require(bool b) { if(!b)throw std::runtime_error("MAC width relation failed"); }
int main() {
    gf2n_mac_key::init_minimum(128); gf2n_short::init_field(64);
    require(gf2n_mac_key::length()==128);
    uint64_t seed=0x514a37b962cd805eULL; unsigned cases=0, old_lost_high=0;
    for(unsigned i=0;i<2176;i++) {
        int128 delta=i<128 ? (i<64?int128(word(0),word(1)<<i):int128(word(1)<<(i-64),word(0))) : int128(next(seed),next(seed));
        int128 mask(next(seed),next(seed));
        auto d=gf2n_mac_key::cut(delta);
        require(d.get()==delta);
        require(gf2n_short::cut(delta)==gf2n_short(delta.get_lower()));
        for(unsigned bit=0;bit<2;bit++) {
            int128 response=mask^(bit?delta:int128());
            // Covers both input sender/receiver conversions and the XOR
            // conversion used for triple MACs, without relying on networking.
            auto receiver=gf2n_mac_key::cut(response);
            auto sender=gf2n_mac_key::cut(mask);
            auto combined=gf2n_mac_key::cut(response^mask);
            auto expected=bit?d:gf2n_long(0);
            require(receiver+sender==expected);
            require(combined==expected);
            if(bit&&delta.get_upper()!=0) {
                require(gf2n_long((response^mask).get_lower())!=expected);
                old_lost_high++;
            }
            for(unsigned high=64;high<128;high++) {
                auto corruption=gf2n_mac_key::cut(int128(word(1)<<(high-64),word(0)));
                require(combined+corruption!=expected);
            }
            cases++;
        }
    }
    std::cout<<"{\"cot_relations\":"<<cases<<",\"high_bit_corruption_rejections\":"<<cases*64
      <<",\"old_truncation_counterexamples\":"<<old_lost_high<<",\"short_field_backward_compatibility_cases\":2176}\n";
}
