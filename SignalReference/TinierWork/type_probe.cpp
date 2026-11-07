#include "GC/TinierSecret.h"
#include <type_traits>
#include <iostream>
static_assert(std::is_base_of_v<gf2n_long,gf2n_mac_key>);
static_assert(std::is_same_v<GC::TinierShare<gf2n_mac_key>::share_type,SemiShare<Bit>>);
int main() {
    gf2n_mac_key::init_minimum(128);
    if(gf2n_mac_key::length()!=128) return 1;
    std::cout << "Tinier bit value; GF128 MAC; statistical default " << DEFAULT_SECURITY << "\n";
    return DEFAULT_SECURITY==128 ? 0:2;
}
