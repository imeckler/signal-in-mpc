#pragma once
// This profile compiles with -X (checked daBits), never -Y (edaBits).
// Upstream's generic edaBit sanitize job narrows a binary field element to int;
// that expression cannot instantiate for gf2n_long. Reject this unused job
// explicitly rather than silently truncating a field element or changing it
// into a different protocol. No upstream source changes are needed.
#include "StrongShamirShare.h"
#include "Protocols/ReplicatedPrep.hpp"

template<> template<>
inline void RingPrep<tls_mpc_worker::StrongShamirShare<gfp_<0,4>>>::sanitize<0>(
    std::vector<edabit<tls_mpc_worker::StrongShamirShare<gfp_<0,4>>>>&,
    int, int, int, int)
{
    throw std::runtime_error("TLS CCD128 profile requires checked daBits; edaBit sanitize is unsupported");
}
