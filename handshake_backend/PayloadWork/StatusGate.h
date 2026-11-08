#pragma once
#include "NativeWorker.h"
#include <cstdint>
#include <utility>
#include <vector>

namespace tls_mpc_worker {
// Release must authenticate every opened share before returning bytes. The
// validity decision is the only declassification on rejection; no ciphertext
// reconstruction is attempted then. Session's guard makes rejection terminal.
template<class Release>
std::vector<uint8_t> release_private_seal(const Bits& sealed,size_t capacity,Release&& release) {
    public_require(capacity<=16384 && sealed.size()==8*(capacity+23),"invalid private seal output shape");
    Bits status(sealed.begin(),sealed.begin()+8);
    public_require(release(status)==std::vector<uint8_t>({255}),"private payload validation rejected");
    Bits wire(sealed.begin()+8,sealed.end());
    auto result=release(wire);
    public_require(result.size()==capacity+22,"invalid private ciphertext shape");
    return result;
}
}
