#pragma once
// Pinned MP-SPDZ defines the gf2n -> Bit constructor in Math/Bit.cpp, but
// instantiates only octet/word fields. Provide the missing long-field case,
// preserving the bit-only precondition as a runtime check in release builds.
#include "Math/Bit.h"
#include "Math/gf2n.h"

template<>
inline Bit::Bit(const gf2n_<int128>& value) : super(value.get_bit(0)) {
    if (!(value.is_zero() || value.is_one()))
        throw std::runtime_error("non-bit GF(2^128) value at binary opening boundary");
}
