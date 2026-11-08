#pragma once
#include "NativeWorker.h"
#include <cstddef>
#include <stdexcept>
#include <utility>

namespace tls_mpc_worker {
// Move-owned validity-preserving plaintext chunk for same-worker protocol consumers. No bytes or
// actual length are opened. private_length is a 16-bit big-endian byte count;
// capacity is public and includes the authenticated router's bounded backing
// storage. The producing circuit, not a C++ comparison of shares, establishes
// private_length <= capacity. Consumers must maintain that circuit invariant.
struct PrivatePayload {
    Bits data;
    Bits private_length;
    Bits validity;
    // Public constants may carry the runtime's full 64-bit register backing;
    // the pinned n_bits=1 function argument uses their low logical bit.
    size_t capacity;
    PrivatePayload(Bits&& data,Bits&& private_length,Bits&& validity,size_t capacity)
        :data(std::move(data)),private_length(std::move(private_length)),validity(std::move(validity)),capacity(capacity) { validate_shape(); }
    void validate_shape() const {
        if(capacity>16385 || this->data.size()!=8*capacity || this->private_length.size()!=16 || this->validity.size()!=8)
            throw std::runtime_error("invalid private payload shape");
        for(const auto* bits:{&this->data,&this->private_length,&this->validity})
            for(const auto& row:*bits)
                if(row.size()!=1 || row[0].get_regs().empty() || row[0].get_regs().size()>size_t(Bit::default_length))
                    throw std::runtime_error("invalid private payload register shape");
    }
    static PrivatePayload from_result(Bits encoded,size_t capacity) {
        if(capacity>16385 || encoded.size()!=8*(capacity+3))
            throw std::runtime_error("invalid private buffer result shape");
        Bits valid(encoded.begin(),encoded.begin()+8);
        Bits length(encoded.begin()+8,encoded.begin()+24);
        Bits data(encoded.begin()+24,encoded.end());
        return PrivatePayload(std::move(data),std::move(length),std::move(valid),capacity);
    }
    PrivatePayload(const PrivatePayload&)=delete;
    PrivatePayload& operator=(const PrivatePayload&)=delete;
    PrivatePayload(PrivatePayload&&) noexcept=default;
    PrivatePayload& operator=(PrivatePayload&&) noexcept=default;
};
}
