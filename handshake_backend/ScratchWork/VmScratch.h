#pragma once
#include "NativeWorker.h"

namespace tls_mpc_worker {
// Counts describe storage shapes, never share values. This API wipes only
// currently constructed VM memory/register objects and temp.Sansp. It is NOT
// an operational retirement receipt. Call only with exclusive host ownership.
struct ScratchCounts {
    size_t arithmetic=0, binary_registers=0, binary_fields=0;
    bool operator==(const ScratchCounts&) const = default;
};

inline ScratchCounts wipe_vm_secret_scratch(Machine<Share>& machine) {
    ScratchCounts counts;
    machine.visit_secret_scratch([&](Share& value) {
        sodium_memzero(static_cast<Field&>(value).get_ptr(),Field::N_BYTES);
        ++counts.arithmetic;
    },[&](Bit& value) {
        ++counts.binary_registers;counts.binary_fields+=value.get_regs().size();
        wipe_bit_storage(value);
    });
    return counts;
}
}
