"""Bulk memory I/O for exported arrays of single secret bits.

This unverified backend adapter changes neither the Lean artifact nor its bit
ordering. Each array cell still contains one bit, matching sbv:[Nx1] native
arguments. Public chunks limit temporary packing to64 lanes; partial tails
preserve their exact length. No input or output is opened here.
"""


def read_bits(array):
    if array.value_type.n_bits != 1:
        raise ValueError('expected an array of single-bit memory cells')
    result = []
    for start in range(0, len(array), 64):
        size = min(64, len(array)-start)
        result.extend(array.get_vector(base=start, size=size).v[0].bit_decompose(size))
    return result


def write_bits(array, bits):
    from Compiler.GC.types import sbitvec, sbits
    if array.value_type.n_bits != 1 or len(array) != len(bits):
        raise ValueError('exported bit output dimensions differ')
    for start in range(0, len(bits), 64):
        batch = bits[start:start+64]
        array.assign_vector(sbitvec.get_type(1).from_vec([sbits.bit_compose(batch)]), base=start)
