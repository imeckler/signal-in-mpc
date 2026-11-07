"""Single-lane malicious Shamir/CCD conversion and same-VM composition.

All production data arguments are shared MP-SPDZ registers. The only public
disclosures are random validity, uniformly masked values, and a statistically
masked input-validation result. Callers explicitly authorize any TLS public
key/ciphertext release. No secret is returned as a Python integer or bytes.

The Python and native implementations are unverified. See SECURITY.txt for
the exact assumptions, source audit, and unimplemented persistence boundary.
"""

from .field_dag import MODULUS, execute, validate


def add_bits(left, right, zero):
    """Unsigned full adder, LSB first; append the carry bit."""
    if len(left) != len(right):
        raise ValueError('adder widths differ')
    carry, output = zero, []
    for a, b in zip(left, right):
        either = a ^ b
        output.append(either ^ carry)
        carry = (a & b) ^ (either & carry)
    return output + [carry]


def subtract_bits(left, right, zero, one):
    """Unsigned subtraction modulo 2^width; return result and borrow."""
    if len(left) != len(right):
        raise ValueError('subtractor widths differ')
    borrow, output = zero, []
    for a, b in zip(left, right):
        either = a ^ b
        output.append(either ^ borrow)
        borrow = ((a ^ one) & b) ^ ((either ^ one) & borrow)
    return output, borrow


def reduce_masked_sum(mask_bits, clear_bits, modulus_bits, zero, one):
    """Canonical (r+c) mod p for 0<=r,c<p, using only Boolean operations.

    This pure circuit helper is shared by the MPC adapter and exhaustive
    small-field boundary checks. Its preconditions are established separately.
    """
    if len(mask_bits) != len(modulus_bits) or len(clear_bits) != len(mask_bits):
        raise ValueError('modular addition widths differ')
    total = add_bits(mask_bits, clear_bits, zero)
    reduced, borrow = subtract_bits(total, list(modulus_bits) + [zero], zero, one)
    use_reduced = borrow ^ one
    return [a ^ ((a ^ b) & use_reduced) for a, b in zip(total, reduced)]


def _runtime():
    from Compiler.GC.types import sbit
    from Compiler.library import check_point, get_program, runtime_error_if
    from Compiler.types import sint
    if get_program().prime != MODULUS:
        raise ValueError('mixed adapter requires compile.py -P (2^255-19)')
    if not get_program().use_dabit:
        raise ValueError('mixed adapter requires compile.py -X')
    return sint, sbit, check_point, runtime_error_if


def enforce_bit_inputs(inputs, positions):
    """Abort on invalid bits, except with probability at most 1/p per check.

    An independent secret uniform field coefficient masks each b*(b-1).
    The result is zero for valid inputs; otherwise it is uniform. Revealing
    individual unmasked residuals could leak maliciously supplied secret data.
    Inputs must be fixed before the fresh coefficients are generated.
    """
    sint, _, check_point, runtime_error_if = _runtime()
    if not positions:
        return
    errors = [inputs[index] * (inputs[index] - 1) for index in positions]
    check_point()
    masked = sint(0)
    for error in errors:
        masked += error * sint.get_random()
    check_point()
    opened = masked.reveal(check=True)
    runtime_error_if(opened != 0, 'invalid field bit input')
    check_point()


def execute_secret(image, inputs):
    """Validate arbitrary shared input bits, evaluate, and return shared fields."""
    validate(image)
    if len(inputs) != image['input_count']:
        raise ValueError('incorrect secret field input count')
    sint, _, _, _ = _runtime()
    if any(not isinstance(value, sint) or value.size != 1 for value in inputs):
        raise TypeError('field input must be a single-lane sint register')
    enforce_bit_inputs(inputs, image['bit_inputs'])
    return execute(image, inputs, sint)


def field_to_wire_bits(value):
    """Secret field -> 32 secret little-endian bytes (MSB-first within bytes).

    Reject the probability-19/2^255 noncanonical daBit mask before opening
    c=x-r. On acceptance the mask is exactly uniform Fp, so c is independent
    of x. This deliberately avoids MP-SPDZ's approximate Rabbit-gap branch.
    """
    sint, sbit, check_point, runtime_error_if = _runtime()
    if not isinstance(value, sint) or value.size != 1:
        raise TypeError('canonical conversion requires one shared field value')
    zero, one = sbit(0), sbit(1)
    pairs = [sint.get_dabit() for _ in range(255)]
    arithmetic_mask = sum((a * (1 << index) for index, (a, _) in enumerate(pairs)), sint(0))
    binary_mask = [b for _, b in pairs]
    modulus_bits = [one if (MODULUS >> index) & 1 else zero for index in range(255)]
    _, valid = subtract_bits(binary_mask, modulus_bits, zero, one)
    check_point()
    # GC reveal itself checks its thread before reconstruction; explicit
    # checkpoints also sequence the arithmetic and binary domains together.
    runtime_error_if(valid.reveal() == 0, 'noncanonical random conversion mask; retry in a fresh session')
    check_point()
    masked_clear = (value - arithmetic_mask).reveal(check=True)
    clear_bits = [sbit(bit) for bit in masked_clear.bit_decompose(255)]
    canonical = reduce_masked_sum(binary_mask, clear_bits, modulus_bits, zero, one)
    # The final carry is mathematically zero after reduction. Preserve all
    # 256 bits rather than silently dropping a potentially significant bit.
    return [canonical[8 * byte + shift] for byte in range(32) for shift in range(7, -1, -1)]


def wire_bits_to_field(bits, mask_high_bit=False):
    """32 shared bytes -> field, with RFC7748 optional top-bit masking.

    Input is MSB-first within each little-endian byte. Domain conversion uses
    the backend's checked daBits and masked binary openings. Reduction is field
    arithmetic; callers requiring canonical input must establish that policy.
    """
    sint, _, check_point, _ = _runtime()
    if len(bits) != 256:
        raise ValueError('expected exactly 32 shared bytes')
    limit = 255 if mask_high_bit else 256
    output = sint(0)
    for index in range(limit):
        bit = bits[8 * (index // 8) + 7 - index % 8]
        if getattr(bit, 'n', None) != 1:
            raise TypeError('wire input must contain single-lane shared bits')
        output += sint(bit) * (1 << index)
    check_point()
    return output


def wire_bits_to_scalar_fields(bits):
    """Exact bytes -> 256 shared field bits, global LSB first; no reduction."""
    sint, _, check_point, _ = _runtime()
    if len(bits) != 256 or any(getattr(bit, 'n', None) != 1 for bit in bits):
        raise ValueError('expected exactly 256 single-lane shared bits')
    output = [sint(bits[8 * (index // 8) + 7 - index % 8]) for index in range(256)]
    check_point()
    return output


def fresh_scalar_fields():
    """Joint random scalar bit registers; no party learns the raw scalar.

    The Lean X25519 artifact performs clamping. The same returned handles may
    be reused for the public-key and server-key DAG evaluations within one VM.
    """
    sint, _, check_point, _ = _runtime()
    bits = [sint.get_dabit()[0] for _ in range(256)]
    check_point()
    return bits


def execute_boolean(image, inputs):
    """Execute an existing Lean Boolean artifact in this same mixed VM.

    Returned CCD registers may feed later stages directly. This does not call
    the separate fixture harness, write a plaintext secret, or reveal outputs.
    """
    _, sbit, _, _ = _runtime()
    from backend_adapter.boolean import execute as execute_bits
    return execute_bits(image, inputs, sbit(0), sbit(1))
