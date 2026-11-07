"""Unverified same-VM new-DH first-message composition; every result stays shared.

The caller selects a previously unseen remote ratchet inside MPC and supplies
old sender/root state. This adapter computes the fresh public key and both DH
agreements. It does not implement retained-chain selection or persistent commit.
"""
from handshake_backend import mixed
from handshake_backend.field_dag import validate


def receive(field_image, receive_image, present, old_state, fresh_private,
            remote, pq_key, sender, receiver, addresses, wire, *, primitives=mixed):
    """MSB-first shared bits within bytes; fresh_private must be jointly random.

    old_state: root32/private32/public32/chain32/index4/previous4.
    No field, byte, identity, status or application output is revealed here.
    """
    validate(field_image)
    if (field_image['input_count'] != 257 or field_image['bit_inputs'] != list(range(256))
            or len(field_image['outputs']) != 1):
        raise ValueError('incorrect X25519 artifact shape')
    sizes = ((present, 8), (old_state, 136 * 8), (fresh_private, 256), (remote, 256),
             (pq_key, 256), (sender, 256), (receiver, 256), (addresses, 36 * 8))
    if any(len(bits) != size for bits, size in sizes) or len(wire) % 8:
        raise ValueError('incorrect shared input shape')
    if (receive_image.get('format') != 'tls-mpc-aig-v1'
            or receive_image.get('name') != 'signal-new-ratchet-receive'
            or receive_image.get('input_bits') != 429 * 8 + len(wire)):
        raise ValueError('incorrect first-message receive artifact shape')
    # Wire representation is big-endian within each little-endian scalar byte.
    zero = fresh_private[0] ^ fresh_private[0]
    one = zero ^ 1
    private = list(fresh_private)
    private[5:8] = [zero] * 3
    private[248], private[249] = zero, one
    scalar = primitives.wire_bits_to_scalar_fields(private)
    old_scalar = primitives.wire_bits_to_scalar_fields(old_state[32 * 8:64 * 8])
    point = primitives.wire_bits_to_field(remote, mask_high_bit=True)
    base = [one if (9 if byte == 0 else 0) >> shift & 1 else zero
            for byte in range(32) for shift in range(7, -1, -1)]
    base_point = primitives.wire_bits_to_field(base, mask_high_bit=True)
    new_public = primitives.field_to_wire_bits(primitives.execute_secret(field_image, scalar + [base_point])[0])
    receiving = primitives.field_to_wire_bits(primitives.execute_secret(field_image, old_scalar + [point])[0])
    sending = primitives.field_to_wire_bits(primitives.execute_secret(field_image, scalar + [point])[0])
    return primitives.execute_boolean(receive_image, list(present) + list(old_state) + private + new_public +
                                      receiving + sending + list(remote) + list(pq_key) + list(sender) +
                                      list(receiver) + list(addresses) + list(wire))


def fresh_private_bits():
    """Joint backend randomness; returned bits never pass through a clear value."""
    sint, _, check_point, _ = mixed._runtime()
    bits = [sint.get_dabit()[1] for _ in range(256)]
    check_point()
    return bits
