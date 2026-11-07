"""Unverified same-VM classical session receive; routing and identifiers stay shared.

The parser first obtains the peer ratchet key inside the Boolean VM. Three
X25519 DAG evaluations prepare the new-ratchet candidate unconditionally, so
retained-versus-new selection never becomes a public branch. The final proved
Boolean circuit authenticates and commits exactly one candidate. SPQR evolution
and persistent refresh/erasure are separate integration work.
"""
from handshake_backend import mixed
from handshake_backend.field_dag import validate
from SignalReference.NewRatchetReceiveWork.adapter import fresh_private_bits


def receive(field_image, parser_image, session_image, present, old_sender, retained,
            fresh_private, pq_key, sender, receiver, addresses, wire, *, primitives=mixed):
    validate(field_image)
    if (field_image['input_count'] != 257 or field_image['bit_inputs'] != list(range(256))
            or len(field_image['outputs']) != 1):
        raise ValueError('incorrect X25519 artifact shape')
    if (parser_image.get('name') != 'signal-protobuf-parse'
            or parser_image.get('input_bits') != len(wire) or len(parser_image.get('outputs', [])) != 720):
        raise ValueError('incorrect parser artifact shape')
    if (session_image.get('name') != 'signal-session-receive'
            or session_image.get('input_bits') != 429 * 8 + len(retained) + len(wire)):
        raise ValueError('incorrect session artifact shape')
    sizes = ((present, 8), (old_sender, 136 * 8), (fresh_private, 256),
             (pq_key, 256), (sender, 256), (receiver, 256), (addresses, 36 * 8))
    if any(len(bits) != size for bits, size in sizes) or len(wire) % 8 or len(retained) % 8:
        raise ValueError('incorrect shared input length')
    parsed = primitives.execute_boolean(parser_image, list(wire))
    remote = parsed[8:264]
    zero = fresh_private[0] ^ fresh_private[0]
    one = zero ^ 1
    private = list(fresh_private)
    private[5:8] = [zero] * 3
    private[248], private[249] = zero, one
    scalar = primitives.wire_bits_to_scalar_fields(private)
    old_scalar = primitives.wire_bits_to_scalar_fields(old_sender[32 * 8:64 * 8])
    point = primitives.wire_bits_to_field(remote, mask_high_bit=True)
    base = [one if (9 if byte == 0 else 0) >> shift & 1 else zero
            for byte in range(32) for shift in range(7, -1, -1)]
    base_point = primitives.wire_bits_to_field(base, mask_high_bit=True)
    new_public = primitives.field_to_wire_bits(primitives.execute_secret(field_image, scalar + [base_point])[0])
    receiving = primitives.field_to_wire_bits(primitives.execute_secret(field_image, old_scalar + [point])[0])
    sending = primitives.field_to_wire_bits(primitives.execute_secret(field_image, scalar + [point])[0])
    return primitives.execute_boolean(session_image, list(present) + list(old_sender) + private + new_public +
        receiving + sending + remote + list(pq_key) + list(sender) + list(receiver) + list(addresses) + list(retained) + list(wire))
