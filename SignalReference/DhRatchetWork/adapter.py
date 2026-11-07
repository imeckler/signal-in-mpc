"""Unverified composition of proved X25519 and Signal root-chain artifacts.

Arguments/results are shared registers. No value, status, key or agreement is
opened here. The existing mixed adapter opens only its documented random
checks/masked values. Full session policy and atomic persistence are external.
"""
from handshake_backend import mixed
from handshake_backend.field_dag import validate


def create_chain(field_image, root_image, root_bits, private_bits, peer_bits, *, primitives=mixed):
    """All bit vectors encode 32 exact bytes, MSB first within each byte.

    Private scalar bytes are never reduced modulo a field. The X25519 circuit
    clamps them. Peer decoding masks the top bit before field reduction.
    Returns status1 || candidate root32 || new chain32 || zero counterBE4.
    """
    validate(field_image)
    if (field_image['input_count'] != 257 or field_image['bit_inputs'] != list(range(256))
            or len(field_image['outputs']) != 1):
        raise ValueError('incorrect X25519 artifact shape')
    if (root_image.get('format') != 'tls-mpc-aig-v1' or root_image.get('name') != 'signal-dh-ratchet'
            or root_image.get('input_bits') != 512 or len(root_image.get('outputs', [])) != 552):
        raise ValueError('incorrect Signal root-chain artifact shape')
    if any(len(bits) != 256 for bits in (root_bits, private_bits, peer_bits)):
        raise ValueError('root, private scalar and peer key must each contain32 shared bytes')
    scalar = primitives.wire_bits_to_scalar_fields(private_bits)
    point = primitives.wire_bits_to_field(peer_bits, mask_high_bit=True)
    agreement = primitives.execute_secret(field_image, scalar + [point])[0]
    agreement_bits = primitives.field_to_wire_bits(agreement)
    return primitives.execute_boolean(root_image, root_bits + agreement_bits)
