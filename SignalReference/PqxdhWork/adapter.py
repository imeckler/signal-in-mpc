"""Unverified same-VM initiator PQXDH composition from shared key slots.

Kyber encapsulation and identity/prekey validation remain unresolved. The KEM
shared-secret input is explicit. No agreement, acceptance or key is opened.
"""
from handshake_backend import mixed
from handshake_backend.field_dag import validate


def initiate(field_image, kdf_image, identity_private, ephemeral_private,
             their_identity, signed_prekey, one_time_prekey, kem_secret, *, primitives=mixed):
    """Inputs are exact 32-byte shared bit vectors, MSB first within each byte.

    one_time_prekey is None or 256 bits; its presence is a public profile.
    Returns shared status255/0 || root32 || chain32 || initialPQR32. Any
    all-zero DH agreement zeroes all97 bytes. KEM failure must be handled by
    a future producing stage; this interface has no KEM validity claim.
    """
    validate(field_image)
    if (field_image['input_count'] != 257 or field_image['bit_inputs'] != list(range(256))
            or len(field_image['outputs']) != 1):
        raise ValueError('incorrect X25519 artifact shape')
    present = one_time_prekey is not None
    profile = 'present' if present else 'none'
    if (kdf_image.get('format') != 'tls-mpc-aig-v1'
            or kdf_image.get('name') != 'signal-pqxdh-' + profile
            or kdf_image.get('input_bits') != (160 if present else 128) * 8
            or len(kdf_image.get('outputs', [])) != 768):
        raise ValueError('incorrect PQXDH KDF artifact shape')
    inputs = [identity_private, ephemeral_private, their_identity, signed_prekey, kem_secret]
    if present:
        inputs.append(one_time_prekey)
    if any(len(bits) != 256 for bits in inputs):
        raise ValueError('each private/public key and KEM secret must contain32 shared bytes')

    def agreement(private, public):
        scalar = primitives.wire_bits_to_scalar_fields(private)
        point = primitives.wire_bits_to_field(public, mask_high_bit=True)
        value = primitives.execute_secret(field_image, scalar + [point])[0]
        return primitives.field_to_wire_bits(value)

    dh = [agreement(identity_private, signed_prekey),
          agreement(ephemeral_private, their_identity),
          agreement(ephemeral_private, signed_prekey)]
    if present:
        dh.append(agreement(ephemeral_private, one_time_prekey))
    masks = []
    for bits in dh:
        nonzero = bits[0]
        for bit in bits[1:]:
            nonzero = nonzero | bit
        masks.append(nonzero)
    accepted = masks[0]
    for mask in masks[1:]:
        accepted = accepted & mask
    keys = primitives.execute_boolean(kdf_image, [bit for block in dh for bit in block] + kem_secret)
    return [accepted] * 8 + [accepted & bit for bit in keys]
