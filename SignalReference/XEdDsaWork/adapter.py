"""Unverified shared-stage orchestration for the bounded 64-byte XEdDSA verifier.

All key, signature, message, point, digest and status values are secret registers.
Only public byte lengths choose artifacts. This adapter performs no reveals and
never branches on a value. Conversion must provide exact canonical field bytes,
RFC7748-style top-bit-masked/reduced Montgomery decoding, and Boolean field bits.

The repository's production mixed conversion/runtime is NOT instantiated here;
this interface does not establish malicious/statistical128 conversion security.
It is not connected to PQXDH or identity/prekey policy. Tests use public values.
"""

def verify(stages, conversion, public_key, signature, message):
    if len(public_key) != 32 or len(signature) != 64:
        raise ValueError('bounded XEdDSA stage requires raw key32 and signature64')
    # Signature length and message length are public metadata, never secret tests.
    u = conversion.decode_u(public_key)
    recovered = [stages.field('recover', i, [u])[0] for i in range(3)]
    validity, root_x, y = recovered
    root_bytes = conversion.encode_field(root_x)
    y_bytes = conversion.encode_field(y)
    binding = stages.boolean('binding', 128, signature + root_bytes + y_bytes)
    digest_input = signature[:32] + binding[1:] + message
    digest = stages.boolean('hash', len(digest_input), digest_input)
    h = stages.boolean('reduce', 64, digest)
    field_inputs = ([root_x, y] + conversion.bits_to_field(binding[:1], 1)
                    + conversion.bits_to_field(h, 256)
                    + conversion.bits_to_field(signature[32:], 253))
    result = [stages.field('signed', i, field_inputs)[0] for i in range(2)]
    return stages.boolean('finish', 160, signature + conversion.encode_field(validity)
                          + conversion.encode_field(result[0]) + conversion.encode_field(result[1]))
