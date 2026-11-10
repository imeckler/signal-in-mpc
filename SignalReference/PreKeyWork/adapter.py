"""Unverified shared composition for the typed prekey validation prefix.

Every value is a secret register; only list lengths select artifacts. The
external trust_result code is the result of the caller's Sending identity-store
check for THIS canonical identity and address:0 allow,1 deny,2 callback error.
This adapter defines no trust policy and does not execute store callbacks.

Both signatures are computed by the frozen XEdDSA verifier; callers cannot
supply their validity. Result precedence follows typed constructor -> trust ->
EC signature -> PQ signature. Fixed circuit execution does not reproduce Rust's
short-circuit timing. Private conversion remains the frozen abstract boundary.

Raw decode errors are returned independently, since actual PreKeyBundleContent
already holds typed keys and defines no combined raw-key decode order. Local
code32 marks that boundary; it is not a libsignal error. No PQXDH/session/store
mutation or production authorization is performed.
"""
from SignalReference.XEdDsaWork.adapter import verify as verify_signature

def signature_result(xstages, conversion, identity_raw, message, signature):
    if len(signature) == 64:
        return verify_signature(xstages, conversion, identity_raw, signature, message)
    # Public shape rejection: frozen decode is identically zero for these lengths.
    return xstages.decode(signature)[:1]

def validate(stages, xstages, conversion, flags, metadata, identity, signed_key,
             pq_key, optional_key, ec_signature, pq_signature, trust_result, features='base'):
    if len(flags) != 11 or len(metadata) != 17 or len(trust_result) != 1:
        raise ValueError('public profile: flags11,metadata17,external trust-result1')
    identity_decoded = stages.run('ec',identity,features)
    signed_decoded = stages.run('ec',signed_key,features)
    pq_decoded = stages.run('kem',pq_key,features)
    optional_decoded = stages.run('ec',optional_key,features)
    optional_ok = stages.run('optional',flags[3:4]+optional_decoded[:1],features)
    # Typed DeviceId boundary; metadata already contains the single device byte.
    device = stages.run('device',conversion.zero_bytes(3)+metadata[4:5],features)
    constructed = stages.run('construct',flags+metadata,features)
    ec = signature_result(xstages,conversion,identity_decoded[3:],signed_decoded[2:],ec_signature)
    pq = signature_result(xstages,conversion,identity_decoded[3:],pq_decoded[2:],pq_signature)
    identity_ok = stages.run('optional',flags[7:8]+identity_decoded[:1],features)
    signed_ok = stages.run('optional',flags[5:6]+signed_decoded[:1],features)
    pq_ok = stages.run('optional',flags[9:10]+pq_decoded[:1],features)
    device_ok = stages.run('optional',flags[1:2]+device[:1],features)
    wire_status = identity_ok+signed_ok+pq_ok+optional_ok+device_ok
    result = stages.run('typed-finish',wire_status+constructed+trust_result+ec+pq,features)
    return {'prefix_result':result,'wire_results':[identity_decoded[:2],signed_decoded[:2],pq_decoded[:2],optional_decoded[:2],device],
            'canonical_identity':identity_decoded[2:],'canonical_signed_key':signed_decoded[2:],'canonical_pq_key':pq_decoded[2:]}
