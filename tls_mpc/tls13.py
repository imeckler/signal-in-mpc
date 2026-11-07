"""TLS 1.3 AES-128-GCM/SHA-256 record and key-schedule circuits (RFC 8446).

This is a stateless cryptographic layer, not a TLS connection implementation.
Secrets and opened record fields remain shared. Record sizes, sequence numbers,
and outgoing content types/padding are public. The caller must durably reserve
each (traffic-key epoch, sequence) once, authenticate the handshake, and implement
TLS alerts, key-usage limits, and atomic state changes. No value is revealed here.
"""

from dataclasses import dataclass

from .backend import bit_or, byte_length, equal, mask, xor
from .crypto import HmacSha256, gcm_open, gcm_seal, hkdf_expand, hkdf_extract, sha256

MAX_CONTENT = 1 << 14
MAX_INNER = MAX_CONTENT + 1
CONTENT_TYPES = (21, 22, 23)


@dataclass(frozen=True)
class SealedRecord:
    header: bytes
    encrypted: list

    def wire(self, ctx):
        return ctx.public(self.header) + self.encrypted


@dataclass(frozen=True)
class OpenedRecord:
    valid: object
    content: list  # fixed-size buffer, zero after content_length and on failure
    content_length: list  # shared unsigned 16-bit integer, big-endian
    content_type: list  # shared byte, zero on failure


def record_nonce(ctx, iv, sequence):
    if byte_length(iv) != 12 or not isinstance(sequence, int) or not 0 <= sequence < 1 << 64:
        raise ValueError('TLS requires a 96-bit IV and a non-wrapping 64-bit sequence')
    return xor(iv, ctx.public(bytes(4) + sequence.to_bytes(8, 'big')))


def seal_record(ctx, key, iv, sequence, content, *, content_type=23, padding=0):
    length = byte_length(content)
    if byte_length(key) != 16:
        raise ValueError('only TLS_AES_128_GCM_SHA256 is implemented')
    if content_type not in CONTENT_TYPES or padding < 0 or length + 1 + padding > MAX_INNER:
        raise ValueError('invalid TLS inner plaintext dimensions or type')
    if length == 0 and content_type != 23:
        raise ValueError('empty handshake/alert fragments are prohibited')
    inner = content + ctx.public(bytes([content_type]) + bytes(padding))
    header = b'\x17\x03\x03' + (byte_length(inner) + 16).to_bytes(2, 'big')
    ciphertext, tag = gcm_seal(ctx, key, record_nonce(ctx, iv, sequence), inner, ctx.public(header))
    return SealedRecord(header, ciphertext + tag)


def open_record(ctx, key, iv, sequence, header: bytes, encrypted):
    length = byte_length(encrypted)
    if byte_length(key) != 16:
        raise ValueError('only TLS_AES_128_GCM_SHA256 is implemented')
    if (len(header) != 5 or header[:3] != b'\x17\x03\x03'
            or int.from_bytes(header[3:], 'big') != length or not 17 <= length <= MAX_INNER + 16):
        raise ValueError('invalid public TLSCiphertext framing')
    authenticated, inner = gcm_open(ctx, key, record_nonce(ctx, iv, sequence),
                                    encrypted[:-128], ctx.public(header), encrypted[-128:])
    # Scan the fixed buffer from the end without exposing padding or content type.
    seen, kind, content_length = ctx.zero, ctx.public(b'\x00'), ctx.public(bytes(2))
    content = [ctx.zero] * len(inner)
    for i in range(byte_length(inner) - 1, -1, -1):
        byte = inner[8 * i:8 * i + 8]
        content[8 * i:8 * i + 8] = mask(ctx, seen, byte)
        nonzero = equal(ctx, byte, ctx.public(b'\x00')) ^ ctx.one
        take = (seen ^ ctx.one) & nonzero
        kind = xor(kind, mask(ctx, take, byte))
        content_length = xor(content_length, mask(ctx, take, ctx.public(i.to_bytes(2, 'big'))))
        seen = bit_or(seen, nonzero)
    allowed = ctx.zero
    for content_type in CONTENT_TYPES:
        allowed = allowed ^ equal(ctx, kind, ctx.public(bytes([content_type])))
    nonempty = equal(ctx, content_length, ctx.public(bytes(2))) ^ ctx.one
    application = equal(ctx, kind, ctx.public(b'\x17'))
    valid = authenticated & seen & allowed & bit_or(nonempty, application)
    return OpenedRecord(valid, mask(ctx, valid, content), mask(ctx, valid, content_length),
                        mask(ctx, valid, kind))


def expand_label(ctx, secret, label: bytes, context, length):
    full_label = b'tls13 ' + label
    context_length = byte_length(context)
    if not 7 <= len(full_label) <= 255 or context_length > 255 or not 0 <= length <= 255 * 32:
        raise ValueError('invalid HKDF-Expand-Label dimensions')
    encoded = ctx.public(length.to_bytes(2, 'big') + bytes([len(full_label)]) + full_label
                         + bytes([context_length])) + context
    return hkdf_expand(ctx, secret, encoded, length)


def derive_secret(ctx, secret, label, transcript_hash):
    if byte_length(transcript_hash) != 32:
        raise ValueError('TLS transcript hash must be SHA-256')
    return expand_label(ctx, secret, label, transcript_hash, 32)


@dataclass(frozen=True)
class HandshakeSecrets:
    client: list
    server: list
    master: list


def handshake_secrets(ctx, dhe_secret, hello_transcript_hash):
    """No-PSK key schedule; DHE computation and transcript authentication are external."""
    if byte_length(dhe_secret) != 32:
        raise ValueError('this profile expects a 32-byte X25519 shared secret')
    zero = ctx.public(bytes(32))
    empty_hash = sha256(ctx, [])
    early = hkdf_extract(ctx, zero, zero)
    derived = derive_secret(ctx, early, b'derived', empty_hash)
    handshake = hkdf_extract(ctx, derived, dhe_secret)
    return HandshakeSecrets(
        derive_secret(ctx, handshake, b'c hs traffic', hello_transcript_hash),
        derive_secret(ctx, handshake, b's hs traffic', hello_transcript_hash),
        hkdf_extract(ctx, derive_secret(ctx, handshake, b'derived', empty_hash), zero))


def application_secrets(ctx, master, server_finished_transcript_hash):
    return (derive_secret(ctx, master, b'c ap traffic', server_finished_transcript_hash),
            derive_secret(ctx, master, b's ap traffic', server_finished_transcript_hash))


def traffic_keys(ctx, secret):
    return expand_label(ctx, secret, b'key', [], 16), expand_label(ctx, secret, b'iv', [], 12)


def next_traffic_secret(ctx, secret):
    return expand_label(ctx, secret, b'traffic upd', [], 32)


def finished_verify_data(ctx, secret, transcript_hash):
    if byte_length(transcript_hash) != 32:
        raise ValueError('TLS transcript hash must be SHA-256')
    return HmacSha256(ctx, expand_label(ctx, secret, b'finished', [], 32)).digest(transcript_hash)
