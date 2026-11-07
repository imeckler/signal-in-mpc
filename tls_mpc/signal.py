"""Established Signal symmetric-chain circuits, pinned to libsignal 0.106.1.

Includes the v4 SignalMessage encoding and authenticated addresses. It is not a
complete Signal session implementation: DH/SPQR ratchets, prekeys, skipped keys,
sealed sender, and persistence are separate work. The PQ contribution must be
provided explicitly from the session's SPQR step. Passing None models SPQR's
explicit no-key result; it must never be used to silently skip that step.

All identifiers, public keys, plaintext, wire messages, and next chain keys stay
shared. Sizes, counters and optional-field presence are public circuit shape.
"""

from dataclasses import dataclass

from .backend import byte_length, equal, mask, select
from .crypto import HmacSha256, cbc_open, cbc_seal, hkdf_expand, hkdf_extract


def _varint(value):
    if not isinstance(value, int) or not 0 <= value < 1 << 32:
        raise ValueError('expected a public uint32')
    result = bytearray()
    while value > 127:
        result.append((value & 127) | 128)
        value >>= 7
    return bytes(result + bytes([value]))


def _field_prefix(number, length):
    return _varint((number << 3) | 2) + _varint(length)


@dataclass(frozen=True)
class MessageKeys:
    cipher: list
    mac: list
    iv: list
    next_chain: list


def chain_step(ctx, chain_key, *, pq_key):
    if byte_length(chain_key) != 32 or (pq_key is not None and byte_length(pq_key) != 32):
        raise ValueError('Signal chain/PQ keys must be 32 bytes')
    chain_mac = HmacSha256(ctx, chain_key)
    seed = chain_mac.digest(ctx.public(b'\x01'))
    next_chain = chain_mac.digest(ctx.public(b'\x02'))
    prk = hkdf_extract(ctx, pq_key, seed)
    material = hkdf_expand(ctx, prk, ctx.public(b'WhisperMessageKeys'), 80)
    return MessageKeys(material[:256], material[256:512], material[512:], next_chain)


@dataclass(frozen=True)
class PqStep:
    key: list | None
    message: list


@dataclass(frozen=True)
class PreparedSend:
    wire: list
    next_chain: list
    next_counter: int


def _check_identity_keys(sender_identity, receiver_identity, ratchet_key):
    if any(byte_length(key) != 33 for key in (sender_identity, receiver_identity, ratchet_key)):
        raise ValueError('Signal public keys must include their 0x05 serialization prefix')


def seal_message(ctx, chain_key, plaintext, *, counter, previous_counter, ratchet_key,
                 sender_identity, receiver_identity, pq: PqStep, addresses):
    """Prepare a v4 message. Reserve/commit the next state once before releasing it."""
    _check_identity_keys(sender_identity, receiver_identity, ratchet_key)
    if not 0 <= counter < (1 << 32) - 1:
        raise ValueError('Signal chain counter cannot wrap')
    if addresses is not None and byte_length(addresses) != 36:
        raise ValueError('addresses must be two (17-byte ServiceId, 1-byte device) pairs')
    keys = chain_step(ctx, chain_key, pq_key=pq.key)
    ciphertext = cbc_seal(ctx, keys.cipher, keys.iv, plaintext)
    wire = ctx.public(b'\x44' + _field_prefix(1, 33)) + ratchet_key
    wire += ctx.public(b'\x10' + _varint(counter) + b'\x18' + _varint(previous_counter)
                       + _field_prefix(4, byte_length(ciphertext))) + ciphertext
    if pq.message:
        wire += ctx.public(_field_prefix(5, byte_length(pq.message))) + pq.message
    if addresses is not None:
        wire += ctx.public(_field_prefix(6, 36)) + addresses
    tag = HmacSha256(ctx, keys.mac).digest(sender_identity + receiver_identity + wire)[:64]
    return PreparedSend(wire + tag, keys.next_chain, counter + 1)


@dataclass(frozen=True)
class MessageShape:
    """Public canonical-layout profile for an expected, in-order v4 message.

    This restricted decoder rejects alternate protobuf encodings and unexpected
    counters/ratchet transitions. A general oblivious parser is still required.
    """
    counter: int
    previous_counter: int
    ciphertext_bytes: int
    pq_bytes: int
    has_addresses: bool


@dataclass(frozen=True)
class OpenedMessage:
    valid: object
    content: list
    content_length: list
    next_chain: list  # selected old chain on failure


def open_message(ctx, chain_key, wire, *, shape: MessageShape, expected_ratchet_key,
                 sender_identity, receiver_identity, pq_key, expected_addresses):
    """Authenticate the original serialized bytes before making plaintext usable.

    Does not commit a chain counter or SPQR state. The surrounding session machine
    must commit all state atomically iff valid, while keeping valid shared unless
    an explicit error-disclosure policy permits opening it.
    """
    _check_identity_keys(sender_identity, receiver_identity, expected_ratchet_key)
    if (not 0 <= shape.counter < (1 << 32) - 1 or shape.ciphertext_bytes <= 0
            or shape.ciphertext_bytes % 16 or shape.ciphertext_bytes >= 1 << 16 or shape.pq_bytes < 0):
        raise ValueError('invalid expected Signal message dimensions')
    if shape.has_addresses and (expected_addresses is None or byte_length(expected_addresses) != 36):
        raise ValueError('expected shared addresses are required')
    fields = [('literal', b'\x44' + _field_prefix(1, 33)), ('ratchet', 33),
              ('literal', b'\x10' + _varint(shape.counter) + b'\x18' + _varint(shape.previous_counter)
               + _field_prefix(4, shape.ciphertext_bytes)), ('ciphertext', shape.ciphertext_bytes)]
    if shape.pq_bytes:
        fields += [('literal', _field_prefix(5, shape.pq_bytes)), ('pq', shape.pq_bytes)]
    if shape.has_addresses:
        fields += [('literal', _field_prefix(6, 36)), ('addresses', 36)]
    expected_length = sum(len(value) if name == 'literal' else value for name, value in fields) + 8
    if byte_length(wire) != expected_length:
        raise ValueError('wire length differs from public message profile')
    valid, offset, parsed = ctx.one, 0, {}
    for name, value in fields:
        size = len(value) if name == 'literal' else value
        part = wire[offset:offset + 8 * size]
        offset += 8 * size
        if name == 'literal':
            valid = valid & equal(ctx, part, ctx.public(value))
        else:
            parsed[name] = part
    valid = valid & equal(ctx, parsed['ratchet'], expected_ratchet_key)
    if shape.has_addresses:
        valid = valid & equal(ctx, parsed['addresses'], expected_addresses)
    keys = chain_step(ctx, chain_key, pq_key=pq_key)
    tag = HmacSha256(ctx, keys.mac).digest(sender_identity + receiver_identity + wire[:-64])[:64]
    valid = valid & equal(ctx, tag, wire[-64:])
    padded_valid, plaintext, length = cbc_open(ctx, keys.cipher, keys.iv, parsed['ciphertext'])
    valid = valid & padded_valid
    return OpenedMessage(valid, mask(ctx, valid, plaintext), mask(ctx, valid, length),
                         select(valid, keys.next_chain, chain_key))


def pad_content(ctx, serialized_content, *, block_size=80):
    """Signal application's 0x80/zero padding; call before seal_message if needed."""
    length = byte_length(serialized_content)
    if block_size < 1:
        raise ValueError('padding block size must be positive')
    return serialized_content + ctx.public(b'\x80' + bytes((-length - 1) % block_size))
