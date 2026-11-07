"""Independent byte-level oracles. Test code only; these use unshared secrets."""

import hmac
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes


def mac(key, message):
    return hmac.digest(key, message, 'sha256')


def hkdf(ikm, salt, info, length):
    prk = mac(bytes(32) if salt is None else salt, ikm)
    previous, output = b'', b''
    for counter in range(1, (length + 31) // 32 + 1):
        previous = mac(prk, previous + info + bytes([counter]))
        output += previous
    return output[:length]


def cbc(key, iv, plaintext, *, pad=True):
    if pad:
        padding = 16 - len(plaintext) % 16
        plaintext += bytes([padding]) * padding
    encryptor = Cipher(algorithms.AES(key), modes.CBC(iv)).encryptor()
    return encryptor.update(plaintext) + encryptor.finalize()


def varint(value):
    result = []
    while True:
        low = value & 127
        value >>= 7
        result.append(low | (128 if value else 0))
        if not value:
            return bytes(result)


def signal_reference(chain, plaintext, pq_key, pq_message, addresses, ratchet, sender, recipient,
                     counter=0, previous=0, *, raw_padded=None):
    # Wire layout from pinned wire.proto/protocol.rs, independent of circuit code.
    material = hkdf(mac(chain, b'\x01'), pq_key, b'WhisperMessageKeys', 80)
    encrypted = cbc(material[:32], material[64:], plaintext if raw_padded is None else raw_padded,
                    pad=raw_padded is None)
    fields = b'\x0a\x21' + ratchet + b'\x10' + varint(counter) + b'\x18' + varint(previous)
    fields += b'\x22' + varint(len(encrypted)) + encrypted
    if pq_message:
        fields += b'\x2a' + varint(len(pq_message)) + pq_message
    if addresses is not None:
        fields += b'\x32\x24' + addresses
    message = b'\x44' + fields
    return message + mac(material[32:64], sender + recipient + message)[:8]
