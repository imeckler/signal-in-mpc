"""Fixed-shape cryptographic circuits. All byte strings are lists of shared bits.

Only public sizes/indices control Python branches. AES encryption and SHA-256
compression use pinned Bristol circuits. GHASH and AES decryption are expressed
directly in XOR/AND gates. No function opens a key, plaintext, or computed tag.
"""

from .backend import byte_length, equal, mask, xor

SHA256_IV = bytes.fromhex('6a09e667bb67ae853c6ef372a54ff53a510e527f9b05688c1f83d9ab5be0cd19')


def sha256(ctx, data, *, state=None, prefix_bytes=0):
    length = byte_length(data)
    if prefix_bytes < 0 or prefix_bytes % 64 or (prefix_bytes + length) * 8 >= 1 << 64:
        raise ValueError('invalid SHA-256 prefix or length')
    state = ctx.public(SHA256_IV) if state is None else state
    padding = b'\x80' + bytes((55 - length) % 64) + ((length + prefix_bytes) * 8).to_bytes(8, 'big')
    padded = data + ctx.public(padding)
    for offset in range(0, len(padded), 512):
        state = ctx.sha256_compress(state, padded[offset:offset + 512])
    return state


class HmacSha256:
    """Prepare the two key-dependent compression states once per shared key."""
    def __init__(self, ctx, key):
        length = byte_length(key)
        if length > 64:
            key, length = sha256(ctx, key), 32
        key = key + ctx.public(bytes(64 - length))
        initial = ctx.public(SHA256_IV)
        self.ctx = ctx
        self.inner = ctx.sha256_compress(initial, xor(key, ctx.public(b'\x36' * 64)))
        self.outer = ctx.sha256_compress(initial, xor(key, ctx.public(b'\x5c' * 64)))

    def digest(self, data):
        inner = sha256(self.ctx, data, state=self.inner, prefix_bytes=64)
        return sha256(self.ctx, inner, state=self.outer, prefix_bytes=64)


def hkdf_extract(ctx, salt, ikm):
    return HmacSha256(ctx, ctx.public(bytes(32)) if salt is None else salt).digest(ikm)


def hkdf_expand(ctx, prk, info, length):
    if byte_length(prk) != 32 or not 0 <= length <= 255 * 32:
        raise ValueError('invalid HKDF key or output length')
    if length == 0:
        return []
    mac, previous, result = HmacSha256(ctx, prk), [], []
    for counter in range(1, (length + 31) // 32 + 1):
        previous = mac.digest(previous + info + ctx.public(bytes([counter])))
        result.extend(previous)
    return result[:length * 8]


def _polynomial_product(ctx, a, b):
    """Karatsuba over GF(2); coefficient order is ascending."""
    n = len(a)
    if n != len(b) or n == 0 or n & (n - 1):
        raise ValueError('polynomial width must be a power of two')
    if n == 1:
        return [a[0] & b[0]]
    half = n // 2
    low = _polynomial_product(ctx, a[:half], b[:half])
    high = _polynomial_product(ctx, a[half:], b[half:])
    middle = _polynomial_product(ctx, xor(a[:half], a[half:]), xor(b[:half], b[half:]))
    middle = xor(xor(middle, low), high)
    result = [ctx.zero] * (2 * n - 1)
    for values, offset in ((low, 0), (middle, half), (high, n)):
        for i, value in enumerate(values):
            result[offset + i] = result[offset + i] ^ value
    return result


def _reduce_polynomial(values, degree, offsets):
    result = list(values)
    for i in range(len(result) - 1, degree - 1, -1):
        for offset in offsets:
            result[i - degree + offset] = result[i - degree + offset] ^ result[i]
    return result[:degree]


def gcm_multiply(ctx, a, b):
    if len(a) != 128 or len(b) != 128:
        raise ValueError('GHASH operands must have 128 bits')
    # NIST's MSB is coefficient x^0 (unlike the AES byte-field encoding).
    return _reduce_polynomial(_polynomial_product(ctx, a, b), 128, (0, 1, 2, 7))


def ghash(ctx, h, aad, ciphertext):
    a_len, c_len = byte_length(aad), byte_length(ciphertext)
    if max(a_len, c_len) * 8 >= 1 << 64:
        raise ValueError('GHASH length overflow')
    blocks = aad + ctx.public(bytes((-a_len) % 16))
    blocks += ciphertext + ctx.public(bytes((-c_len) % 16))
    blocks += ctx.public((8 * a_len).to_bytes(8, 'big') + (8 * c_len).to_bytes(8, 'big'))
    value = ctx.public(bytes(16))
    for offset in range(0, len(blocks), 128):
        value = gcm_multiply(ctx, xor(value, blocks[offset:offset + 128]), h)
    return value


def _gcm_ctr(ctx, key, nonce, data):
    length = byte_length(data)
    if byte_length(nonce) != 12 or (length + 15) // 16 >= (1 << 32) - 1:
        raise ValueError('unsupported GCM nonce or length')
    result = []
    for offset in range(0, len(data), 128):
        stream = ctx.aes(key, nonce + ctx.public((2 + offset // 128).to_bytes(4, 'big')))
        chunk = data[offset:offset + 128]
        result += xor(chunk, stream[:len(chunk)])
    return result


def gcm_seal(ctx, key, nonce, plaintext, aad):
    ciphertext = _gcm_ctr(ctx, key, nonce, plaintext)
    h = ctx.aes(key, ctx.public(bytes(16)))
    tag_mask = ctx.aes(key, nonce + ctx.public(b'\x00\x00\x00\x01'))
    tag = xor(tag_mask, ghash(ctx, h, aad, ciphertext))
    return ciphertext, tag


def gcm_open(ctx, key, nonce, ciphertext, aad, tag):
    if byte_length(tag) != 16:
        raise ValueError('GCM requires a full 16-byte tag')
    h = ctx.aes(key, ctx.public(bytes(16)))
    tag_mask = ctx.aes(key, nonce + ctx.public(b'\x00\x00\x00\x01'))
    expected = xor(tag_mask, ghash(ctx, h, aad, ciphertext))
    valid = equal(ctx, tag, expected)
    plaintext = _gcm_ctr(ctx, key, nonce, ciphertext)
    return valid, mask(ctx, valid, plaintext)


def cbc_seal(ctx, key, iv, plaintext):
    length = byte_length(plaintext)
    if byte_length(key) != 32 or byte_length(iv) != 16:
        raise ValueError('Signal CBC requires a 32-byte key and 16-byte IV')
    pad = 16 - length % 16
    padded = plaintext + ctx.public(bytes([pad]) * pad)
    previous, result = iv, []
    for offset in range(0, len(padded), 128):
        previous = ctx.aes(key, xor(previous, padded[offset:offset + 128]))
        result.extend(previous)
    return result


def _gf8_multiply(ctx, a, b):
    product = _polynomial_product(ctx, list(reversed(a)), list(reversed(b)))
    return list(reversed(_reduce_polynomial(product, 8, (0, 1, 3, 4))))


def _gf8_square(ctx, value):
    polynomial = [ctx.zero] * 15
    for i, bit in enumerate(reversed(value)):
        polynomial[2 * i] = bit
    return list(reversed(_reduce_polynomial(polynomial, 8, (0, 1, 3, 4))))


def _gf8_inverse(ctx, a):
    a2 = _gf8_square(ctx, a)
    a3 = _gf8_multiply(ctx, a2, a)
    a6 = _gf8_square(ctx, a3)
    a12 = _gf8_square(ctx, a6)
    a15 = _gf8_multiply(ctx, a12, a3)
    a240 = a15
    for _ in range(4):
        a240 = _gf8_square(ctx, a240)
    return _gf8_multiply(ctx, _gf8_multiply(ctx, a240, a12), a2)


def _aes_sbox(ctx, byte):
    bits = list(reversed(_gf8_inverse(ctx, byte)))
    return list(reversed([bits[i] ^ bits[(i + 4) % 8] ^ bits[(i + 5) % 8]
                          ^ bits[(i + 6) % 8] ^ bits[(i + 7) % 8]
                          ^ ctx.bit((0x63 >> i) & 1) for i in range(8)]))


def _aes_inv_sbox(ctx, byte):
    bits = list(reversed(byte))
    inverse_affine = list(reversed([bits[(i + 2) % 8] ^ bits[(i + 5) % 8]
                                    ^ bits[(i + 7) % 8] ^ ctx.bit((5 >> i) & 1)
                                    for i in range(8)]))
    return _gf8_inverse(ctx, inverse_affine)


def aes256_expand(ctx, key):
    if byte_length(key) != 32:
        raise ValueError('AES-256 requires a 32-byte key')
    words = [[key[j:j + 8] for j in range(i, i + 32, 8)] for i in range(0, 256, 32)]
    rcon = 1
    for i in range(8, 60):
        temp = words[i - 1]
        if i % 8 == 0:
            temp = [_aes_sbox(ctx, byte) for byte in temp[1:] + temp[:1]]
            temp[0] = xor(temp[0], ctx.public(bytes([rcon])))
            rcon = ((rcon << 1) ^ (0x11b if rcon & 0x80 else 0)) & 0xff
        elif i % 8 == 4:
            temp = [_aes_sbox(ctx, byte) for byte in temp]
        words.append([xor(a, b) for a, b in zip(words[i - 8], temp)])
    return [[bit for word in words[i:i + 4] for byte in word for bit in byte]
            for i in range(0, 60, 4)]


def _xtime(ctx, byte):
    return xor(byte[1:] + [ctx.zero],
               [byte[0] if (0x1b >> shift) & 1 else ctx.zero for shift in range(7, -1, -1)])


def aes256_decrypt_block(ctx, round_keys, block):
    if len(round_keys) != 15 or byte_length(block) != 16:
        raise ValueError('invalid AES decryption dimensions')
    state = xor(block, round_keys[14])
    for round_index in range(13, -1, -1):
        columns = [state[i:i + 8] for i in range(0, 128, 8)]
        shifted = [columns[4 * ((column - row) % 4) + row]
                   for column in range(4) for row in range(4)]
        state = xor(sum((_aes_inv_sbox(ctx, byte) for byte in shifted), []), round_keys[round_index])
        if round_index:
            columns = [state[i:i + 8] for i in range(0, 128, 8)]
            result = []
            for start in range(0, 16, 4):
                base = columns[start:start + 4]
                x2 = [_xtime(ctx, a) for a in base]
                x4 = [_xtime(ctx, a) for a in x2]
                x8 = [_xtime(ctx, a) for a in x4]
                for row in range(4):
                    out = ctx.public(b'\x00')
                    for j, coefficient in enumerate((14, 11, 13, 9)):
                        i = (row + j) % 4
                        for power, values in ((1, base), (2, x2), (4, x4), (8, x8)):
                            if coefficient & power:
                                out = xor(out, values[i])
                    result.extend(out)
            state = result
    return state


def cbc_open(ctx, key, iv, ciphertext):
    length = byte_length(ciphertext)
    if byte_length(iv) != 16 or length == 0 or length % 16 or length >= 1 << 16:
        raise ValueError('invalid CBC record dimensions')
    keys, previous, plaintext = aes256_expand(ctx, key), iv, []
    for offset in range(0, len(ciphertext), 128):
        block = ciphertext[offset:offset + 128]
        plaintext += xor(aes256_decrypt_block(ctx, keys, block), previous)
        previous = block
    valid, content_length = ctx.zero, ctx.public(bytes(2))
    candidates = []
    for padding in range(1, 17):
        matches = equal(ctx, plaintext[-8 * padding:], ctx.public(bytes([padding]) * padding))
        candidates.append(matches)
        valid = valid ^ matches  # disjoint: the final byte selects exactly one candidate
        content_length = xor(content_length, mask(ctx, matches, ctx.public((length - padding).to_bytes(2, 'big'))))
    unpadded = []
    for i in range(length):
        keep = ctx.zero
        for padding, candidate in enumerate(candidates, 1):
            if i < length - padding:
                keep = keep ^ candidate
        unpadded += mask(ctx, keep, plaintext[i * 8:i * 8 + 8])
    return valid, unpadded, content_length
