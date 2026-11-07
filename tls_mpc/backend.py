"""MP-SPDZ adapter. Bits are packed across independent lanes, MSB first in bytes.

The computational modules never reveal values. Public lengths and Python loop
bounds determine the circuit shape. Keys and data enter through private inputs.
This adapter and the Python compiler path are not yet verified by Lean.
"""


class MpcBackend:
    def __init__(self, lanes=1):
        if not isinstance(lanes, int) or lanes < 1:
            raise ValueError('lanes must be a positive public integer')
        from Compiler.GC.types import sbits, sbitvec
        from circuit import Circuit
        self.lanes, self.vec = lanes, sbitvec
        self.word = sbits.get_type(lanes)
        self.zero = self.word(0)
        self.one = self.word((1 << lanes) - 1)
        self.circuit_type, self.circuits = Circuit, {}

    def bit(self, public_value):
        if public_value not in (0, 1):
            raise ValueError('public bit must be 0 or 1')
        return self.one if public_value else self.zero

    def public(self, data: bytes):
        if not isinstance(data, bytes):
            raise TypeError('public constants must be bytes')
        return [self.bit((byte >> shift) & 1) for byte in data for shift in range(7, -1, -1)]

    def input_bytes(self, length, party):
        if length < 0 or party < 0:
            raise ValueError('invalid private input dimensions')
        result = []
        for offset in range(0, length, 8):
            width = min(8, length - offset) * 8
            vector = self.vec.get_type(width).get_input_from(party, size=self.lanes)
            result.extend(reversed(vector.v))
        return result

    def shared_input(self, length, parties):
        if length < 0 or parties < 1:
            raise ValueError('invalid input dimensions')
        result = self.public(bytes(length))
        for party in range(parties):
            result = xor(result, self.input_bytes(length, party))
        return result

    def circuit(self, name, *inputs):
        if name not in self.circuits:
            self.circuits[name] = self.circuit_type(name)
        vectors = [self.vec.from_vec(list(reversed(value))) for value in inputs]
        return list(reversed(self.circuits[name](*vectors).v))

    def aes(self, key, block):
        if len(block) != 128 or len(key) not in (128, 256):
            raise ValueError('AES requires a 16-byte block and a 16/32-byte key')
        return self.circuit('aes_128' if len(key) == 128 else 'aes_256', key, block)

    def sha256_compress(self, state, block):
        if len(state) != 256 or len(block) != 512:
            raise ValueError('invalid SHA-256 compression dimensions')
        return self.circuit('sha256', block, state)


def byte_length(bits):
    if len(bits) % 8:
        raise ValueError('expected whole bytes')
    return len(bits) // 8


def xor(left, right):
    if len(left) != len(right):
        raise ValueError('XOR length mismatch')
    return [a ^ b for a, b in zip(left, right)]


def select(condition, yes, no):
    if len(yes) != len(no):
        raise ValueError('selection length mismatch')
    return [b ^ (condition & (a ^ b)) for a, b in zip(yes, no)]


def reduce_and(ctx, bits):
    values = list(bits)
    if not values:
        return ctx.one
    while len(values) > 1:
        values = [values[i] & values[i + 1] for i in range(0, len(values) - 1, 2)] + values[len(values) // 2 * 2:]
    return values[0]


def equal(ctx, left, right):
    return reduce_and(ctx, [bit ^ ctx.one for bit in xor(left, right)])


def bit_or(a, b):
    return a ^ b ^ (a & b)


def mask(ctx, valid, bits):
    return [valid & bit for bit in bits]
