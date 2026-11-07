"""Synthetic fixture sharing and cleartext circuit evaluation, ONLY for tests."""

from pathlib import Path
from random import Random

from scripts.clear_circuit import execute
from tls_mpc.backend import MpcBackend

ROOT = Path(__file__).resolve().parents[1]
CIRCUITS = ROOT / '.deps/MP-SPDZ/Programs/Circuits'


def input_tokens(inputs, parties=5):
    """Input order: named value, owning party, 8-byte chunk, then SIMD lane."""
    lanes = len(next(iter(inputs.values()))) if inputs else 1
    random = Random(972105)  # public, deterministic TEST material only
    tokens = [[] for _ in range(parties)]
    for values in inputs.values():
        if len(values) != lanes or any(len(v) != len(values[0]) for v in values):
            raise ValueError('all test lanes must have the same public shape')
        fragments = [[] for _ in range(parties)]
        for value in values:
            others = [random.randbytes(len(value)) for _ in range(parties - 1)]
            final = bytearray(value)
            for fragment in others:
                for i, byte in enumerate(fragment):
                    final[i] ^= byte
            for party, fragment in enumerate(others + [bytes(final)]):
                fragments[party].append(fragment)
        for party in range(parties):
            for offset in range(0, len(values[0]), 8):
                for lane in range(lanes):
                    tokens[party].append(int.from_bytes(fragments[party][lane][offset:offset + 8], 'big'))

    return tokens


def evaluate(inputs, computation, *, parties=5):
    """Each dict value is a list of equal-size byte strings, one per SIMD lane."""
    lanes = len(next(iter(inputs.values()))) if inputs else 1
    def run():
        ctx = MpcBackend(lanes)
        shared = {name: ctx.shared_input(len(values[0]), parties) for name, values in inputs.items()}
        return computation(ctx, shared)

    return execute(None, CIRCUITS, [], input_tokens(inputs, parties), callback=run)


def opened(bits, lane=0):
    """Inspect the cleartext test model. This helper must never enter MPC code."""
    if len(bits) % 8:
        raise ValueError('expected bytes')
    return bytes(sum(((bits[i + j].value >> lane) & 1) << (7 - j) for j in range(8))
                 for i in range(0, len(bits), 8))


def bit_value(bit, lane=0):
    return (bit.value >> lane) & 1
