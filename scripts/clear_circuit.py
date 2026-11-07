"""Small cleartext interpreter for the benchmark source and Bristol circuits.

It interprets XOR, AND, and INV directly, with Python integers packing independent
test lanes. This is a correctness oracle adapter, NOT a secure MPC implementation
and NOT an interpreter for MP-SPDZ bytecode. Only the local benchmark source is
executed; no real key or input files are read.
"""

from collections import deque
from dataclasses import dataclass
from pathlib import Path
import runpy
import sys
from types import ModuleType, SimpleNamespace


def execute(source: Path | None, circuits: Path, arguments, input_tokens, *, callback=None):
    streams = [deque(items) for items in input_tokens]
    outputs = []

    @dataclass(frozen=True)
    class Bits:
        value: int
        n: int

        def __xor__(self, other):
            if self.n != other.n:
                raise ValueError('XOR width mismatch')
            return Bits(self.value ^ other.value, self.n)

        def __and__(self, other):
            if self.n != other.n:
                raise ValueError('AND width mismatch')
            return Bits(self.value & other.value, self.n)

        def __bool__(self):
            raise TypeError('a shared bit cannot control a Python branch')

        def bit_decompose(self):
            return [Bits((self.value >> i) & 1, 1) for i in range(self.n)]

        def reveal(self):
            return self

        def print_reg(self):
            outputs.append(self.value)

    class BitType:
        def __init__(self, n):
            self.n = n

        def __call__(self, value):
            if not 0 <= value < 1 << self.n:
                raise ValueError('constant outside bit width')
            return Bits(value, self.n)

        def bit_compose(self, parts):
            if len(parts) != self.n or any(x.n != 1 for x in parts):
                raise ValueError('composition width mismatch')
            return Bits(sum(x.value << i for i, x in enumerate(parts)), self.n)

    class Vector:
        def __init__(self, words=None):
            self.v = []
            if words is not None:
                width = words[0].n
                if any(x.n != width for x in words):
                    raise ValueError('vector word width mismatch')
                self.v = [Bits(sum(((x.value >> bit) & 1) << lane
                                   for lane, x in enumerate(words)), len(words))
                          for bit in range(width)]

        @classmethod
        def from_vec(cls, columns):
            result = cls()
            result.v = list(columns)
            if not result.v or any(x.n != result.v[0].n for x in result.v):
                raise ValueError('vector lane count mismatch')
            return result

        @staticmethod
        def get_type(width):
            class InputVector:
                @staticmethod
                def get_input_from(party, size=1):
                    return Vector([BitType(width)(streams[party].popleft()) for _ in range(size)])
            return InputVector

        def elements(self):
            return [Bits(sum(((x.value >> lane) & 1) << bit
                             for bit, x in enumerate(self.v)), len(self.v))
                    for lane in range(self.v[0].n)]

    class Circuit:
        def __init__(self, name):
            if name not in ('aes_128', 'aes_256', 'sha256'):
                raise ValueError('unsupported test circuit')
            rows = [line.split() for line in (circuits / f'{name}.txt').read_text().splitlines()
                    if line.strip()]
            self.gate_count, self.wire_count = map(int, rows[0])
            input_spec, output_spec = [list(map(int, row)) for row in rows[1:3]]
            if input_spec[0] != len(input_spec) - 1 or output_spec[0] != 1:
                raise ValueError('unsupported circuit interface')
            self.input_widths = input_spec[1:]
            self.output_width = output_spec[1]
            self.gates = []
            defined = set(range(sum(self.input_widths)))
            for row in rows[3:]:
                arity, out_count = map(int, row[:2])
                op = row[-1]
                if op not in ('XOR', 'AND', 'INV') or arity != (1 if op == 'INV' else 2):
                    raise ValueError('unsupported gate')
                if out_count != 1 or len(row) != arity + 4:
                    raise ValueError('invalid gate shape')
                ins = list(map(int, row[2:2 + arity]))
                out = int(row[2 + arity])
                if any(i not in defined for i in ins) or out in defined or not 0 <= out < self.wire_count:
                    raise ValueError('invalid wire use')
                defined.add(out)
                self.gates.append((op, ins, out))
            if len(self.gates) != self.gate_count:
                raise ValueError('gate count mismatch')
            if any(i not in defined for i in range(self.wire_count - self.output_width, self.wire_count)):
                raise ValueError('undefined output wire')

        def __call__(self, *inputs):
            if [len(x.v) for x in inputs] != self.input_widths:
                raise ValueError('circuit input width mismatch')
            flattened = [bit for value in inputs for bit in value.v]
            lanes = flattened[0].n
            if any(bit.n != lanes for bit in flattened):
                raise ValueError('circuit lane mismatch')
            wires = [None] * self.wire_count
            wires[:len(flattened)] = [x.value for x in flattened]
            mask = (1 << lanes) - 1
            for op, ins, out in self.gates:
                if op == 'XOR':
                    wires[out] = wires[ins[0]] ^ wires[ins[1]]
                elif op == 'AND':
                    wires[out] = wires[ins[0]] & wires[ins[1]]
                else:
                    wires[out] = wires[ins[0]] ^ mask
            return Vector.from_vec(Bits(x, lanes) for x in wires[-self.output_width:])

    replacements = {name: ModuleType(name) for name in ('circuit', 'Compiler', 'Compiler.GC', 'Compiler.GC.types')}
    replacements['circuit'].Circuit = Circuit
    replacements['Compiler.GC.types'].sbits = SimpleNamespace(get_type=BitType)
    replacements['Compiler.GC.types'].sbitvec = Vector
    previous = {name: sys.modules.get(name) for name in replacements}
    try:
        sys.modules.update(replacements)
        if callback is None:
            runpy.run_path(str(source), init_globals={'program': SimpleNamespace(args=arguments)})
            result = outputs
        else:
            result = callback()
    finally:
        for name, value in previous.items():
            if value is None:
                sys.modules.pop(name, None)
            else:
                sys.modules[name] = value
    if any(streams):
        raise ValueError('unused fixture inputs')
    return result
