#!/usr/bin/env python3
"""Differential public evaluation of packed vs original numeric AIG traversal."""
from pathlib import Path
import itertools
import json
import random
import sys
import hashlib
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from backend_adapter.aig import execute as scalar
from backend_adapter.aig_packed import execute as packed, plan


def evaluate(image, bits, width):
    return packed(image, bits, 0, 1,
                  lambda values: sum(x << i for i, x in enumerate(values)),
                  lambda value, count: [(value >> i) & 1 for i in range(count)],
                  lambda count, value: value, lanes=width)


def main():
    rng = random.Random(982731)
    checked = 0
    for size in (1, 2, 4, 8):
        for trial in range(12):
            nodes = [[0]] + [[1, 0, size, bit] for bit in range(size)]
            for _ in range(120):
                a, b = rng.randrange(len(nodes)), rng.randrange(len(nodes))
                ai, bi = rng.randrange(2), rng.randrange(2)
                if rng.randrange(3) == 0:
                    # Force XOR recovery, either source ordering, complements.
                    left = len(nodes)
                    nodes.append([2, a, ai, b, bi])
                    nodes.append([2, b, 1-bi, a, 1-ai])
                    nodes.append([2, left, 1, left+1, 1])
                else:
                    nodes.append([2, a, ai, b, bi])
            image = {'format': 'tls-mpc-aig-v1', 'input_bits': size, 'input_widths': [size],
                     'nodes': nodes, 'outputs': [[index, rng.randrange(2)] for index in range(len(nodes))]}
            for bits in itertools.product((0, 1), repeat=size):
                expected = scalar(image, bits, 0, 1, optimize=False)
                assert scalar(image, bits, 0, 1) == expected
                for width in (1, 7, 32, 64):
                    assert evaluate(image, bits, width) == expected, (size, trial, width)
                    checked += 1
    root = Path(__file__).resolve().parents[1]
    artifact = root/'artifacts/lean/handshake/tls-open-handshake-record-58.json'
    image = json.loads(artifact.read_text())
    for _ in range(4):
        bits = [rng.randrange(2) for _ in range(image['input_bits'])]
        assert evaluate(image, bits, 64) == scalar(image, bits, 0, 1)
        checked += 1
    key, iv, content = bytes(range(16)), bytes(range(12)), bytes(range(36))
    handshake_cases = []
    for kind in (21, 22, 23):
        header = bytes.fromhex('1703030035')
        wire = header + AESGCM(key).encrypt(iv, content+bytes([kind]), header)
        for tamper in (False, True):
            record = wire[:-1]+bytes([wire[-1]^1]) if tamper else wire
            bits = [(byte >> bit) & 1 for byte in key+iv+bytes(8)+record for bit in range(7,-1,-1)]
            result = evaluate(image, bits, 64)
            output = bytes(sum(result[j+i] << (7-i) for i in range(8)) for j in range(0,len(result),8))
            if tamper or kind == 23:
                assert output == bytes(41)
            else:
                assert output == bytes([255,kind,0,36])+content+bytes(1)
            handshake_cases.append({'type':kind,'bad_tag':tamper})
    roots, groups = plan(image)
    source = root/'backend_adapter/aig_packed.py'
    report = {'differential_evaluations': checked, 'native_mpc_executed': False,
              'packed_handshake_gate_cases': handshake_cases,
              'scope': 'public integer packing vs original AIG, including all-node outputs and XOR motifs',
              'tls_58_and_depth': max((depth for (depth, _, _), _ in groups), default=0),
              'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest()}
    (root/'benchmarks/results/tls-packed-aig-checks.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
