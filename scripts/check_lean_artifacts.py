#!/usr/bin/env python3
"""Export Lean programs, interpret them over test inputs, and compile to MPC.

The mathematical artifact semantics are proved in Lean. These checks exercise
the unverified export/adapter boundary; they are not native MPC executions.
"""

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from backend_adapter.boolean import load
from scripts.clear_circuit import execute
from test_support.circuit import input_tokens

CASES = [('tls-nonce',), ('tls-inner', '7', '3'), ('tls-header', '7', '3'),
         ('authenticated-release', '8')]


def pack(bits):
    padded = list(bits) + [0] * (-len(bits) % 8)
    return bytes(sum(padded[i + j] << (7 - j) for j in range(8)) for i in range(0, len(padded), 8))


def bits(data):
    return [(value >> shift) & 1 for value in data for shift in range(7, -1, -1)]


def fixtures(case, batch):
    raw, expected_bytes = [], []
    for lane in range(batch):
        fixture = hashlib.shake_256(f'lean-artifact-public-fixture-{lane}'.encode()).digest(40)
        if case[0] == 'tls-nonce':
            iv = int.from_bytes(fixture[:12], 'big')
            sequences = [0, 1, 1 << 32, 1 << 63, (1 << 64) - 1]
            sequence = sequences[lane % len(sequences)]
            raw.append(pack([(iv >> i) & 1 for i in range(96)] + [(sequence >> i) & 1 for i in range(64)]))
            expected_bytes.append((iv ^ sequence).to_bytes(12, 'big'))
        elif case[0] == 'tls-inner':
            size, padding = int(case[1]), int(case[2])
            raw.append(fixture[:size])
            expected_bytes.append(fixture[:size] + b'\x17' + bytes(padding))
        elif case[0] == 'tls-header':
            raw.append(b'')
            expected_bytes.append(b'\x17\x03\x03' + (int(case[1]) + 1 + int(case[2]) + 16).to_bytes(2, 'big'))
        else:
            size, valid = int(case[1]), int(lane % 2 == 0)
            raw.append(pack([valid] + bits(fixture[:size])))
            expected_bytes.append(fixture[:size] if valid else bytes(size))
    expected = [int.from_bytes(value[offset:offset + 8], 'big')
                for offset in range(0, len(expected_bytes[0]), 8) for value in expected_bytes]
    return {'raw': raw}, expected


def main():
    backend = ROOT / '.deps/MP-SPDZ'
    emitted = ROOT / 'artifacts/lean'
    copied = backend / 'Programs/Source/lean-artifacts'
    emitted.mkdir(parents=True, exist_ok=True)
    copied.mkdir(parents=True, exist_ok=True)
    subprocess.run(['lake', 'build', 'emit_mpc'], cwd=ROOT, check=True)
    source = ROOT / 'programs/lean_artifact.mpc'
    shutil.copy2(source, backend / 'Programs/Source/lean_artifact.mpc')
    environment = os.environ.copy()
    environment['PYTHONPATH'] = str(ROOT) + os.pathsep + environment.get('PYTHONPATH', '')
    records = []
    for case in CASES:
        name = '-'.join(case)
        exported = subprocess.run([str(ROOT / '.lake/build/bin/emit_mpc'), *case], cwd=ROOT,
                                  check=True, text=True, capture_output=True)
        path = emitted / f'{name}.json'
        path.write_text(exported.stdout)
        image = load(path)
        shutil.copy2(path, copied / path.name)
        for batch in (1, 16):
            arguments = [name, str(batch), '5']
            program_name = 'lean_artifact-' + '-'.join(arguments)
            directory = ROOT / 'benchmarks/results/raw' / program_name
            directory.mkdir(parents=True, exist_ok=True)
            command = [sys.executable, './compile.py', '-M', '-B', '128', 'lean_artifact', *arguments]
            compiled = subprocess.run(command, cwd=backend, env=environment, capture_output=True,
                                      text=True, timeout=300)
            log = compiled.stdout + compiled.stderr
            (directory / 'compile.log').write_text(log)
            if compiled.returncode:
                raise RuntimeError(log[-4000:])
            inputs, expected = fixtures(case, batch)
            previous = Path.cwd()
            try:
                os.chdir(backend)
                observed = execute(source, backend / 'Programs/Circuits',
                                   ['lean_artifact', *arguments], input_tokens(inputs))
            finally:
                os.chdir(previous)
            if observed != expected:
                raise AssertionError(f'{name}, batch {batch}: exported artifact output mismatch')
            triples = re.findall(r'(\d+) bit triples', log)
            records.append({'artifact': name, 'batch': batch, 'input_bits': image['input_bits'],
                            'output_bits': len(image['outputs']), 'all_outputs_match': True,
                            'bit_triples': int(triples[-1]) if triples else 0,
                            'output_values_checked': len(expected),
                            'artifact_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                            'bytecode_sha256': hashlib.sha256(
                                (backend / f'Programs/Bytecode/{program_name}-0.bc').read_bytes()).hexdigest()})
            print(json.dumps(records[-1]), flush=True)
    paths = [ROOT / 'Main.lean', source, ROOT / 'backend_adapter/boolean.py', Path(__file__).resolve(),
             ROOT / 'scripts/clear_circuit.py', ROOT / 'test_support/circuit.py']
    paths += sorted((ROOT / 'TlsMpc').glob('*.lean'))
    report = {'kind': 'lean_export_and_mpc_adapter_differential_checks', 'cases': records,
              'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
              'verified_boundary': 'Lean source expressions through numeric instruction export and ideal evaluation',
              'limitations': ['JSON transport and execution adapter are unverified.',
                              'MP-SPDZ bytecode is compiled but not executed by this check.',
                              'This suite covers framing, nonce, and conditional release only.',
                              'Separate crypto and Signal reports record their own coverage.',
                              'No native MPC execution or live TLS/Signal interoperability is tested.']}
    (ROOT / 'benchmarks/results/lean-artifact-checks.json').write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
