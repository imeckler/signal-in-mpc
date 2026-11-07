#!/usr/bin/env python3
"""Compare the bounded secret unpadding circuit with a public padding oracle."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

import cryptography
from cryptography.hazmat.primitives.padding import PKCS7

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from backend_adapter.boolean import load
from backend_adapter.aig import statistics
from scripts.check_lean_crypto import compile_and_check, evaluate_lanes


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def reference(block):
    context = PKCS7(128).unpadder()
    try:
        plaintext = context.update(block) + context.finalize()
    except ValueError:
        return bytes(18)
    return bytes([255, len(plaintext)]) + plaintext + bytes(16 - len(plaintext))


def fixtures():
    blocks = []
    # Interleave accept/reject fixtures so vectorized backend checks cover both.
    for count in (16, 1, 15, 2, 14, 3, 13, 4, 12, 5, 11, 6, 10, 7, 9, 8):
        prefix = hashlib.sha256(f'public-unpad-{count}'.encode()).digest()[:16 - count]
        valid = prefix + bytes([count]) * count
        invalid = bytearray(valid)
        invalid[16 - count] ^= 1
        blocks.extend((valid, bytes(invalid)))
    blocks.extend(bytes(15) + bytes([last]) for last in range(256))
    for count in range(2, 17):
        block = bytes(16 - count) + bytes([count]) * count
        for offset in range(16 - count, 15):
            damaged = bytearray(block)
            damaged[offset] ^= 1
            blocks.append(bytes(damaged))
    blocks.extend(hashlib.sha256(f'public-unpad-random-{i}'.encode()).digest()[:16]
                  for i in range(32))
    return blocks, [reference(block) for block in blocks]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-backend', action='store_true')
    options = parser.parse_args()
    subprocess.run(['lake', 'build', 'emit_mpc'], cwd=ROOT, check=True)
    executable = ROOT / '.lake/build/bin/emit_mpc'
    names = ('Main.lean', 'TlsMpc/Signal/Unpad.lean', 'TlsMpc/ByteAuth.lean',
             'TlsMpc/ByteCircuit.lean', 'TlsMpc/AigExport.lean', 'TlsMpc/BvConstruct.lean',
             'backend_adapter/aig.py', 'backend_adapter/boolean.py', 'programs/lean_artifact.mpc',
             'scripts/check_lean_crypto.py')
    paths = [ROOT / name for name in names] + [executable, Path(__file__).resolve()]
    before = {str(path.relative_to(ROOT)): digest(path) for path in paths}
    output = ROOT / '.deps/signal-unpad-artifacts/signal-unpad16.json'
    output.parent.mkdir(parents=True, exist_ok=True)
    started = time.perf_counter()
    with output.open('w') as target:
        subprocess.run([str(executable), 'signal-unpad16'], cwd=ROOT, stdout=target,
                       check=True, timeout=60)
    elapsed = time.perf_counter() - started
    image = load(output)
    raw, expected = fixtures()
    if image['input_bits'] != 128 or len(image['outputs']) != 144:
        raise AssertionError('unexpected fixed unpadding ABI')
    if evaluate_lanes(image, raw) != expected:
        raise AssertionError('Lean unpadding artifact differs from cryptography PKCS7')
    record = {'arguments': ['signal-unpad16'], 'input_bits': 128, 'output_bits': 144,
              'fixture_lanes': len(raw), 'accepted_lanes': sum(x[0] == 255 for x in expected),
              'rejected_lanes': sum(x[0] == 0 for x in expected), 'all_outputs_match': True,
              'artifact_sha256': digest(output), 'native_export_seconds': elapsed,
              'adapter_statistics': statistics(image)}
    if not options.skip_backend:
        record['mpc_compilations'] = [compile_and_check(output, raw, expected, batch)
                                      for batch in (1, 16)]
        for result in record['mpc_compilations']:
            if result['bit_triples'] != record['adapter_statistics']['executed_and_gates'] * result['batch']:
                raise AssertionError('backend gate count differs from adapter statistics')
    after = {str(path.relative_to(ROOT)): digest(path) for path in paths}
    if before != after:
        raise RuntimeError('sources or exporter changed during checks')
    report = {'kind': 'lean_signal_unpad_checks', 'cases': [record], 'source_sha256': before,
              'reference': f'cryptography{cryptography.__version__} PKCS7(128).unpadder',
              'native_mpc_executed': False, 'throughput_measured': False,
              'limitations': ['Final16-byte block only; no AES decryption or complete Signal receive transition.',
                              'Mask, retained length and bytes are secret outputs in the implementation.',
                              'This test harness opens synthetic public fixtures only.',
                              'The actual Rust-reference proof is audited separately.']}
    (ROOT / 'benchmarks/results/lean-signal-unpad-checks.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(record), flush=True)


if __name__ == '__main__':
    main()
