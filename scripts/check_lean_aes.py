#!/usr/bin/env python3
"""Check Lean AES circuits against FIPS examples and OpenSSL on public fixtures.

This compiles the generic MPC adapter and checks its public-share interpretation;
it does not execute a native MPC protocol or measure network throughput.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from backend_adapter.boolean import load
from backend_adapter.aig import statistics
from scripts.check_lean_crypto import compile_and_check, evaluate_lanes


def reference(key, block):
    return subprocess.run(['openssl', 'enc', f'-aes-{len(key) * 8}-ecb', '-e', '-nopad',
                           '-nosalt', '-K', key.hex()], input=block, capture_output=True,
                          check=True).stdout


def cases():
    for size, known in ((16, '69c4e0d86a7b0430d8cdb78070b4c55a'),
                        (32, '8ea2b7ca516745bfeafc49904b496089')):
        raw = [bytes(range(size)) + bytes.fromhex('00112233445566778899aabbccddeeff'),
               bytes(size + 16), bytes([255]) * (size + 16)]
        raw += [hashlib.shake_256(f'public-aes-fixture-{size}-{i}'.encode()).digest(size + 16)
                for i in range(3)]
        expected = [reference(x[:size], x[size:]) for x in raw]
        assert expected[0].hex() == known
        yield f'aes{size * 8}-block', raw, expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-backend', action='store_true')
    args = parser.parse_args()
    subprocess.run(['lake', 'build', 'emit_mpc'], cwd=ROOT, check=True)
    records = []
    with tempfile.TemporaryDirectory(prefix='tls-mpc-lean-aes-') as directory:
        for name, raw, expected in cases():
            path = Path(directory) / (name + '.json')
            with path.open('w') as output:
                subprocess.run([str(ROOT / '.lake/build/bin/emit_mpc'), name],
                               stdout=output, check=True, timeout=60)
            image = load(path)
            if evaluate_lanes(image, raw) != expected:
                raise AssertionError(f'AES artifact differs from OpenSSL: {name}')
            record = {'arguments': [name], 'input_bits': image['input_bits'],
                      'output_bits': len(image['outputs']), 'nodes': len(image['nodes']),
                      'adapter_operations': statistics(image), 'fixture_lanes': len(raw),
                      'all_outputs_match': True,
                      'artifact_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
            print(json.dumps(record), flush=True)
            if not args.skip_backend:
                record['mpc_compilations'] = []
                for batch in (1, 16):
                    result = compile_and_check(path, raw, expected, batch)
                    if result['bit_triples'] != record['adapter_operations']['executed_and_gates'] * batch:
                        raise AssertionError(f'Unexpected AND cost: {name}, batch {batch}')
                    record['mpc_compilations'].append(result)
                print(json.dumps({'arguments': [name], 'mpc_compilations': record['mpc_compilations']}), flush=True)
            records.append(record)
    sources = [ROOT / name for name in ('TlsMpc/Aes.lean', 'TlsMpc/AesSbox.lean',
               'TlsMpc/BvConstruct.lean', 'TlsMpc/ByteCircuit.lean', 'TlsMpc/AigExport.lean',
               'Main.lean', 'backend_adapter/aig.py', 'backend_adapter/boolean.py',
               'programs/lean_artifact.mpc', 'specs/aes-sbox.json')]
    sources += [Path(__file__).resolve()]
    report = {'kind': 'lean_aes_artifact_checks', 'cases': records,
              'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in sources},
              'reference': 'https://doi.org/10.6028/NIST.FIPS.197-upd1',
              'native_mpc_executed': False, 'throughput_measured': False,
              'limitations': ['The standard-to-Lean correspondence is a human review obligation.',
                              'Native export, JSON, adapter optimization and backend execution are unverified.',
                              'Block encryption alone does not implement GCM, CBC or an authenticated TLS connection.',
                              'Only public synthetic fixtures are opened by the test harness.']}
    (ROOT / 'benchmarks/results/lean-aes-checks.json').write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
