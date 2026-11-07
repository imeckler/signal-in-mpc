#!/usr/bin/env python3
"""Public-fixture checks for Lean AES-128-GCM against cryptography/OpenSSL."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

import cryptography
from cryptography.exceptions import InvalidTag
from cryptography.hazmat.primitives.ciphers.aead import AESGCM

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from backend_adapter.boolean import load
from backend_adapter.aig import statistics
from scripts.check_lean_crypto import compile_and_check, evaluate_lanes


def cases():
    for aad_size, size in ((0, 0), (0, 16), (5, 1), (5, 15), (5, 16), (5, 17), (20, 60), (17, 31)):
        raw = [bytes(28 + aad_size + size)]
        raw += [hashlib.shake_256(f'public-gcm-{aad_size}-{size}-{i}'.encode()).digest(28 + aad_size + size)
                for i in range(3)]
        expected = [AESGCM(x[:16]).encrypt(x[16:28], x[28 + aad_size:], x[28:28 + aad_size]) for x in raw]
        if (aad_size, size) == (0, 0):
            assert expected[0].hex() == '58e2fccefa7e3061367f1d57a4e7455a'
        if (aad_size, size) == (0, 16):
            assert expected[0].hex() == '0388dace60b6a392f328c2b971b2fe78ab6e47d42cec13bdf53a67b21257bddf'
        yield ('gcm-seal', str(aad_size), str(size)), raw, expected
    for aad_size, size in ((0, 0), (0, 16), (5, 17), (20, 60)):
        raw = []
        for lane in range(4):
            source = hashlib.shake_256(f'public-gcm-open-{aad_size}-{size}-{lane}'.encode()).digest(
                28 + aad_size + size)
            sealed = AESGCM(source[:16]).encrypt(source[16:28], source[28 + aad_size:], source[28:28 + aad_size])
            valid = source[:28 + aad_size] + sealed
            raw.append(valid)
            # Cover every tag bit, as well as independent key/nonce/AAD/ciphertext
            # modifications. Fixtures stay public and all rejection outputs must
            # be a zero acceptance byte plus a full zero plaintext buffer.
            positions = [0, 16 * 8, (len(valid) - 1) * 8]
            if aad_size:
                positions.append(28 * 8)
            if size:
                positions.append((28 + aad_size) * 8)
            if lane == 0:
                positions += list(range((len(valid) - 16) * 8, len(valid) * 8))
            for bit in positions:
                altered = bytearray(valid)
                altered[bit // 8] ^= 1 << (bit % 8)
                raw.append(bytes(altered))
        expected = []
        for x in raw:
            try:
                plaintext = AESGCM(x[:16]).decrypt(x[16:28], x[28 + aad_size:], x[28:28 + aad_size])
                expected.append(b'\xff' + plaintext)
            except InvalidTag:
                expected.append(bytes(1 + size))
        yield ('gcm-open', str(aad_size), str(size)), raw, expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-backend', action='store_true')
    args = parser.parse_args()
    subprocess.run(['lake', 'build', 'emit_mpc'], cwd=ROOT, check=True)
    records = []
    with tempfile.TemporaryDirectory(prefix='tls-mpc-lean-gcm-') as directory:
        for command, raw, expected in cases():
            path = Path(directory) / ('-'.join(command) + '.json')
            with path.open('w') as output:
                subprocess.run([str(ROOT / '.lake/build/bin/emit_mpc'), *command],
                               stdout=output, check=True, timeout=120)
            image = load(path)
            if evaluate_lanes(image, raw) != expected:
                raise AssertionError(f'GCM artifact differs from OpenSSL: {command}')
            record = {'arguments': command, 'input_bits': image['input_bits'],
                      'output_bits': len(image['outputs']), 'nodes': len(image['nodes']),
                      'adapter_operations': statistics(image), 'fixture_lanes': len(raw),
                      'all_outputs_match': True,
                      'artifact_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
            print(json.dumps(record), flush=True)
            if not args.skip_backend and command in (('gcm-seal', '5', '17'), ('gcm-open', '5', '17')):
                record['mpc_compilations'] = [compile_and_check(path, raw, expected, batch) for batch in (1, 16)]
                print(json.dumps({'arguments': command, 'mpc_compilations': record['mpc_compilations']}), flush=True)
            records.append(record)
    sources = [ROOT / name for name in ('TlsMpc/Aes.lean', 'TlsMpc/AesSbox.lean', 'TlsMpc/Ghash.lean',
               'TlsMpc/Gcm.lean', 'TlsMpc/ByteAuth.lean', 'TlsMpc/GcmOpen.lean',
               'TlsMpc/BvConstruct.lean', 'TlsMpc/ByteCircuit.lean', 'TlsMpc/AigExport.lean',
               'Main.lean', 'backend_adapter/aig.py', 'backend_adapter/boolean.py', 'programs/lean_artifact.mpc')]
    sources += [Path(__file__).resolve()]
    report = {'kind': 'lean_gcm_artifact_checks', 'cases': records,
              'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in sources},
              'oracle_cryptography_version': cryptography.__version__,
              'reference': 'https://doi.org/10.6028/NIST.SP.800-38D',
              'native_mpc_executed': False, 'throughput_measured': False,
              'limitations': ['Native export, JSON, adapter and MPC backend remain unverified.',
                              'Nonce uniqueness, durable state and authenticated TLS handshake are not established here.']}
    (ROOT / 'benchmarks/results/lean-gcm-checks.json').write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
