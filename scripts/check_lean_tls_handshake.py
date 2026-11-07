#!/usr/bin/env python3
"""Check Lean Finished verification and HRR transcript hashing with public fixtures."""

import argparse
from datetime import datetime, timezone
import hashlib
import hmac
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from backend_adapter.boolean import load
from backend_adapter.aig import statistics
from scripts.check_lean_crypto import compile_and_check, evaluate_lanes, label, sample


def finished(secret, transcript_hash):
    return b'\x14\x00\x00\x20' + hmac.digest(label(secret, 'finished', b'', 32), transcript_hash, 'sha256')


def cases():
    secret = bytes.fromhex('b3eddb126e067f35a780b3abf45e2d8f3b1a950738f52e9600746a0e27a55a21')
    transcript = bytes.fromhex('9608102a0f1ccc6db6250b7b7e417b1a000eaada3daae4777a7686c9ff83df13')
    message = bytes.fromhex('14000020a8ec436d677634ae525ac1fcebe11a039ec17694fac6e98527b642f2edd5ce61')
    assert finished(secret, transcript) == message
    valid = secret + transcript + message
    raw, expected = [valid], [b'\xff']
    for bit in range(36 * 8):
        bad = bytearray(valid)
        bad[64 + bit // 8] ^= 1 << (bit % 8)
        raw.append(bytes(bad))
        expected.append(b'\x00')
    for position in (0, 32):
        bad = bytearray(valid)
        bad[position] ^= 1
        raw.append(bytes(bad))
        expected.append(b'\x00')
    for i in range(4):
        prefix = sample(f'finished-{i}', 64)
        raw.append(prefix + finished(prefix[:32], prefix[32:]))
        expected.append(b'\xff')
    yield ('tls-verify-finished',), raw, expected

    for size in (0, 3, 55, 56, 64, 120):
        raw, expected = [], []
        for i in range(2):
            secret, transcript = sample(f'secret-{i}', 32), sample(f'transcript-{size}-{i}', size)
            valid = secret + transcript + finished(secret, hashlib.sha256(transcript).digest())
            raw.append(valid)
            expected.append(b'\xff')
            positions = [0, 32 + size, 35 + size, len(valid) - 1]
            if size:
                positions.append(32)
            for position in positions:
                bad = bytearray(valid)
                bad[position] ^= 1
                raw.append(bytes(bad))
                expected.append(b'\x00')
        yield ('tls-verify-finished-transcript', str(size)), raw, expected

    for hello_size, retry_size, following_size in ((4, 4, 0), (55, 56, 8), (64, 36, 64), (120, 89, 128)):
        raw, expected = [], []
        for i in range(3):
            def message(kind, size):
                return bytes([kind]) + (size - 4).to_bytes(3, 'big') + sample(f'body-{kind}-{size}-{i}', size - 4)
            hello, retry = message(1, hello_size), message(2, retry_size)
            following = message(1, following_size) if following_size else b''
            wire = hello + retry + following
            raw.append(wire)
            synthetic = b'\xfe\x00\x00\x20' + hashlib.sha256(hello).digest()
            digest = hashlib.sha256(synthetic + retry + following).digest()
            assert digest != hashlib.sha256(wire).digest()
            expected.append(digest)
        yield ('tls-retry-transcript-hash', str(hello_size), str(retry_size), str(following_size)), raw, expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-backend', action='store_true')
    args = parser.parse_args()
    subprocess.run(['lake', 'build', 'emit_mpc'], cwd=ROOT, check=True)
    records = []
    with tempfile.TemporaryDirectory(prefix='tls-mpc-handshake-') as directory:
        for command, raw, expected in cases():
            path = Path(directory) / ('-'.join(command) + '.json')
            with path.open('w') as output:
                subprocess.run([str(ROOT / '.lake/build/bin/emit_mpc'), *command], stdout=output,
                               cwd=ROOT, check=True, timeout=300)
            image = load(path)
            if evaluate_lanes(image, raw) != expected:
                raise AssertionError(f'TLS handshake circuit mismatch: {command}')
            result = {'arguments': command, 'input_bits': image['input_bits'],
                      'output_bits': len(image['outputs']), 'nodes': len(image['nodes']),
                      'adapter_operations': statistics(image), 'fixture_lanes': len(raw),
                      'all_outputs_match': True,
                      'artifact_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
            print(json.dumps(result), flush=True)
            if not args.skip_backend and command in (('tls-verify-finished',), ('tls-retry-transcript-hash', '4', '4', '0')):
                result['mpc_compilations'] = [compile_and_check(path, raw, expected, batch) for batch in (1, 16)]
                print(json.dumps({'arguments': command, 'mpc_compilations': result['mpc_compilations']}), flush=True)
            records.append(result)
    rejected = [('tls-verify-finished-transcript', '4097'),
                ('tls-retry-transcript-hash', '4097', '0', '0'),
                ('tls-retry-transcript-hash', '0', '4097', '0'),
                ('tls-retry-transcript-hash', '0', '0', '4097')]
    for command in rejected:
        bad = subprocess.run([str(ROOT / '.lake/build/bin/emit_mpc'), *command], capture_output=True, timeout=5)
        if not bad.returncode or bad.stdout:
            raise AssertionError(f'invalid public shape emitted an artifact: {command}')
    names = ('TlsMpc/TlsHandshake.lean', 'TlsMpc/TlsKdf.lean', 'TlsMpc/Sha256.lean',
             'TlsMpc/ByteAuth.lean', 'TlsMpc/BvConstruct.lean', 'TlsMpc/ByteCircuit.lean',
             'TlsMpc/AigExport.lean', 'Main.lean', 'backend_adapter/aig.py',
             'backend_adapter/boolean.py', 'programs/lean_artifact.mpc',
             'scripts/check_lean_crypto.py', 'scripts/clear_circuit.py')
    paths = [ROOT / name for name in names] + [Path(__file__).resolve()]
    report = {'kind': 'lean_tls_handshake_checks', 'checked_utc': datetime.now(timezone.utc).isoformat(),
              'cases': records, 'rejected_public_shapes': rejected,
              'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
              'references': ['https://www.rfc-editor.org/rfc/rfc9846#section-4.1',
                             'https://www.rfc-editor.org/rfc/rfc9846#section-4.5.3',
                             'https://www.rfc-editor.org/rfc/rfc8448#section-3'],
              'backend_compilation_tested': not args.skip_backend,
              'native_mpc_executed': False, 'throughput_measured': False,
              'limitations': ['Inputs must contain correctly assembled handshake transcript bytes.',
                             'No certificate, hostname, CertificateVerify, ECDHE or handshake-state validation.',
                             'Successful Finished verification alone does not authenticate the server.',
                             'Native export, JSON, adapter and MPC execution are unverified.']}
    (ROOT / 'benchmarks/results/lean-tls-handshake-checks.json').write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
