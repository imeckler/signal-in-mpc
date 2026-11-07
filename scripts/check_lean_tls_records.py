#!/usr/bin/env python3
"""Check Lean TLS record protection against RFC8448 and independent AESGCM."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

from cryptography.hazmat.primitives.ciphers.aead import AESGCM

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from backend_adapter.boolean import load
from backend_adapter.aig import statistics
from scripts.check_lean_crypto import compile_and_check, evaluate_lanes


def record(raw, kind, padding):
    key, iv, seq, content = raw[:16], raw[16:28], raw[28:36], raw[36:]
    nonce = bytes(a ^ b for a, b in zip(iv, bytes(4) + seq))
    inner = content + bytes([kind]) + bytes(padding)
    header = b'\x17\x03\x03' + (len(inner) + 16).to_bytes(2, 'big')
    return header + AESGCM(key).encrypt(nonce, inner, header)


def cases():
    key = bytes.fromhex('dbfaa693d1762c5b666af5d950258d01')
    iv = bytes.fromhex('5bd3c71b836e0b76bb73265f')
    message = bytes.fromhex('14000020a8ec436d677634ae525ac1fcebe11a039ec17694fac6e98527b642f2edd5ce61')
    finished = bytes.fromhex('170303003575ec4dc238cce60b298044a71e219c56cc77b0517fe9b93c7a4bfc44d87f38f80338ac98fc46deb384bd1caeacab6867d726c40546')
    raw = key + iv + bytes(8) + message
    assert record(raw, 22, 0) == finished
    yield ('tls-seal-record', '22', '36', '0'), [raw], [finished]
    application = bytes.fromhex('1703030043a23f7054b62c94d0affafe8228ba55cbefacea42f914aa66bcab3f2b9819a8a5b46b395bd54a9a20441e2b62974e1f5a6292a2977014bd1e3deae63aeebb21694915e4')
    raw = (bytes.fromhex('17422dda596ed5d9acd890e3c63f5051')
           + bytes.fromhex('5b78923dee08579033e523d9') + bytes(8) + bytes(range(50)))
    assert record(raw, 23, 0) == application
    yield ('tls-seal-record', '23', '50', '0'), [raw], [application]
    for size, padding in ((0, 0), (5, 3), (15, 0), (16, 0), (238, 0), (239, 0)):
        raw = [hashlib.shake_256(f'tls-record-{size}-{padding}-{i}'.encode()).digest(28)
               + seq.to_bytes(8, 'big')
               + hashlib.shake_256(f'tls-content-{size}-{i}'.encode()).digest(size)
               for i, seq in enumerate((0, 0x0102030405060708, 2**64 - 1))]
        expected = [record(x, 23, padding) for x in raw]
        yield ('tls-seal-record', '23', str(size), str(padding)), raw, expected
        if (size, padding) != (5, 3):
            continue
        opened_raw, opened_expected = [], []
        for source, wire in zip(raw, expected):
            valid = source[:36] + wire[5:]
            opened_raw.append(valid)
            opened_expected.append(b'\xff' + source[36:] + b'\x17' + bytes(padding))
            for position in (0, 16, 28, 36, len(valid) - 1):
                bad = bytearray(valid)
                bad[position] ^= 1
                opened_raw.append(bytes(bad))
                opened_expected.append(bytes(size + padding + 2))
        yield ('tls-open-inner', str(size + padding + 1)), opened_raw, opened_expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-backend', action='store_true')
    args = parser.parse_args()
    subprocess.run(['lake', 'build', 'emit_mpc'], cwd=ROOT, check=True)
    records = []
    with tempfile.TemporaryDirectory(prefix='tls-mpc-record-') as directory:
        for command, raw, expected in cases():
            path = Path(directory) / ('-'.join(command) + '.json')
            with path.open('w') as output:
                subprocess.run([str(ROOT / '.lake/build/bin/emit_mpc'), *command],
                               stdout=output, check=True, timeout=180)
            image = load(path)
            if evaluate_lanes(image, raw) != expected:
                raise AssertionError(f'TLS record mismatch: {command}')
            result = {'arguments': command, 'input_bits': image['input_bits'],
                      'output_bits': len(image['outputs']), 'nodes': len(image['nodes']),
                      'adapter_operations': statistics(image), 'fixture_lanes': len(raw),
                      'all_outputs_match': True,
                      'artifact_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
            print(json.dumps(result), flush=True)
            if not args.skip_backend and command in (('tls-seal-record', '23', '5', '3'), ('tls-open-inner', '9')):
                result['mpc_compilations'] = [compile_and_check(path, raw, expected, batch) for batch in (1, 16)]
                print(json.dumps({'arguments': command, 'mpc_compilations': result['mpc_compilations']}), flush=True)
            records.append(result)
    rejected = [('tls-seal-record', '20', '1', '0'), ('tls-seal-record', '21', '0', '0'),
                ('tls-seal-record', '22', '0', '0'), ('tls-seal-record', '23', '16385', '0'),
                ('tls-seal-record', '23', '0', '16385'), ('tls-open-inner', '0')]
    for command in rejected:
        bad = subprocess.run([str(ROOT / '.lake/build/bin/emit_mpc'), *command], capture_output=True, timeout=5)
        if not bad.returncode or bad.stdout:
            raise AssertionError(f'invalid public shape emitted an artifact: {command}')
    sources = [ROOT / name for name in ('TlsMpc/TlsRecord.lean', 'TlsMpc/Gcm.lean', 'TlsMpc/GcmOpen.lean',
               'TlsMpc/ByteAuth.lean', 'TlsMpc/Aes.lean', 'TlsMpc/AesSbox.lean', 'TlsMpc/Ghash.lean',
               'TlsMpc/BvConstruct.lean', 'TlsMpc/ByteCircuit.lean', 'TlsMpc/AigExport.lean', 'Main.lean',
               'backend_adapter/aig.py', 'backend_adapter/boolean.py', 'programs/lean_artifact.mpc')]
    sources.append(Path(__file__).resolve())
    report = {'kind': 'lean_tls_record_checks', 'cases': records, 'rejected_public_shapes': rejected,
              'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
              'reference_vectors': 'https://www.rfc-editor.org/rfc/rfc8448#section-3',
              'native_mpc_executed': False, 'throughput_measured': False,
              'limitations': ['Opening returns authenticated TLSInnerPlaintext; type/padding parsing remains pending.',
                             'Caller must validate the canonical public header before open-inner.',
                             'No handshake authentication, durable sequence reservation or key-usage policy is exercised.',
                             'Native export, JSON, adapter and MPC execution are unverified.']}
    (ROOT / 'benchmarks/results/lean-tls-record-checks.json').write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
