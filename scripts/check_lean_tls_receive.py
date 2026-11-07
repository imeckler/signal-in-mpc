#!/usr/bin/env python3
"""Differential checks for Lean TLS padding/type parsing and complete record opening.

Only public fixtures are used. The Python code is an independent test oracle,
not a protocol implementation or a circuit builder used by the application.
"""

import argparse
from collections import defaultdict
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

from cryptography.exceptions import InvalidTag
from cryptography.hazmat.primitives.ciphers.aead import AESGCM

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from backend_adapter.boolean import load
from backend_adapter.aig import statistics
from scripts.check_lean_crypto import compile_and_check, evaluate_lanes


def sample(label, size):
    return hashlib.shake_256(label.encode()).digest(size)


def parse_inner(inner):
    trimmed = inner.rstrip(b'\x00')
    if not trimmed:
        return bytes(len(inner) + 4)
    content, kind = trimmed[:-1], trimmed[-1]
    if kind not in (21, 22, 23) or (kind != 23 and not content):
        return bytes(len(inner) + 4)
    return (bytes([255, kind]) + len(content).to_bytes(2, 'big')
            + content + bytes(len(inner) - len(content)))


def nonce(prefix):
    return bytes(a ^ b for a, b in zip(prefix[16:28], bytes(4) + prefix[28:36]))


def protect(prefix, inner, header=None):
    if header is None:
        header = b'\x17\x03\x03' + (len(inner) + 16).to_bytes(2, 'big')
    return prefix + header + AESGCM(prefix[:16]).encrypt(nonce(prefix), inner, header)


def open_record(raw):
    prefix, wire = raw[:36], raw[36:]
    size = len(wire) - 21
    header = b'\x17\x03\x03' + (size + 16).to_bytes(2, 'big')
    if wire[:5] != header:
        return bytes(size + 4)
    try:
        return parse_inner(AESGCM(prefix[:16]).decrypt(nonce(prefix), wire[5:], header))
    except InvalidTag:
        return bytes(size + 4)


def parser_cases():
    for size in (1, 2, 17, 256, 257, 1024):
        raw = [bytes([127]) * (size - 1) + bytes([tag]) for tag in range(256)]
        raw.append(bytes(size))
        for kind in (21, 22, 23):
            for content_size in sorted({0, min(1, size - 1), size // 2, size - 1}):
                content = bytes(content_size) if content_size % 2 else sample(f'content-{content_size}', content_size)
                raw.append(content + bytes([kind]) + bytes(size - content_size - 1))
        yield ('tls-parse-inner', str(size)), raw, [parse_inner(x) for x in raw]


def record_cases():
    grouped = defaultdict(list)

    def add(raw):
        grouped[len(raw) - 36].append(raw)

    for size in (1, 17, 257):
        for i, sequence in enumerate((0, 0x0102030405060708, 2**64 - 1)):
            prefix = sample(f'key-iv-{size}-{i}', 28) + sequence.to_bytes(8, 'big')
            inner = sample(f'plaintext-{size}-{i}', size - 1) + b'\x17'
            valid = protect(prefix, inner)
            add(valid)
            for position in (0, 16, 28, 36, 37, 38, 39, 40, 41, len(valid) - 1):
                bad = bytearray(valid)
                bad[position] ^= 1
                add(bytes(bad))
            add(protect(prefix, bytes(size)))
            for kind in (21, 22, 23):
                add(protect(prefix, bytes([kind]) + bytes(size - 1)))
            # A valid GCM tag cannot authorize a malformed TLS header.
            for index in range(5):
                malformed = bytearray(valid[36:41])
                malformed[index] ^= 1
                add(protect(prefix, inner, bytes(malformed)))

    prefix = sample('exhaustive-record-key-iv', 28) + bytes(8)
    for tag in range(256):
        add(protect(prefix, b'\x7f' * 16 + bytes([tag])))
    valid = protect(prefix, b'hello\x00\x00\x17' + bytes(9))
    add(valid)
    for bit in range(128):
        bad = bytearray(valid)
        bad[len(bad) - 16 + bit // 8] ^= 1 << (bit % 8)
        add(bytes(bad))

    # RFC8448 section 3: complete client Finished and application records.
    for key, iv, wire, expected_content, kind in (
        ('dbfaa693d1762c5b666af5d950258d01', '5bd3c71b836e0b76bb73265f',
         '170303003575ec4dc238cce60b298044a71e219c56cc77b0517fe9b93c7a4bfc44d87f38f80338ac98fc46deb384bd1caeacab6867d726c40546',
         bytes.fromhex('14000020a8ec436d677634ae525ac1fcebe11a039ec17694fac6e98527b642f2edd5ce61'), 22),
        ('17422dda596ed5d9acd890e3c63f5051', '5b78923dee08579033e523d9',
         '1703030043a23f7054b62c94d0affafe8228ba55cbefacea42f914aa66bcab3f2b9819a8a5b46b395bd54a9a20441e2b62974e1f5a6292a2977014bd1e3deae63aeebb21694915e4',
         bytes(range(50)), 23),
    ):
        raw = bytes.fromhex(key + iv) + bytes(8) + bytes.fromhex(wire)
        assert open_record(raw) == parse_inner(expected_content + bytes([kind]))
        add(raw)
    for size, raw in sorted(grouped.items()):
        yield ('tls-open-record', str(size)), raw, [open_record(x) for x in raw]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-backend', action='store_true')
    args = parser.parse_args()
    subprocess.run(['lake', 'build', 'emit_mpc'], cwd=ROOT, check=True)
    records = []
    with tempfile.TemporaryDirectory(prefix='tls-mpc-receive-') as directory:
        for command, raw, expected in (*parser_cases(), *record_cases()):
            path = Path(directory) / ('-'.join(command) + '.json')
            with path.open('w') as output:
                subprocess.run([str(ROOT / '.lake/build/bin/emit_mpc'), *command],
                               stdout=output, check=True, timeout=300)
            image = load(path)
            actual = evaluate_lanes(image, raw)
            if actual != expected:
                lane = next(i for i, (x, y) in enumerate(zip(actual, expected)) if x != y)
                raise AssertionError(f'TLS receive mismatch: {command}, fixture {lane}')
            result = {'arguments': command, 'input_bits': image['input_bits'],
                      'output_bits': len(image['outputs']), 'nodes': len(image['nodes']),
                      'adapter_operations': statistics(image), 'fixture_lanes': len(raw),
                      'accepted_lanes': sum(bool(x[0]) for x in expected),
                      'all_outputs_match': True,
                      'artifact_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
            print(json.dumps(result), flush=True)
            if not args.skip_backend and command in (('tls-parse-inner', '17'), ('tls-open-record', '38')):
                # Include both valid and invalid lanes in the backend fixture.
                selected = [next(i for i, x in enumerate(expected) if x[0]),
                            next(i for i, x in enumerate(expected) if not x[0])]
                result['mpc_compilations'] = [compile_and_check(path, [raw[i] for i in selected],
                    [expected[i] for i in selected], batch) for batch in (1, 16)]
                print(json.dumps({'arguments': command, 'mpc_compilations': result['mpc_compilations']}), flush=True)
            records.append(result)
    rejected = [('tls-parse-inner', '0'), ('tls-parse-inner', '1025'),
                ('tls-open-record', '21'), ('tls-open-record', '1046')]
    for command in rejected:
        result = subprocess.run([str(ROOT / '.lake/build/bin/emit_mpc'), *command], capture_output=True, timeout=5)
        if not result.returncode or result.stdout:
            raise AssertionError(f'invalid public shape emitted an artifact: {command}')
    names = ('TlsMpc/TlsInner.lean', 'TlsMpc/TlsReceive.lean', 'TlsMpc/TlsRecord.lean',
             'TlsMpc/Gcm.lean', 'TlsMpc/GcmOpen.lean', 'TlsMpc/ByteAuth.lean', 'TlsMpc/Aes.lean',
             'TlsMpc/AesSbox.lean', 'TlsMpc/Ghash.lean', 'TlsMpc/BvConstruct.lean',
             'TlsMpc/ByteCircuit.lean', 'TlsMpc/AigExport.lean', 'Main.lean',
             'backend_adapter/aig.py', 'backend_adapter/boolean.py', 'programs/lean_artifact.mpc',
             'scripts/check_lean_crypto.py', 'scripts/clear_circuit.py')
    paths = [ROOT / name for name in names] + [Path(__file__).resolve()]
    report = {'kind': 'lean_tls_receive_checks', 'checked_utc': datetime.now(timezone.utc).isoformat(),
              'cases': records, 'rejected_public_shapes': rejected,
              'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
              'references': ['https://www.rfc-editor.org/rfc/rfc9846#section-5',
                             'https://www.rfc-editor.org/rfc/rfc8448#section-3'],
              'backend_compilation_tested': not args.skip_backend,
              'native_mpc_executed': False, 'throughput_measured': False,
              'limitations': ['No handshake authentication or connection-state content-type policy.',
                             'No durable sequence reservation, negotiated limits or key-usage policy.',
                             'Native export, JSON, adapter and MPC execution are unverified.',
                             'No native MPC or live TLS execution is exercised.']}
    (ROOT / 'benchmarks/results/lean-tls-receive-checks.json').write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
