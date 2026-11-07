#!/usr/bin/env python3
"""Independent public fixtures for compiled Lean Signal serialization/send.

Python is a differential harness only. Production encryption, serialization
and MAC computation are all in the exported Lean circuit.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import hmac
import json
import re
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from backend_adapter.boolean import load
from backend_adapter.aig import statistics
from scripts.check_lean_crypto import compile_and_check, evaluate_lanes


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sample(label, length):
    return hashlib.shake_256(label.encode()).digest(length)


def varint(value):
    output = bytearray()
    while value >= 128:
        output.append((value & 127) | 128)
        value >>= 7
    output.append(value)
    return bytes(output)


def bytes_field(tag, value):
    return varint(tag * 8 + 2) + varint(len(value)) + value


def content(version, counter, previous, ratchet, ciphertext, pq, addresses):
    return (bytes([((version & 15) << 4) | 4]) + bytes_field(1, b'\x05' + ratchet) +
            b'\x10' + varint(counter) + b'\x18' + varint(previous) + bytes_field(4, ciphertext) +
            (bytes_field(5, pq) if pq else b'') +
            (bytes_field(6, addresses) if addresses is not None else b''))


def content_size(ciphertext_size, pq_size, cw, pw, address):
    return (1 + 35 + (1 + cw) + (1 + pw) + 1 + len(varint(ciphertext_size)) + ciphertext_size +
            (1 + len(varint(pq_size)) + pq_size if pq_size else 0) + (38 if address else 0))


def valid_addresses(addresses):
    return addresses is None or (addresses[0] in (0, 1) and addresses[18] in (0, 1) and
                                 1 <= addresses[17] <= 127 and 1 <= addresses[35] <= 127)


def valid(cw, pw, counter, previous, addresses):
    return len(varint(counter)) == cw and len(varint(previous)) == pw and valid_addresses(addresses)


def address(label):
    return b'\x00' + sample(label + '-sender', 16) + b'\x01\x01' + sample(label + '-receiver', 16) + b'\x7f'


BOUNDARIES = [0, 127, 128, 16383, 16384, (1 << 21) - 1, 1 << 21,
              (1 << 28) - 1, 1 << 28, (1 << 32) - 1]


def smallest(width):
    return 0 if width == 1 else 1 << (7 * (width - 1))


def serialization_cases():
    shapes = [(0, 0, cw, pw, False) for cw in range(1, 6) for pw in range(1, 6)]
    shapes += [(127, 0, 1, 5, True), (128, 1, 5, 1, True), (0, 127, 3, 2, True),
               (1024, 128, 4, 4, True)]
    for ct_size, pq_size, cw, pw, has_address in shapes:
        label = f'serialize-{ct_size}-{pq_size}-{cw}-{pw}-{has_address}'
        ratchet, ciphertext, pq = sample(label + '-ratchet', 32), sample(label + '-ct', ct_size), sample(label + '-pq', pq_size)
        addresses = address(label) if has_address else None
        raw, expected, labels = [], [], []

        def append(name, counter=smallest(cw), previous=smallest(pw), version=4, addr=addresses,
                   rk=ratchet, ct=ciphertext, pq_value=pq):
            raw.append(bytes([version]) + counter.to_bytes(4, 'big') + previous.to_bytes(4, 'big') +
                       rk + ct + pq_value + (addr or b''))
            result = (b'\xff' + content(version, counter, previous, rk, ct, pq_value, addr)
                      if valid(cw, pw, counter, previous, addr)
                      else bytes(1 + content_size(ct_size, pq_size, cw, pw, has_address)))
            expected.append(result)
            labels.append(name)

        append('valid-profile')
        for value in BOUNDARIES:
            append(f'counter-boundary-{value}', counter=value)
            append(f'previous-boundary-{value}', previous=value)
        if (ct_size, pq_size, cw, pw) == (0, 0, 1, 1):
            for version in range(256):
                append(f'constructor-version-{version}', version=version)
        if has_address:
            for offset, value in ((0, 2), (18, 255), (17, 0), (17, 128), (35, 0), (35, 255)):
                changed = bytearray(addresses)
                changed[offset] = value
                append(f'bad-address-{offset}-{value}', addr=bytes(changed))
            append('shared-ratchet-payload', rk=sample(label + '-changed-ratchet', 32))
            append('shared-ciphertext-payload', ct=sample(label + '-changed-ct', ct_size))
            append('shared-pq-payload', pq_value=sample(label + '-changed-pq', pq_size))
        args = ['signal-serialize', str(ct_size), str(pq_size), str(cw), str(pw), 'present' if has_address else 'none']
        compile_backend = (ct_size, pq_size, cw, pw, has_address) == (128, 1, 5, 1, True)
        yield args, raw, expected, labels, compile_backend


def send_cases():
    for pt_size, pq_size, cw, pw, has_address in ((0, 0, 1, 1, False), (15, 0, 2, 5, True),
                                                 (16, 7, 5, 3, True), (127, 128, 4, 4, False)):
        label = f'send-{pt_size}-{pq_size}-{cw}-{pw}-{has_address}'
        version = 4
        fields = [smallest(cw).to_bytes(4, 'big'), smallest(pw).to_bytes(4, 'big'),
                  sample(label + '-ratchet', 32), sample(label + '-cipher-key', 32), sample(label + '-iv', 16),
                  sample(label + '-mac-key', 32), sample(label + '-sender', 32), sample(label + '-receiver', 32),
                  sample(label + '-plaintext', pt_size), sample(label + '-pq', pq_size),
                  address(label) if has_address else b'']
        raw, expected, labels = [], [], []

        def append(name, values=fields, ver=version):
            co, pr, ratchet, key, iv, mk, sender, receiver, plaintext, pq, addr = values
            counter, previous = int.from_bytes(co, 'big'), int.from_bytes(pr, 'big')
            ciphertext = subprocess.check_output(['openssl', 'enc', '-aes-256-cbc', '-nosalt',
                                                 '-K', key.hex(), '-iv', iv.hex()], input=plaintext)
            body = content(ver, counter, previous, ratchet, ciphertext, pq, addr if has_address else None)
            tag = hmac.digest(mk, b'\x05' + sender + b'\x05' + receiver + body, 'sha256')[:8]
            raw.append(bytes([ver]) + b''.join(values))
            expected.append(b'\xff' + body + tag if valid(cw, pw, counter, previous, addr if has_address else None)
                            else bytes(9 + content_size(len(ciphertext), pq_size, cw, pw, has_address)))
            labels.append(name)

        append('valid-profile')
        for field_index, name in enumerate(('counter', 'previous', 'ratchet', 'cipher-key', 'iv', 'mac-key',
                                           'sender-identity', 'receiver-identity', 'plaintext', 'pq', 'addresses')):
            if not fields[field_index]:
                continue
            changed = list(fields)
            modified = bytearray(changed[field_index])
            modified[-2 if field_index == 10 else -1] ^= 1
            changed[field_index] = bytes(modified)
            append('bind-' + name, changed)
        for ver in (0, 3, 15, 255):
            append(f'constructor-version-{ver}', ver=ver)
        for index in (0, 1):
            for value in (0, (1 << 32) - 1):
                changed = list(fields)
                changed[index] = value.to_bytes(4, 'big')
                append(f'counter-profile-{index}-{value}', changed)
        if has_address:
            for offset, value in ((0, 2), (17, 0), (18, 2), (35, 128)):
                changed = list(fields)
                addr = bytearray(changed[-1]); addr[offset] = value; changed[-1] = bytes(addr)
                append(f'bad-address-{offset}', changed)
        args = ['signal-send', str(pt_size), str(pq_size), str(cw), str(pw), 'present' if has_address else 'none']
        yield args, raw, expected, labels, pt_size in (0, 16)


def lean_sources():
    found = set()
    def visit(module):
        if not module.startswith('TlsMpc'):
            return
        path = ROOT / (module.replace('.', '/') + '.lean')
        if path in found:
            return
        found.add(path)
        for name in re.findall(r'^import ([A-Za-z0-9_.]+)', path.read_text(), re.M):
            visit(name)
    visit('TlsMpc.Signal.Send')
    return sorted(found)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-backend', action='store_true')
    parser.add_argument('--isolated-exporter', action='store_true', help='Run SignalReference/SendExport.lean until root Main integration')
    options = parser.parse_args()
    exporter = ROOT / '.lake/build/bin/emit_mpc'
    command = (['lake', 'env', 'lean', '--run', 'SignalReference/SendExport.lean']
               if options.isolated_exporter else [str(exporter)])
    exporter_sources = ([ROOT / 'SignalReference/SendExport.lean', ROOT / 'lean-toolchain']
                        if options.isolated_exporter else [exporter, ROOT / 'Main.lean'])
    sources = [*exporter_sources, *lean_sources(),
               ROOT / 'backend_adapter/aig.py', ROOT / 'backend_adapter/boolean.py', ROOT / 'programs/lean_artifact.mpc',
               ROOT / 'scripts/check_lean_crypto.py', ROOT / 'scripts/clear_circuit.py',
               ROOT / 'test_support/circuit.py', Path(__file__).resolve(),
               ROOT / '.deps/libsignal-v0.106.1/rust/protocol/src/protocol.rs',
               ROOT / '.deps/libsignal-v0.106.1/rust/protocol/src/proto/wire.proto',
               ROOT / '.deps/libsignal-vendor/prost-0.14.4/src/encoding.rs',
               ROOT / '.deps/libsignal-vendor/prost-0.14.4/src/encoding/varint.rs',
               ROOT / '.deps/libsignal-vendor/prost-derive-0.14.4/src/lib.rs']
    if not options.skip_backend:
        backend = ROOT / '.deps/MP-SPDZ'
        sources += [backend / 'compile.py', *sorted((backend / 'Compiler').rglob('*.py'))]
    before = {str(path.relative_to(ROOT)): digest(path) for path in sources}
    destination = ROOT / '.deps/signal-send-artifacts'
    destination.mkdir(exist_ok=True)
    records = []
    for args, inputs, outputs, labels, compile_backend in [*serialization_cases(), *send_cases()]:
        path = destination / ('-'.join(args) + '.json')
        started = time.perf_counter()
        with path.open('w') as output:
            subprocess.run([*command, *args], stdout=output, cwd=ROOT, check=True, timeout=300)
        elapsed = time.perf_counter() - started
        artifact = load(path)
        observed = evaluate_lanes(artifact, inputs)
        if observed != outputs:
            failed = [label for label, actual, expected in zip(labels, observed, outputs) if actual != expected]
            raise AssertionError(f'Artifact mismatch {args}: {failed}')
        fixture_path = path.with_name(path.stem + '-fixtures.json')
        fixture_path.write_text(json.dumps([{'label': label, 'input': x.hex(), 'output': y.hex()}
                                           for label, x, y in zip(labels, inputs, outputs)], indent=2) + '\n')
        row = {'arguments': args, 'artifact_sha256': digest(path), 'fixture_sha256': digest(fixture_path),
               'fixture_lanes': len(inputs), 'input_bits': artifact['input_bits'], 'output_bits': len(artifact['outputs']),
               'export_seconds': elapsed, 'adapter_operations': statistics(artifact), 'all_outputs_match': True}
        records.append(row)
        print(json.dumps(row), flush=True)
        if compile_backend and not options.skip_backend:
            row['mpc_compilations'] = [compile_and_check(path, inputs, outputs, batch) for batch in (1, 16)]
            for result in row['mpc_compilations']:
                assert result['bit_triples'] == row['adapter_operations']['executed_and_gates'] * result['batch']
            print(json.dumps({'arguments': args, 'mpc_compilations': row['mpc_compilations']}), flush=True)
    invalid = [['signal-send', '0', '0', '0', '1', 'none'], ['signal-send', '0', '0', '1', '6', 'none'],
               ['signal-send', '1025', '0', '1', '1', 'none'], ['signal-serialize', '0', '1025', '1', '1', 'none'],
               ['signal-serialize', '0', '0', '1', '1', 'unknown']]
    for args in invalid:
        result = subprocess.run([*command, *args], cwd=ROOT, capture_output=True, timeout=30)
        assert result.returncode, args
    if before != {str(path.relative_to(ROOT)): digest(path) for path in sources}:
        raise RuntimeError('Exporter or sources changed during checks; refusing mixed provenance')
    report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'kind': 'lean_signal_send_checks',
              'cases': records, 'invalid_public_shapes_rejected': invalid, 'source_sha256': before,
              'exporter_command': command,
              'native_mpc_executed': False, 'backend_bytecode_compiled': not options.skip_backend,
              'throughput_measured': False, 'upstream_commit': '904c8dc8216073b078a5f2f5090e3da8382e6a92',
              'actual_signalmessage_constructor_equivalence': False,
              'actual_rustcrypto_aes_cbc_hmac_wrapper_equivalence': False,
              'session_state_transition_or_persistence': False,
              'limitations': ['All fixture inputs are synthetic public values.',
                  'Plaintext/PQ lengths, address presence and canonical counter widths are public profiles.',
                  'Inputs are derived message keys and typed raw identity/ratchet/address encodings.',
                  'Invalid profiles or typed address encodings zero the secret status and full output.',
                  'Prost leaf refinements are tracked separately; these fixtures are not an end-to-end actual Rust proof.',
                  'JSON/native export, generic adapter and MPC execution backend remain unverified.']}
    target = ROOT / 'benchmarks/results/lean-signal-send-checks.json'
    target.write_text(json.dumps(report, indent=2) + '\n')
    print(f'Wrote {target.relative_to(ROOT)}: {len(records)} artifacts, {sum(r["fixture_lanes"] for r in records)} lanes.', flush=True)


if __name__ == '__main__':
    main()
