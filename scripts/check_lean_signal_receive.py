#!/usr/bin/env python3
"""Public OpenSSL/HMAC fixtures for Lean Signal CBC and authenticated opening.

This harness never implements production crypto or executes networked MPC.
The serialized spans are fixture metadata; no protobuf parser is claimed.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import hmac
import json
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


def cbc(key, iv, data, decrypt=False):
    command = ['openssl', 'enc', '-aes-256-cbc', '-nopad', '-nosalt', '-K', key.hex(), '-iv', iv.hex()]
    if decrypt:
        command.append('-d')
    return subprocess.check_output(command, input=data)


def opened(key, iv, ciphertext, authenticated=True):
    padded = cbc(key, iv, ciphertext, True)
    count = padded[-1]
    if not authenticated or not 1 <= count <= 16 or padded[-count:] != bytes([count]) * count:
        return bytes(9 + len(ciphertext))
    plaintext = padded[:-count]
    return b'\xff' + len(plaintext).to_bytes(8, 'big') + plaintext + bytes(count)


def mac(key, sender, receiver, content):
    return hmac.digest(key, b'\x05' + sender + b'\x05' + receiver + content, 'sha256')[:8]


def varint(n):
    output = bytearray()
    while n >= 128:
        output.append((n & 127) | 128)
        n >>= 7
    output.append(n)
    return bytes(output)


def encode_content(ciphertext, ratchet, address, pq, version=0x44):
    # Actual locked proto/wire.proto field numbers. Values are synthetic public
    # fixtures; these offsets are not supplied by a production parser.
    leading = bytes([version, 0x0a, 33, 5]) + ratchet + b'\x10\x05\x18\x00\x22' + varint(len(ciphertext))
    offset = len(leading)
    content = leading + ciphertext
    if pq:
        content += b'\x2a' + varint(len(pq)) + pq
    address_offset = None
    if address is not None:
        content += b'\x32\x24'
        address_offset = len(content)
        content += address
    return content, offset, address_offset


def cbc_cases():
    for size in (16, 32, 64, 80, 272):
        key, iv = sample(f'cbc-key-{size}', 32), sample(f'cbc-iv-{size}', 16)
        base = sample(f'cbc-body-{size}', size)
        pads = [(f'padding-{count}', base[:-count] + bytes([count]) * count) for count in range(1, 17)]
        pads += [('padding-zero', base[:-1] + b'\x00'), ('padding-17', base[:-1] + b'\x11'),
                 ('padding-255', base[:-1] + b'\xff'), ('suffix-mismatch', base[:-3] + b'\x03\x02\x03')]
        raw, expected, labels = [], [], []
        for label, padded in pads:
            ciphertext = cbc(key, iv, padded)
            raw.append(key + iv + ciphertext)
            expected.append(opened(key, iv, ciphertext))
            labels.append(label)
        yield ['signal-cbc-open', str(size)], raw, expected, labels, size in (16, 64)


def mac_cases():
    for size in (0, 53, 54, 137):
        inputs, outputs = [], []
        for lane in range(4):
            fields = sample(f'mac-{size}-{lane}', 96 + size)
            inputs.append(fields)
            outputs.append(mac(fields[:32], fields[32:64], fields[64:96], fields[96:]))
        yield ['signal-message-mac', str(size)], inputs, outputs, ['public-hmac-domain'] * 4, False


def receive_cases():
    for size, has_address, pq_length in ((16, False, 0), (32, True, 0), (64, True, 7)):
        material = sample(f'receive-keys-{size}', 144)
        key, iv, mac_key, sender, receiver = material[:32], material[32:48], material[48:80], material[80:112], material[112:]
        ratchet, pq = sample(f'ratchet-{size}', 32), sample(f'pq-{size}', pq_length)
        address = (b'\x00' + sample('sender-service', 16) + b'\x01' +
                   b'\x01' + sample('receiver-service', 16) + b'\x7f') if has_address else None
        baseline = sample(f'plaintext-{size}', size)
        raw, expected, labels = [], [], []

        def append(label, padded=None, *, version=0x44, change=None, address_value=address, expected_address=address):
            padded = padded if padded is not None else baseline[:-5] + b'\x05' * 5
            ciphertext = cbc(key, iv, padded)
            content, ct_offset, address_offset = encode_content(ciphertext, ratchet, address_value, pq, version)
            wire = content + mac(mac_key, sender, receiver, content)
            fields = [key, iv, mac_key, sender, receiver, wire, expected_address or b'']
            if change:
                fields = change(fields, ct_offset, address_offset)
            actual_key, actual_iv, mk, si, ri, actual_wire, wanted = fields
            authentication = hmac.compare_digest(mac(mk, si, ri, actual_wire[:-8]), actual_wire[-8:])
            authentication &= actual_wire[0] >> 4 in (3, 4)
            if has_address:
                observed = actual_wire[address_offset:address_offset + 36]
                authentication &= (observed == wanted and wanted[0] in (0, 1) and wanted[18] in (0, 1)
                                   and 1 <= wanted[17] <= 127 and 1 <= wanted[35] <= 127)
            body = actual_wire[ct_offset:ct_offset + size]
            raw.append(b''.join(fields))
            expected.append(opened(actual_key, actual_iv, body, authentication))
            labels.append(label)
            return len(wire), ct_offset, address_offset

        shape = append('valid')

        def flip_field(field, offset):
            def change(fields, ct_offset, address_offset):
                index = ct_offset if offset == 'ciphertext' else offset
                item = bytearray(fields[field]); item[index] ^= 1; fields[field] = bytes(item)
                return fields
            return change

        # Put rejection cases early so backend batch16 checks both outcomes.
        append('bad-mac', change=flip_field(5, -1))
        append('invalid-padding-valid-mac', baseline[:-1] + b'\x00')
        append('ciphertext-tamper', change=flip_field(5, 'ciphertext'))
        append('sender-identity-tamper', change=flip_field(3, 0))
        append('receiver-identity-tamper', change=flip_field(4, 31))
        append('mac-key-tamper', change=flip_field(2, 0))
        append('bad-version-valid-mac', version=0x54)
        for count in range(1, 17):
            append(f'padding-{count}', baseline[:-count] + bytes([count]) * count)
        for version in (0x00, 0x24, 0xf4):
            append(f'bad-version-{version}', version=version)
        for version in (0x30, 0x3f, 0x40, 0x4f):
            append(f'accepted-version-{version}', version=version)
        for index in range(8):
            append(f'mac-byte-{index}-tamper', change=flip_field(5, index - 8))
        append('content-tamper', change=flip_field(5, 5))
        append('padding-17-valid-mac', baseline[:-1] + b'\x11')
        append('padding-suffix-mismatch-valid-mac', baseline[:-3] + b'\x03\x02\x03')
        if has_address:
            for index in (0, 1, 17, 18, 19, 35):
                wrong = bytearray(address); wrong[index] ^= 1
                append(f'expected-address-{index}-mismatch', expected_address=bytes(wrong))
            for index, value in ((0, 2), (18, 255), (17, 0), (35, 128)):
                bad = bytearray(address); bad[index] = value
                append(f'invalid-address-{index}-valid-mac', address_value=bytes(bad), expected_address=bytes(bad))
            wrong = bytearray(address); wrong[1] ^= 1
            append('address-payload-mismatch-valid-mac', address_value=bytes(wrong))
        wire_size, ct_offset, address_offset = shape
        args = ['signal-open-span', str(wire_size), str(ct_offset), str(size),
                str(address_offset) if has_address else 'none']
        yield args, raw, expected, labels, size in (16, 32)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-backend', action='store_true')
    options = parser.parse_args()
    exporter = ROOT / '.lake/build/bin/emit_mpc'
    sources = [exporter, ROOT / 'Main.lean', ROOT / 'TlsMpc/AesInverse.lean', ROOT / 'TlsMpc/Aes.lean',
               ROOT / 'TlsMpc/AesSbox.lean', ROOT / 'TlsMpc/ByteAuth.lean', ROOT / 'TlsMpc/Sha256.lean',
               ROOT / 'TlsMpc/HmacPrepared.lean', ROOT / 'TlsMpc/ByteCircuit.lean', ROOT / 'TlsMpc/AigExport.lean',
               ROOT / 'TlsMpc/BvConstruct.lean', ROOT / 'backend_adapter/aig.py', ROOT / 'backend_adapter/boolean.py',
               ROOT / 'programs/lean_artifact.mpc', ROOT / 'scripts/check_lean_crypto.py',
               ROOT / 'scripts/clear_circuit.py', ROOT / 'test_support/circuit.py', Path(__file__).resolve()]
    sources += [ROOT / ('TlsMpc/Signal/' + name + '.lean') for name in
                ('Unpad', 'OpenResult', 'CbcOpen', 'MessageMac', 'Receive')]
    if not options.skip_backend:
        backend = ROOT / '.deps/MP-SPDZ'
        sources += [backend / 'compile.py', *sorted((backend / 'Compiler').rglob('*.py'))]
    before = {str(path.relative_to(ROOT)): digest(path) for path in sources}
    destination = ROOT / '.deps/signal-receive-artifacts'
    destination.mkdir(exist_ok=True)
    records = []
    for args, inputs, outputs, labels, compile_backend in [*cbc_cases(), *mac_cases(), *receive_cases()]:
        path = destination / ('-'.join(args) + '.json')
        start = time.perf_counter()
        with path.open('w') as output:
            subprocess.run([str(exporter), *args], stdout=output, cwd=ROOT, check=True, timeout=300)
        elapsed = time.perf_counter() - start
        artifact = load(path)
        if evaluate_lanes(artifact, inputs) != outputs:
            observed = evaluate_lanes(artifact, inputs)
            failures = [label for label, actual, expected in zip(labels, observed, outputs) if actual != expected]
            raise AssertionError(f'Artifact mismatch {args}: {failures}')
        fixture_path = path.with_name(path.stem + '-fixtures.json')
        fixture_path.write_text(json.dumps([{'label': label, 'input': value.hex(), 'output': result.hex()}
                                           for label, value, result in zip(labels, inputs, outputs)], indent=2) + '\n')
        row = {'arguments': args, 'artifact_sha256': digest(path), 'fixture_sha256': digest(fixture_path),
               'fixture_lanes': len(inputs), 'input_bits': artifact['input_bits'], 'output_bits': len(artifact['outputs']),
               'native_export_seconds': elapsed, 'adapter_operations': statistics(artifact), 'all_outputs_match': True}
        records.append(row)
        print(json.dumps(row), flush=True)
        if compile_backend and not options.skip_backend:
            indices = ([0, 16, 17, 18, 19, *range(1, 12)] if args[0] == 'signal-cbc-open' else list(range(16)))
            selected_inputs = [inputs[i] for i in indices]
            selected_outputs = [outputs[i] for i in indices]
            row['mpc_compilations'] = [compile_and_check(path, selected_inputs, selected_outputs, batch) for batch in (1, 16)]
            for result in row['mpc_compilations']:
                if result['bit_triples'] != row['adapter_operations']['executed_and_gates'] * result['batch']:
                    raise AssertionError('Unexpected backend AND count')
            print(json.dumps({'arguments': args, 'mpc_compilations': row['mpc_compilations']}), flush=True)
    invalid_shapes = [
        ['signal-cbc-open', '0'], ['signal-cbc-open', '15'], ['signal-cbc-open', '1025'],
        ['signal-open-span', '24', '0', '16', 'none'], ['signal-open-span', '24', '1', '16', 'none'],
        ['signal-open-span', '80', '1', '0', 'none'], ['signal-open-span', '80', '1', '15', 'none'],
        ['signal-open-span', '80', '1', '16', '1'], ['signal-open-span', '80', '1', '16', '60'],
    ]
    for args in invalid_shapes:
        result = subprocess.run([str(exporter), *args], cwd=ROOT, capture_output=True, timeout=30)
        if result.returncode == 0:
            raise AssertionError(f'Invalid public shape accepted: {args}')
    if before != {str(path.relative_to(ROOT)): digest(path) for path in sources}:
        raise RuntimeError('Exporter or sources changed during checks; refusing mixed provenance')
    report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'kind': 'lean_signal_receive_checks',
              'cases': records, 'invalid_public_shapes_rejected': invalid_shapes, 'source_sha256': before,
              'native_mpc_executed': False, 'backend_bytecode_compiled': not options.skip_backend,
              'throughput_measured': False, 'upstream_commit': '904c8dc8216073b078a5f2f5090e3da8382e6a92',
              'reference_sources': ['rust/crypto/src/aes_cbc.rs', 'rust/protocol/src/protocol.rs', 'rust/protocol/src/proto/wire.proto'],
              'actual_rustcrypto_aes_cbc_hmac_wrapper_equivalence': False,
              'full_protobuf_parser_or_session_state_machine': False,
              'limitations': ['All fixture inputs are synthetic public values.',
                  'Serialized ciphertext/address offsets and address presence are public fixture metadata; an in-MPC parser must establish them for general wire input.',
                  'OpenSSL/HMAC fixture agreement supplements Lean lowering proofs and does not establish actual Rust wrapper equivalence.',
                  'JSON/native export, generic adapter and MPC execution backend remain unverified.']}
    output = ROOT / 'benchmarks/results/lean-signal-receive-checks.json'
    output.write_text(json.dumps(report, indent=2) + '\n')
    print(f'Wrote {output.relative_to(ROOT)}: {len(records)} artifacts, {sum(x["fixture_lanes"] for x in records)} fixture lanes.', flush=True)


if __name__ == '__main__':
    main()
