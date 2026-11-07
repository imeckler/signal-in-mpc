#!/usr/bin/env python3
"""Public independent fixtures for the coupled SPQR and Signal send circuit."""
from datetime import datetime, timezone
import argparse
import hashlib
import hmac
import json
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from backend_adapter.boolean import load
from backend_adapter.aig import statistics
from scripts.check_lean_crypto import evaluate_lanes, compile_and_check
from scripts.check_lean_signal_chain_send import derive
from scripts.check_lean_signal_send import content, content_size, valid, sample, address, smallest


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def varint(value):
    result = bytearray()
    while value > 127:
        result.append((value & 127) | 128)
        value >>= 7
    result.append(value)
    return bytes(result)


def spqr_derive(chain, counter):
    prk = hmac.digest(bytes(32), chain, 'sha256')
    info = (counter + 1).to_bytes(4, 'big') + b'Signal PQ Ratchet V1 Chain Next'
    block1 = hmac.digest(prk, info + b'\x01', 'sha256')
    block2 = hmac.digest(prk, block1 + info + b'\x02', 'sha256')
    return block1, block2


def cases():
    profiles = ((0, 1, 1, 1, 1, 0, False, False),
                (17, 5, 2, 10, 5, 3, True, True))
    for size, cw, pw, ew, iw, kw, chunk, addresses_present in profiles:
        label = f'spqr-send-{size}-{cw}-{pw}-{ew}-{iw}-{kw}-{chunk}-{addresses_present}'
        base = [b'\x04', smallest(cw).to_bytes(4, 'big'), smallest(pw).to_bytes(4, 'big'),
                sample(label + '-ratchet', 32), sample(label + '-chain', 32), sample(label + '-pq-chain', 32),
                max(0, smallest(iw) - 1).to_bytes(4, 'big'), max(1, smallest(ew)).to_bytes(8, 'big'),
                b'\x01' if chunk else b'\x00', smallest(kw).to_bytes(2, 'big') if chunk else b'',
                sample(label + '-chunk', 32) if chunk else b'', sample(label + '-sender', 32),
                sample(label + '-receiver', 32), sample(label + '-plaintext', size),
                address(label) if addresses_present else b'']
        raw, outputs, labels = [], [], []
        pq_size = 2 + ew + iw + (kw + 32 if chunk else 0)
        ct_size = (size // 16 + 1) * 16

        def append(name, fields=base):
            version, co, pr, ratchet, chain, pq_chain, pc, ep, kind, ci, data, sender, receiver, plaintext, addresses = fields
            counter, previous, pq_counter, epoch = [int.from_bytes(x, 'big') for x in (co, pr, pc, ep)]
            accepted = (counter != 0xffffffff and pq_counter != 0xffffffff and epoch != 0 and
                        valid(cw, pw, counter, previous, addresses if addresses_present else None) and
                        len(varint(epoch)) == ew and len(varint((pq_counter + 1) & 0xffffffff)) == iw and
                        kind[0] in ((1, 2, 3, 5, 6) if chunk else (0, 4)) and
                        (not chunk or len(varint(int.from_bytes(ci, 'big'))) == kw))
            if accepted:
                next_pq, pq_key = spqr_derive(pq_chain, pq_counter)
                pq = b'\x01' + varint(epoch) + varint(pq_counter + 1) + kind
                if chunk:
                    pq += varint(int.from_bytes(ci, 'big')) + data
                next_chain, cipher_key, mac_key, iv = derive(chain, pq_key)
                ciphertext = subprocess.check_output(['openssl', 'enc', '-aes-256-cbc', '-nosalt',
                                                     '-K', cipher_key.hex(), '-iv', iv.hex()], input=plaintext)
                body = content(version[0], counter, previous, ratchet, ciphertext, pq,
                               addresses if addresses_present else None)
                tag = hmac.digest(mac_key, b'\x05' + sender + b'\x05' + receiver + body, 'sha256')[:8]
                result = (b'\xff' + next_chain + (counter + 1).to_bytes(4, 'big') +
                          next_pq + (pq_counter + 1).to_bytes(4, 'big') + body + tag)
            else:
                result = (b'\x00' + chain + co + pq_chain + pc +
                          bytes(8 + content_size(ct_size, pq_size, cw, pw, addresses_present)))
            raw.append(b''.join(fields)); outputs.append(result); labels.append(name)
            return result

        append('valid-bound-pq-key-and-index')
        for kind in (*range(7), 255):
            fields = list(base); fields[8] = bytes([kind]); append(f'payload-kind-{kind}', fields)
        for field, name in ((0, 'version'), (3, 'ratchet'), (4, 'signal-chain'), (5, 'pq-chain'),
                            (10, 'chunk-data'), (11, 'sender'), (12, 'receiver'), (13, 'plaintext')):
            if base[field]:
                fields = list(base); fields[field] = sample(label + '-changed-' + name, len(base[field]))
                append('bind-' + name, fields)
        for field, name in ((1, 'signal-counter'), (6, 'pq-counter')):
            for value in (0, 126, 127, 128, 0x0ffffffe, 0x0fffffff, 0x10000000, 0xfffffffe, 0xffffffff):
                fields = list(base); fields[field] = value.to_bytes(4, 'big'); append(f'{name}-{value}', fields)
        for value in (0, 1, 127, 128, 2**63 - 1, 2**63, 2**64 - 1):
            fields = list(base); fields[7] = value.to_bytes(8, 'big'); append(f'epoch-{value}', fields)
        for previous in (0, 127, 128, 0xffffffff):
            fields = list(base); fields[2] = previous.to_bytes(4, 'big'); append(f'previous-{previous}', fields)
        if chunk:
            for index in (0, 127, 128, 16383, 16384, 65535):
                fields = list(base); fields[9] = index.to_bytes(2, 'big'); append(f'chunk-index-{index}', fields)
        if addresses_present:
            for offset, value in ((0, 2), (17, 0), (18, 255), (35, 128)):
                fields = list(base); addr = bytearray(fields[-1]); addr[offset] = value
                fields[-1] = bytes(addr); append(f'invalid-address-{offset}-{value}', fields)
        else:
            fields = list(base)
            for index in range(8):
                result = append(f'consecutive-coupled-state-{index}', fields)
                assert result[0] == 255
                fields = list(fields)
                fields[4], fields[1], fields[5], fields[6] = result[1:33], result[33:37], result[37:69], result[69:73]
        args = ['signal-spqr-send', str(size), str(cw), str(pw), str(ew), str(iw), str(kw),
                'present' if chunk else 'none', 'present' if addresses_present else 'none']
        yield args, raw, outputs, labels, size == 17


def lean_sources():
    found = set()
    def visit(module):
        if not module.startswith('TlsMpc'):
            return
        path = ROOT / (module.replace('.', '/') + '.lean')
        if path in found:
            return
        found.add(path)
        for imported in re.findall(r'^import ([A-Za-z0-9_.]+)', path.read_text(), re.M):
            visit(imported)
    visit('TlsMpc.Signal.SpqrSend')
    return sorted(found)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compile-backend', action='store_true')
    options = parser.parse_args()
    command = ['lake', 'env', 'lean', '--run', 'SignalReference/SpqrSendExport.lean']
    sources = [ROOT / 'SignalReference/SpqrSendExport.lean', ROOT / 'lean-toolchain', *lean_sources(),
               Path(__file__), ROOT / 'scripts/check_lean_signal_send.py', ROOT / 'scripts/check_lean_signal_chain_send.py',
               ROOT / 'scripts/check_lean_crypto.py', ROOT / 'scripts/clear_circuit.py', ROOT / 'test_support/circuit.py',
               ROOT / 'backend_adapter/aig.py', ROOT / 'backend_adapter/boolean.py', ROOT / 'programs/lean_artifact.mpc']
    if options.compile_backend:
        backend = ROOT / '.deps/MP-SPDZ'
        sources += [backend / 'compile.py', *sorted((backend / 'Compiler').rglob('*.py'))]
    before = {str(p.relative_to(ROOT)): digest(p) for p in sources}
    directory = ROOT / '.deps/signal-spqr-send-artifacts'; directory.mkdir(exist_ok=True)
    results = []
    for args, raw, expected, labels, compile_backend in cases():
        path = directory / ('-'.join(args) + '.json')
        started = time.perf_counter()
        with path.open('w') as output:
            subprocess.run([*command, *args], cwd=ROOT, stdout=output, check=True, timeout=300)
        elapsed = time.perf_counter() - started
        artifact = load(path)
        observed = evaluate_lanes(artifact, raw)
        if observed != expected:
            failures = [label for label, got, want in zip(labels, observed, expected) if got != want]
            raise AssertionError(f'SPQR send mismatch {args}: {failures}')
        fixtures = path.with_name(path.stem + '-fixtures.json')
        fixtures.write_text(json.dumps([{'label': l, 'input': x.hex(), 'output': y.hex()}
                                       for l, x, y in zip(labels, raw, expected)], indent=2) + '\n')
        row = {'arguments': args, 'artifact_sha256': digest(path), 'fixture_sha256': digest(fixtures),
               'fixture_lanes': len(raw), 'input_bits': artifact['input_bits'], 'output_bits': len(artifact['outputs']),
               'export_seconds': elapsed, 'adapter_operations': statistics(artifact), 'all_outputs_match': True}
        results.append(row); print(json.dumps(row), flush=True)
        if compile_backend and options.compile_backend:
            row['mpc_compilations'] = [compile_and_check(path, raw, expected, batch) for batch in (1, 16)]
            for result in row['mpc_compilations']:
                assert result['bit_triples'] == row['adapter_operations']['executed_and_gates'] * result['batch']
            print(json.dumps({'arguments': args, 'mpc_compilations': row['mpc_compilations']}), flush=True)
    assert before == {str(p.relative_to(ROOT)): digest(p) for p in sources}, 'Sources changed during checks'
    report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'cases': results, 'source_sha256': before,
              'exporter_command': command, 'native_mpc_executed': False, 'throughput_measured': False,
              'backend_bytecode_compiled': options.compile_backend,
              'actual_full_spqr_signal_send_refinement': False,
              'limitations': ['Synthetic public fixtures only; no native MPC execution.',
                  'Requires already selected active SPQR chain for epoch minus one and outgoing SPQR state-machine payload.',
                  'Epoch selection, KEM/chunk state transitions and inactive/no-chain branch are outside this profile.',
                  'Either exhausted counter, zero epoch, invalid kind/width/address rejects and preserves BOTH old chain states.',
                  'Atomic storage, rollback protection and proactive refresh are not implemented by this pure circuit.',
                  'Full actual RustCrypto/prost/Signal/SPQR equivalence remains separate.']}
    target = ROOT / 'benchmarks/results/lean-signal-spqr-send-checks.json'
    target.write_text(json.dumps(report, indent=2) + '\n')
    print(f'Passed {sum(r["fixture_lanes"] for r in results)} coupled SPQR send fixture lanes.', flush=True)


if __name__ == '__main__':
    main()
