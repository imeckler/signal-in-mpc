#!/usr/bin/env python3
"""Public independent fixtures for the bounded shared chain send step."""
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
from scripts.check_lean_signal_send import content, content_size, valid, sample, address, smallest


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def derive(chain, salt):
    seed = hmac.digest(chain, b'\x01', 'sha256')
    next_chain = hmac.digest(chain, b'\x02', 'sha256')
    prk = hmac.digest(salt, seed, 'sha256')
    block, material = b'', b''
    for index in range(1, 4):
        block = hmac.digest(prk, block + b'WhisperMessageKeys' + bytes([index]), 'sha256')
        material += block
    return next_chain, material[:32], material[32:64], material[64:80]


def cases():
    for size, pq_size, cw, pw, has_address in ((0, 0, 1, 1, False), (17, 5, 5, 2, True)):
        label = f'chain-{size}-{pq_size}-{cw}-{pw}-{has_address}'
        base = [bytes([4]), smallest(cw).to_bytes(4, 'big'), smallest(pw).to_bytes(4, 'big'),
                sample(label + '-ratchet', 32), sample(label + '-chain', 32), b'\x00',
                sample(label + '-pq-key', 32), sample(label + '-sender', 32), sample(label + '-receiver', 32),
                sample(label + '-plaintext', size), sample(label + '-pq', pq_size),
                address(label) if has_address else b'']
        raw, outputs, labels = [], [], []

        def append(name, fields=base):
            version, co, pr, ratchet, chain, present, pq_key, sender, receiver, plaintext, pq, addresses = fields
            counter, previous = int.from_bytes(co, 'big'), int.from_bytes(pr, 'big')
            accepted = (present[0] in (0, 1) and counter != 0xffffffff and
                        valid(cw, pw, counter, previous, addresses if has_address else None))
            ct_size = (size // 16 + 1) * 16
            if accepted:
                next_chain, cipher_key, mac_key, iv = derive(chain, pq_key if present == b'\x01' else bytes(32))
                ciphertext = subprocess.check_output(['openssl', 'enc', '-aes-256-cbc', '-nosalt',
                                                     '-K', cipher_key.hex(), '-iv', iv.hex()], input=plaintext)
                body = content(version[0], counter, previous, ratchet, ciphertext, pq, addresses if has_address else None)
                tag = hmac.digest(mac_key, b'\x05' + sender + b'\x05' + receiver + body, 'sha256')[:8]
                result = b'\xff' + next_chain + (counter + 1).to_bytes(4, 'big') + body + tag
            else:
                result = b'\x00' + chain + co + bytes(8 + content_size(ct_size, pq_size, cw, pw, has_address))
            raw.append(b''.join(fields)); outputs.append(result); labels.append(name)

        append('valid-no-pq-key')
        for present in (0, 1, 2, 255):
            fields = list(base); fields[5] = bytes([present]); append(f'pq-key-flag-{present}', fields)
        for field, name in ((4, 'chain'), (6, 'pq-key'), (7, 'sender'), (8, 'receiver'), (9, 'plaintext'), (10, 'pq')):
            if not base[field]:
                continue
            fields = list(base); fields[field] = sample(label + '-changed-' + name, len(base[field])); append('bind-' + name, fields)
            if field == 6:
                fields[5] = b'\x01'; append('bind-present-pq-key', fields)
        for counter in (0, 127, 128, 0x0fffffff, 0x10000000, 0xfffffffe, 0xffffffff):
            fields = list(base); fields[1] = counter.to_bytes(4, 'big'); append(f'counter-{counter}', fields)
        for previous in (0, 127, 128, 0xffffffff):
            fields = list(base); fields[2] = previous.to_bytes(4, 'big'); append(f'previous-{previous}', fields)
        for version in (0, 3, 15, 255):
            fields = list(base); fields[0] = bytes([version]); append(f'constructor-version-{version}', fields)
        if has_address:
            for offset, value in ((0, 2), (17, 0), (18, 255), (35, 128)):
                fields = list(base); addr = bytearray(fields[-1]); addr[offset] = value
                fields[-1] = bytes(addr); append(f'bad-address-{offset}-{value}', fields)
        args = ['signal-chain-send', str(size), str(pq_size), str(cw), str(pw), 'present' if has_address else 'none']
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
    visit('TlsMpc.Signal.ChainSend')
    return sorted(found)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-backend', action='store_true')
    options = parser.parse_args()
    command = ['lake', 'env', 'lean', '--run', 'SignalReference/ChainSendExport.lean']
    sources = [ROOT / 'SignalReference/ChainSendExport.lean', ROOT / 'lean-toolchain', *lean_sources(),
               Path(__file__), ROOT / 'scripts/check_lean_signal_send.py', ROOT / 'scripts/check_lean_crypto.py',
               ROOT / 'scripts/clear_circuit.py', ROOT / 'test_support/circuit.py',
               ROOT / 'backend_adapter/aig.py', ROOT / 'backend_adapter/boolean.py', ROOT / 'programs/lean_artifact.mpc']
    if not options.skip_backend:
        backend = ROOT / '.deps/MP-SPDZ'
        sources += [backend / 'compile.py', *sorted((backend / 'Compiler').rglob('*.py'))]
    before = {str(p.relative_to(ROOT)): digest(p) for p in sources}
    directory = ROOT / '.deps/signal-chain-send-artifacts'; directory.mkdir(exist_ok=True)
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
            raise AssertionError(f'Chain send mismatch {args}: {failures}')
        fixtures = path.with_name(path.stem + '-fixtures.json')
        fixtures.write_text(json.dumps([{'label': l, 'input': x.hex(), 'output': y.hex()}
                                       for l, x, y in zip(labels, raw, expected)], indent=2) + '\n')
        row = {'arguments': args, 'artifact_sha256': digest(path), 'fixture_sha256': digest(fixtures),
               'fixture_lanes': len(raw), 'input_bits': artifact['input_bits'], 'output_bits': len(artifact['outputs']),
               'export_seconds': elapsed, 'adapter_operations': statistics(artifact), 'all_outputs_match': True}
        results.append(row); print(json.dumps(row), flush=True)
        if compile_backend and not options.skip_backend:
            row['mpc_compilations'] = [compile_and_check(path, raw, expected, batch) for batch in (1, 16)]
            for result in row['mpc_compilations']:
                assert result['bit_triples'] == row['adapter_operations']['executed_and_gates'] * result['batch']
            print(json.dumps({'arguments': args, 'mpc_compilations': row['mpc_compilations']}), flush=True)
    assert before == {str(p.relative_to(ROOT)): digest(p) for p in sources}, 'Sources changed during checks'
    report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'cases': results, 'source_sha256': before,
              'exporter_command': command, 'native_mpc_executed': False, 'throughput_measured': False,
              'backend_bytecode_compiled': not options.skip_backend,
              'full_actual_libsignal_chain_send_refinement': False,
              'limitations': ['Synthetic public fixtures only; native MPC remains unexecuted.',
                  'The secret SPQR-key presence/key and outgoing PQ bytes must come from the same future verified SPQR transition.',
                  'Counter exhaustion rejects; rejected output preserves old chain key/counter and zeros wire bytes.',
                  'Atomic database commit, rollback protection and proactive refresh are not implemented by this pure circuit.',
                  'Full actual RustCrypto/Signal state-machine equivalence remains separate from proved Lean circuit lowering.']}
    target = ROOT / 'benchmarks/results/lean-signal-chain-send-checks.json'
    target.write_text(json.dumps(report, indent=2) + '\n')
    print(f'Passed {sum(r["fixture_lanes"] for r in results)} bounded chain-send fixture lanes.', flush=True)


if __name__ == '__main__':
    main()
