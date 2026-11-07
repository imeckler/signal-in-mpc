#!/usr/bin/env python3
"""Check the proved Signal DH-root circuit and unverified mixed composition.

All test keys/agreements are synthetic public data. Optional compilation is
not native MPC execution and does not measure network throughput.
"""
from datetime import datetime, timezone
import argparse
import hashlib
import hmac
import json
import os
from pathlib import Path
import random
import re
import shutil
import subprocess
import sys
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey, X25519PublicKey
from backend_adapter.boolean import load as load_boolean, execute as execute_boolean
from backend_adapter.aig import statistics
from handshake_backend.field_dag import load as load_field, evaluate_clear, MODULUS
from SignalReference.DhRatchetWork.adapter import create_chain
from scripts.check_lean_crypto import evaluate_lanes, compile_and_check


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def wire_bits(data):
    return [(byte >> shift) & 1 for byte in data for shift in range(7, -1, -1)]


def wire_bytes(bits):
    return bytes(sum(bits[8 * i + j] << (7 - j) for j in range(8)) for i in range(len(bits) // 8))


def expected(root, agreement):
    if agreement == bytes(32):
        return b'\x00' + root + bytes(36)
    prk = hmac.digest(root, agreement, 'sha256')
    first = hmac.digest(prk, b'WhisperRatchet\x01', 'sha256')
    second = hmac.digest(prk, first + b'WhisperRatchet\x02', 'sha256')
    return b'\xff' + first + second + bytes(4)


def source_files():
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
    visit('TlsMpc.Signal.DhRatchet')
    return sorted(found)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compile-backend', action='store_true')
    parser.add_argument('--compile-mixed', action='store_true')
    options = parser.parse_args()
    references = [ROOT / '.deps/libsignal-v0.106.1/rust/protocol/src/ratchet/keys.rs',
                  ROOT / '.deps/libsignal-v0.106.1/rust/core/src/curve.rs']
    sources = [*source_files(), Path(__file__), ROOT / 'lean-toolchain',
               ROOT / 'SignalReference/DhRatchetExport.lean', ROOT / 'SignalReference/DhRatchetChecks.lean',
               ROOT / 'SignalReference/DhRatchetWork/adapter.py', ROOT / 'SignalReference/DhRatchetWork/program.mpc',
               ROOT / 'handshake_backend/mixed.py', ROOT / 'handshake_backend/field_dag.py',
               ROOT / 'backend_adapter/aig.py', ROOT / 'backend_adapter/boolean.py', ROOT / 'programs/lean_artifact.mpc',
               ROOT / 'scripts/check_lean_crypto.py', ROOT / 'scripts/clear_circuit.py', ROOT / 'test_support/circuit.py',
               *references]
    backend = ROOT / '.deps/MP-SPDZ'
    if options.compile_backend or options.compile_mixed:
        sources += [backend / 'compile.py', *sorted((backend / 'Compiler').rglob('*.py'))]
    snapshot = {str(p.relative_to(ROOT)): digest(p) for p in sources}
    subprocess.run(['lake', 'build', 'TlsMpc.Signal.DhRatchet'], cwd=ROOT, check=True)
    checks = ROOT / 'SignalReference/DhRatchetChecks.lean'
    audited = subprocess.run(['lake', 'env', 'lean', str(checks)], cwd=ROOT,
                             capture_output=True, text=True, check=True)
    endpoints = re.findall(r'^#print axioms (\S+)', checks.read_text(), re.M)
    found = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", audited.stdout)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    assert [name for name, _ in found] == endpoints and len(found) == 15
    for name, assumptions in found:
        assert not ({x.strip() for x in assumptions.split(',') if x.strip()} - allowed), name
    directory = ROOT / '.deps/signal-dh-ratchet-artifacts'; directory.mkdir(exist_ok=True)
    paths = []
    command = ['lake', 'env', 'lean', '--run', 'SignalReference/DhRatchetExport.lean']
    for name in ('signal-dh-field', 'signal-dh-ratchet'):
        path = directory / (name + '.json')
        with path.open('w') as output:
            subprocess.run([*command, name], cwd=ROOT, stdout=output, check=True, timeout=300)
        paths.append(path)
    field_path, boolean_path = paths
    field, boolean = load_field(field_path), load_boolean(boolean_path)
    rng = random.Random(7748_5869)
    pairs = []
    for i in range(32):
        pairs.append((f'random-{i}', rng.randbytes(32), rng.randbytes(32), rng.randbytes(32)))
    scalar = bytes.fromhex('77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a')
    root = rng.randbytes(32)
    for peer in (0, 1, MODULUS - 1, MODULUS, MODULUS + 1, 9, MODULUS + 9, (1 << 255) + 9):
        pairs.append((f'peer-{peer}', root, scalar, peer.to_bytes(32, 'little')))
    for toggle in (1, 2, 4, 1 << 254, 1 << 255, 7 | (1 << 254) | (1 << 255)):
        private = (int.from_bytes(scalar, 'little') ^ toggle).to_bytes(32, 'little')
        pairs.append((f'clamped-bits-{toggle}', root, private, (9).to_bytes(32, 'little')))
    raw, outputs, fixtures = [], [], []
    for name, key, private, peer in pairs:
        try:
            want_agreement = X25519PrivateKey.from_private_bytes(private).exchange(X25519PublicKey.from_public_bytes(peer))
        except ValueError:
            want_agreement = bytes(32)
        scalar_bits = [(int.from_bytes(private, 'little') >> i) & 1 for i in range(256)]
        point = (int.from_bytes(peer, 'little') & ((1 << 255) - 1)) % MODULUS
        agreement = evaluate_clear(field, scalar_bits + [point])[0].to_bytes(32, 'little')
        assert agreement == want_agreement, name
        result = expected(key, want_agreement)
        raw.append(key + agreement); outputs.append(result)
        fixtures.append({'label': name, 'root': key.hex(), 'private': private.hex(), 'peer': peer.hex(),
                         'agreement': agreement.hex(), 'output': result.hex()})
    for index in range(32):
        agreement = bytes(index) + b'\x01' + bytes(31 - index)
        key = rng.randbytes(32)
        raw.append(key + agreement); outputs.append(expected(key, agreement))
        fixtures.append({'label': f'nonzero-agreement-byte-{index}', 'root': key.hex(),
                         'agreement': agreement.hex(), 'output': outputs[-1].hex()})
    for key in (bytes(32), bytes([255]) * 32, root):
        raw.append(key + bytes(32)); outputs.append(expected(key, bytes(32)))
        fixtures.append({'label': 'zero-agreement-preserves-root', 'root': key.hex(),
                         'agreement': bytes(32).hex(), 'output': outputs[-1].hex()})
    assert evaluate_lanes(boolean, raw) == outputs

    # Exercise the actual unverified composition adapter on public clear bits.
    # Curve arithmetic and final KDF are still evaluated from the Lean artifacts.
    def as_field(bits, mask_high_bit=False):
        value = int.from_bytes(wire_bytes(bits), 'little')
        if mask_high_bit:
            value &= (1 << 255) - 1
        return value % MODULUS
    public_primitives = SimpleNamespace(
        wire_bits_to_scalar_fields=lambda bits: [bits[8 * (i // 8) + 7 - i % 8] for i in range(256)],
        wire_bits_to_field=as_field,
        execute_secret=evaluate_clear,
        field_to_wire_bits=lambda x: wire_bits(x.to_bytes(32, 'little')),
        execute_boolean=lambda image, inputs: execute_boolean(image, inputs, 0, 1))
    for name, key, private, peer in (pairs[0], pairs[1], pairs[32], pairs[33]):
        actual = wire_bytes(create_chain(field, boolean, wire_bits(key), wire_bits(private), wire_bits(peer),
                                         primitives=public_primitives))
        fixture = next(row for row in fixtures if row['label'] == name)
        assert actual.hex() == fixture['output'], name
    fixture_path = directory / 'fixtures.json'
    fixture_path.write_text(json.dumps(fixtures, indent=2) + '\n')
    report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'checked_endpoints': len(found),
              'field_fixture_lanes': len(pairs), 'boolean_fixture_lanes': len(raw), 'adapter_clear_cases': 4,
              'field_nodes': len(field['nodes']),
              'field_multiplications': sum(n['op'] == 'mul' for n in field['nodes']),
              'boolean_adapter_operations': statistics(boolean),
              'artifacts': {str(p.relative_to(ROOT)): digest(p) for p in paths},
              'fixture_sha256': digest(fixture_path), 'all_outputs_match': True,
              'native_mpc_executed': False, 'throughput_measured': False,
              'actual_dalek_or_rustcrypto_wrapper_equivalence': False,
              'conversion_boundary': 'Composition theorem assumes the exact canonical field-to-byte relation; mixed adapter remains unverified.'}
    print(json.dumps(report), flush=True)
    if options.compile_backend:
        report['boolean_mpc_compilations'] = [compile_and_check(boolean_path, raw, outputs, batch) for batch in (1, 16)]
    if options.compile_mixed:
        shutil.copy2(ROOT / 'SignalReference/DhRatchetWork/program.mpc', backend / 'Programs/Source/signal_dh_ratchet.mpc')
        env = os.environ.copy()
        env['PYTHONPATH'] = str(ROOT) + os.pathsep + env.get('PYTHONPATH', '')
        compile_command = [sys.executable, './compile.py', '-X', '-P', str(MODULUS),
                           'signal_dh_ratchet', str(field_path), str(boolean_path)]
        compiled = subprocess.run(compile_command, cwd=backend, env=env, capture_output=True, text=True, timeout=600)
        log = ROOT / 'benchmarks/results/raw/signal-dh-ratchet-mixed-compile.log'
        log.write_text(compiled.stdout + compiled.stderr)
        if compiled.returncode:
            raise RuntimeError((compiled.stdout + compiled.stderr)[-6000:])
        bytecodes = sorted((backend / 'Programs/Bytecode').glob('signal_dh_ratchet*.bc'))
        assert bytecodes
        report['mixed_mpc_compilation'] = {'command': compile_command, 'compiler_log_sha256': digest(log),
            'bytecode_sha256': {p.name: digest(p) for p in bytecodes}, 'native_executed': False,
            'input_boundary': 'Each root/private/peer byte is XOR shared by five parties; output stays in shared memory.'}
    assert snapshot == {str(p.relative_to(ROOT)): digest(p) for p in sources}, 'Sources changed during audit'
    report['source_sha256'] = snapshot
    (ROOT / 'benchmarks/results/lean-signal-dh-ratchet-checks.json').write_text(json.dumps(report, indent=2) + '\n')
    axiom_path = ROOT / 'SignalReference/dh-ratchet-axioms.txt'
    axiom_path.write_text(audited.stdout)
    proof_report = {'checked_at_utc': report['checked_at_utc'], 'checked_endpoints': len(found),
                    'theorems': endpoints, 'allowed_foundational_axioms': sorted(allowed), 'custom_axioms': [],
                    'source_sha256': snapshot, 'axiom_report_sha256': digest(axiom_path),
                    'actual_dalek_or_rustcrypto_wrapper_equivalence': False,
                    'unverified_conversion_exact_representation_required': True,
                    'full_ratchet_state_transition_or_persistence': False}
    (ROOT / 'SignalReference/dh-ratchet-proof-check.json').write_text(json.dumps(proof_report, indent=2) + '\n')
    print(f'Passed {len(found)} proof endpoints, {len(pairs)} X25519 and {len(raw)} root-chain fixture lanes.', flush=True)


if __name__ == '__main__':
    main()
