#!/usr/bin/env python3
"""Independent SPQR decoder fixtures; preserve implementation overflow rules."""
from datetime import datetime, timezone
import argparse
import hashlib
import json
from pathlib import Path
import random
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from backend_adapter.boolean import load
from backend_adapter.aig import statistics
from scripts.check_lean_crypto import evaluate_lanes, compile_and_check


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def decode(data, offset=0):
    if offset >= len(data):
        return False, offset, 0
    value = 0
    for i in range(min(10, len(data) - offset)):
        byte = data[offset + i]
        value |= ((byte & 127) << (7 * i)) & ((1 << 64) - 1)
        if byte < 128:
            return True, offset + i + 1, value
    return False, offset, 0


def cases():
    rng = random.Random(0x53505152)
    for size in (0, 1, 2, 9, 10, 11, 32, 64, 128, 256):
        for offset_mode in (False, True):
            raw, expected, labels = [], [], []
            mode = 'signal-spqr-decode-at' if offset_mode else 'signal-spqr-decode'
            def add(label, data, start=0):
                assert len(data) == size
                success, end, value = decode(data, start)
                if offset_mode:
                    raw.append(start.to_bytes(8, 'big') + data)
                    result = bytes([255 if success else 0]) + end.to_bytes(8, 'big') + value.to_bytes(8, 'big')
                else:
                    assert start == 0
                    raw.append(data)
                    result = bytes([255 if success else 0, end if success else 0]) + value.to_bytes(8, 'big')
                expected.append(result); labels.append(label)
            for byte in (0, 1, 127, 128, 255):
                add(f'uniform-{byte}', bytes([byte]) * size)
            for i in range(24):
                add(f'random-{i}', rng.randbytes(size), rng.randrange(size + 2) if offset_mode else 0)
            if size == 1:
                for byte in range(256):
                    add(f'first-byte-{byte}', bytes([byte]))
            if size >= 10:
                for count in range(1, 11):
                    add(f'noncanonical-zero-{count}', b'\x80' * (count - 1) + b'\x00' + b'\xff' * (size - count))
                    add(f'full-payload-{count}', b'\xff' * (count - 1) + b'\x7f' + b'\x80' * (size - count))
                if size == 10:
                    for last in range(256):
                        add(f'exact-tenth-byte-{last}', b'\xff' * 9 + bytes([last]))
                if size > 10:
                    add('eleventh-byte-cannot-terminate', b'\x80' * 10 + b'\x00' + b'\x01' * (size - 11))
            if offset_mode:
                base = rng.randbytes(size)
                for start in range(size + 2):
                    add(f'every-offset-{start}', base, start)
                for start in (0, max(0, size - 10), max(0, size - 1), size, size + 1, 2**32, 2**64 - 1):
                    add(f'truncated-tail-{start}', bytes([128]) * size, start)
                    if size:
                        add(f'last-byte-terminates-{start}', bytes([128]) * (size - 1) + b'\x00', start)
            args = [mode, str(size)]
            selected = (not offset_mode and size == 10) or (offset_mode and size == 64)
            yield args, raw, expected, labels, selected


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
    visit('TlsMpc.Signal.SpqrDecodeAt')
    return sorted(found)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compile-backend', action='store_true')
    options = parser.parse_args()
    sources = [*lean_sources(), Path(__file__), ROOT / 'lean-toolchain',
               ROOT / 'SignalReference/SpqrDecodeExport.lean', ROOT / 'SignalReference/SpqrDecodeChecks.lean',
               ROOT / 'scripts/check_lean_crypto.py', ROOT / 'scripts/clear_circuit.py', ROOT / 'test_support/circuit.py',
               ROOT / 'backend_adapter/aig.py', ROOT / 'backend_adapter/boolean.py', ROOT / 'programs/lean_artifact.mpc',
               ROOT / '.deps/libsignal-vendor/spqr/src/lib.rs']
    if options.compile_backend:
        backend = ROOT / '.deps/MP-SPDZ'
        sources += [backend / 'compile.py', *sorted((backend / 'Compiler').rglob('*.py'))]
    snapshot = {str(p.relative_to(ROOT)): digest(p) for p in sources}
    subprocess.run(['lake', 'build', 'TlsMpc.Signal.SpqrDecodeAt'], cwd=ROOT, check=True)
    checks = ROOT / 'SignalReference/SpqrDecodeChecks.lean'
    result = subprocess.run(['lake', 'env', 'lean', str(checks)], cwd=ROOT, capture_output=True, text=True, check=True)
    endpoints = re.findall(r'^#print axioms (\S+)', checks.read_text(), re.M)
    found = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", result.stdout)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    assert [name for name, _ in found] == endpoints and len(found) == 36
    for name, assumptions in found:
        assert not ({x.strip() for x in assumptions.split(',') if x.strip()} - allowed), name
    directory = ROOT / '.deps/signal-spqr-decode-artifacts'; directory.mkdir(exist_ok=True)
    command = ['lake', 'env', 'lean', '--run', 'SignalReference/SpqrDecodeExport.lean']
    results = []
    for args, raw, expected, labels, selected in cases():
        path = directory / ('-'.join(args) + '.json')
        with path.open('w') as output:
            subprocess.run([*command, *args], cwd=ROOT, stdout=output, check=True, timeout=300)
        artifact = load(path)
        observed = evaluate_lanes(artifact, raw)
        if observed != expected:
            failures = [label for label, got, want in zip(labels, observed, expected) if got != want]
            raise AssertionError(f'Decoder mismatch {args}: {failures}')
        fixtures = path.with_name(path.stem + '-fixtures.json')
        fixtures.write_text(json.dumps([{'label': label, 'input': inp.hex(), 'output': out.hex()}
                                       for label, inp, out in zip(labels, raw, expected)], indent=2) + '\n')
        row = {'arguments': args, 'artifact_sha256': digest(path), 'fixture_sha256': digest(fixtures),
               'fixture_lanes': len(raw), 'input_bits': artifact['input_bits'], 'output_bits': len(artifact['outputs']),
               'adapter_operations': statistics(artifact), 'all_outputs_match': True}
        if selected and options.compile_backend:
            row['mpc_compilations'] = [compile_and_check(path, raw, expected, batch) for batch in (1, 16)]
        results.append(row); print(json.dumps(row), flush=True)
    assert snapshot == {str(p.relative_to(ROOT)): digest(p) for p in sources}, 'Sources changed during decoder check'
    report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'checked_endpoints': len(found),
              'cases': results, 'source_sha256': snapshot, 'exporter_command': command,
              'native_mpc_executed': False, 'throughput_measured': False,
              'backend_bytecode_compiled': options.compile_backend,
              'implementation_rule': 'Actual SPQR accepts noncanonical encodings and truncates excess tenth-byte payload bits; this is not Prost overflow policy.',
              'full_message_parser': False, 'actual_reference_report': 'SignalReference/VarintDecodeWork/proof-report.json (separate audit)'}
    (ROOT / 'benchmarks/results/lean-signal-spqr-decode-checks.json').write_text(json.dumps(report, indent=2) + '\n')
    axioms = ROOT / 'SignalReference/spqr-decode-axioms.txt'; axioms.write_text(result.stdout)
    proof = {'checked_at_utc': report['checked_at_utc'], 'checked_endpoints': len(found), 'theorems': endpoints,
             'allowed_foundational_axioms': sorted(allowed), 'custom_axioms': [], 'source_sha256': snapshot,
             'axiom_report_sha256': digest(axioms),
             'operation': 'secret prefix and secret-offset SPQR varint decode; failure preserves offset and zeroes value',
             'actual_reference_proof_audited_separately': 'SignalReference/VarintDecodeWork/proof-report.json'}
    (ROOT / 'SignalReference/spqr-decode-proof-check.json').write_text(json.dumps(proof, indent=2) + '\n')
    print(f'Passed {len(results)} decoder profiles, {sum(r["fixture_lanes"] for r in results)} fixtures and36 kernel endpoints.', flush=True)


if __name__ == '__main__':
    main()
