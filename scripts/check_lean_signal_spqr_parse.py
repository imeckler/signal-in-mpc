#!/usr/bin/env python3
"""Differential public fixtures for shared-cursor SPQR V1 parsing.

This independent Python fixture is not an accepted Rust implementation model.
Actual varint refinement is audited separately in VarintDecodeWork.
"""
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


def read_varint(wire, start):
    value = 0
    for i, byte in enumerate(wire[start:start + 10]):
        value = (value | ((byte & 127) << (7 * i))) & ((1 << 64) - 1)
        if byte < 128:
            return value, start + i + 1
    raise ValueError('unterminated varint')


def parse(wire):
    try:
        if not wire or wire[0] != 1:
            raise ValueError('not V1')
        epoch, at = read_varint(wire, 1)
        if epoch == 0:
            raise ValueError('zero epoch')
        index, at = read_varint(wire, at)
        if index > 0xffffffff or at >= len(wire):
            raise ValueError('invalid index or missing kind')
        kind = wire[at]
        at += 1
        if kind not in range(7):
            raise ValueError('invalid kind')
        has_chunk = kind not in (0, 4)
        chunk_index, data = 0, bytes(32)
        if has_chunk:
            chunk_index, at = read_varint(wire, at)
            if chunk_index > 65535 or at + 32 > len(wire):
                raise ValueError('invalid or truncated chunk')
            data = wire[at:at + 32]
        return b'\xff' + epoch.to_bytes(8, 'big') + index.to_bytes(4, 'big') + bytes([kind, has_chunk]) + chunk_index.to_bytes(2, 'big') + data
    except ValueError:
        return bytes(49)


def varint(value, width=None):
    out = []
    while value:
        out.append(value & 127)
        value >>= 7
    if not out:
        out = [0]
    if width is not None:
        assert len(out) <= width <= 10
        out += [0] * (width - len(out))
    return bytes(byte | (128 if i + 1 < len(out) else 0) for i, byte in enumerate(out))


def fixtures():
    rng = random.Random(0x5350515250415253)
    sizes = (0, 1, 3, 4, 5, 10, 20, 36, 37, 38, 39, 48, 64, 128, 256)
    groups = {n: [] for n in sizes}
    def add(size, label, wire):
        assert len(wire) == size
        groups[size].append((label, wire, parse(wire)))
    for size in sizes:
        for byte in (0, 1, 127, 128, 255):
            add(size, f'uniform-{byte}', bytes([byte]) * size)
        for i in range(24):
            add(size, f'random-{i}', rng.randbytes(size))
        for kind in range(7):
            wire = b'\x01\x01\x00' + bytes([kind])
            if kind not in (0, 4):
                wire += b'\x00' + rng.randbytes(32)
            if len(wire) <= size:
                add(size, f'kind-{kind}-trailing-{size-len(wire)}', wire + rng.randbytes(size - len(wire)))
    for version in range(256):
        add(4, f'version-{version}', bytes([version, 1, 0, 0]))
    for kind in range(256):
        add(37, f'kind-byte-{kind}', bytes([1, 1, 0, kind, 0]) + bytes(32))
    for epoch in (0, 1, 127, 128, 2**32 - 1, 2**32, 2**63, 2**64 - 1):
        for index in (0, 1, 127, 128, 2**31, 2**32 - 1, 2**32, 2**64 - 1):
            for chunk in (0, 127, 128, 65535, 65536, 2**64 - 1):
                wire = b'\x01' + varint(epoch) + varint(index) + b'\x02' + varint(chunk) + rng.randbytes(32)
                add(64, f'boundaries-{epoch}-{index}-{chunk}', wire + rng.randbytes(64-len(wire)))
    for width in range(1, 11):
        for slot in ('epoch', 'index', 'chunk'):
            pieces = {'epoch': varint(1), 'index': varint(0), 'chunk': varint(0)}
            pieces[slot] = varint(1 if slot == 'epoch' else 0, width)
            wire = b'\x01' + pieces['epoch'] + pieces['index'] + b'\x03' + pieces['chunk'] + rng.randbytes(32)
            add(64, f'noncanonical-{slot}-{width}', wire + bytes(64 - len(wire)))
    for last in range(256):
        for slot in ('epoch', 'index', 'chunk'):
            pieces = {'epoch': b'\x01', 'index': b'\x00', 'chunk': b'\x00'}
            pieces[slot] = b'\x80' * 9 + bytes([last])
            wire = b'\x01' + pieces['epoch'] + pieces['index'] + b'\x05' + pieces['chunk'] + rng.randbytes(32)
            add(64, f'tenth-byte-{slot}-{last}', wire + bytes(64 - len(wire)))
    # Tail lengths one below, exactly at and beyond each chunk boundary.
    for size in sizes:
        if size >= 4:
            for width in range(1, 11):
                wire = b'\x01\x01\x00\x06' + varint(65535, max(width, 3)) + rng.randbytes(32)
                add(size, f'chunk-tail-{width}-{size}', (wire + b'\x80' * size)[:size])
            for width in range(1, 11):
                # An incomplete varint cannot terminate on zero-filled absent data.
                tail = b'\x01' + b'\x80' * width
                wire = (b'\x01\x01\x00\x00' + bytes(size))[:size - len(tail)] + tail if len(tail) <= size else tail[:size]
                add(size, f'unterminated-tail-{width}', wire)
    # Every truncation point in a maximum-width accepted message is tested.
    wire = b'\x01' + varint(2**64 - 1) + varint(2**32 - 1, 10) + b'\x06' + varint(65535, 10) + rng.randbytes(32)
    assert len(wire) == 64 and parse(wire)[0] == 255
    for size in sizes:
        add(size, 'max-width-truncation', (wire + bytes(size))[:size])
    return groups


def sources():
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
    visit('TlsMpc.Signal.SpqrParseSpec')
    found |= {Path(__file__), ROOT / 'lean-toolchain', ROOT / 'SignalReference/SpqrParseExport.lean',
              ROOT / 'SignalReference/SpqrParseChecks.lean', ROOT / 'scripts/check_lean_crypto.py',
              ROOT / 'scripts/clear_circuit.py', ROOT / 'test_support/circuit.py',
              ROOT / 'backend_adapter/aig.py', ROOT / 'backend_adapter/boolean.py', ROOT / 'programs/lean_artifact.mpc',
              ROOT / '.deps/libsignal-vendor/spqr/src/lib.rs', ROOT / '.deps/libsignal-vendor/spqr/src/v1/chunked/states/serialize.rs'}
    return found


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('--compile-backend', action='store_true')
    options = cli.parse_args()
    files = sources()
    if options.compile_backend:
        backend = ROOT / '.deps/MP-SPDZ'
        files |= {backend / 'compile.py', *sorted((backend / 'Compiler').rglob('*.py'))}
    snapshot = {str(p.relative_to(ROOT)): digest(p) for p in sorted(files)}
    subprocess.run(['lake', 'build', 'TlsMpc.Signal.SpqrParseSpec'], cwd=ROOT, check=True)
    checks = ROOT / 'SignalReference/SpqrParseChecks.lean'
    checked = subprocess.run(['lake', 'env', 'lean', str(checks)], cwd=ROOT, capture_output=True, text=True, check=True)
    endpoints = re.findall(r'^#print axioms (\S+)', checks.read_text(), re.M)
    found = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", checked.stdout)
    assert [name for name, _ in found] == endpoints
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for name, axioms in found:
        assert not ({a.strip() for a in axioms.split(',') if a.strip()} - allowed), name
    directory = ROOT / '.deps/signal-spqr-parse-artifacts'
    directory.mkdir(exist_ok=True)
    command = ['lake', 'env', 'lean', '--run', 'SignalReference/SpqrParseExport.lean', 'signal-spqr-parse']
    results = []
    for size, cases in fixtures().items():
        path = directory / f'signal-spqr-parse-{size}.json'
        with path.open('w') as output:
            subprocess.run([*command, str(size)], cwd=ROOT, stdout=output, check=True, timeout=300)
        artifact = load(path)
        labels, raw, expected = map(list, zip(*cases))
        observed = evaluate_lanes(artifact, raw)
        assert observed == expected, (size, [label for label, got, want in zip(labels, observed, expected) if got != want])
        fixture_file = path.with_name(path.stem + '-fixtures.json')
        fixture_file.write_text(json.dumps([{'label': label, 'input': inp.hex(), 'output': out.hex()}
                                            for label, inp, out in cases], indent=2) + '\n')
        row = {'wire_bytes': size, 'artifact_sha256': digest(path), 'fixture_sha256': digest(fixture_file),
               'fixture_lanes': len(raw), 'input_bits': artifact['input_bits'], 'output_bits': len(artifact['outputs']),
               'adapter_operations': statistics(artifact), 'all_outputs_match': True}
        if options.compile_backend and size in (37, 64):
            # Exercise every accepted payload branch as well as rejection in
            # the source-level backend check; batch1 starts with a real chunk.
            picked = [next(case for case in cases if case[2][0] == 255 and case[2][13] == kind)
                      for kind in (2, 0, 1, 3, 4, 5, 6)]
            picked += [case for case in cases if case[2][0] == 0][:9]
            row['backend_fixture_labels'] = [case[0] for case in picked]
            row['mpc_compilations'] = [compile_and_check(path, [case[1] for case in picked],
                                                        [case[2] for case in picked], batch)
                                       for batch in (1, 16)]
        results.append(row)
        print(json.dumps(row), flush=True)
    assert snapshot == {str(p.relative_to(ROOT)): digest(p) for p in sorted(files)}, 'Sources changed during check'
    report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'checked_endpoints': len(found),
              'source_sha256': snapshot, 'cases': results, 'exporter_command': command,
              'backend_bytecode_compiled': options.compile_backend, 'native_mpc_executed': False,
              'throughput_measured': False, 'all_inputs_and_outputs_secret': True,
              'public_parameters': ['input byte length'], 'output_bytes': 49,
              'version_scope': 'V1 only; V0 negotiation handled separately',
              'full_actual_rust_parser_refinement': False,
              'actual_varint_reference': 'SignalReference/VarintDecodeWork/acceptance.json',
              'state_machine_or_kem': False}
    (ROOT / 'benchmarks/results/lean-signal-spqr-parse-checks.json').write_text(json.dumps(report, indent=2) + '\n')
    axioms_path = ROOT / 'SignalReference/spqr-parse-axioms.txt'
    axioms_path.write_text(checked.stdout)
    proof = {'checked_at_utc': report['checked_at_utc'], 'checked_endpoints': len(found), 'theorems': endpoints,
             'source_sha256': snapshot, 'axiom_report_sha256': digest(axioms_path),
             'allowed_foundational_axioms': sorted(allowed), 'custom_axioms': [],
             'operation': 'V1 message parse through shared cursor reads and varints; kernel theorem to branch-based Nat-cursor parser spec',
             'full_actual_rust_parser_refinement': False}
    (ROOT / 'SignalReference/spqr-parse-proof-check.json').write_text(json.dumps(proof, indent=2) + '\n')
    print(f'Passed {len(results)} profiles, {sum(r["fixture_lanes"] for r in results)} fixtures and {len(found)} theorem endpoints.')


if __name__ == '__main__':
    main()
