#!/usr/bin/env python3
"""Public independent SPQR V1 wire and canonical-width fixtures."""
from datetime import datetime, timezone
import argparse
import hashlib
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


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def varint(value):
    result = []
    while value >= 128:
        result.append((value & 127) | 128)
        value >>= 7
    return bytes([*result, value])


def smallest(width):
    return 0 if width == 1 else 1 << (7 * (width - 1))


def profiles():
    for ew in range(1, 11):
        yield ew, 1 + (ew - 1) % 5, 0, False
        yield ew, 5 - (ew - 1) % 5, 1 + (ew - 1) % 3, True
    yield 10, 5, 3, True


def fixtures(ew, iw, cw, chunk):
    epoch, index = smallest(ew), smallest(iw)
    chunk_index = smallest(cw) if chunk else 0
    data = hashlib.sha256(f'public SPQR chunk {ew}-{iw}-{cw}'.encode()).digest()
    rows = []
    wire_size = 2 + ew + iw + (cw + 32 if chunk else 0)

    def add(label, e=epoch, i=index, kind=1 if chunk else 0, c=chunk_index, payload=data):
        accepted = (len(varint(e)) == ew and len(varint(i)) == iw and
                    (kind in (1, 2, 3, 5, 6) if chunk else kind in (0, 4)) and
                    (not chunk or len(varint(c)) == cw))
        raw = e.to_bytes(8, 'big') + i.to_bytes(4, 'big') + bytes([kind])
        if chunk:
            raw += c.to_bytes(2, 'big') + payload
        if accepted:
            wire = b'\x01' + varint(e) + varint(i) + bytes([kind])
            if chunk:
                wire += varint(c) + payload
            output = b'\xff' + wire
        else:
            output = bytes(1 + wire_size)
        rows.append((label, raw, output))

    for kind in range(256) if ew == 1 else (0, 1, 2, 3, 4, 5, 6, 7, 255):
        add(f'kind-{kind}', kind=kind)
    for e in sorted({0, 127, 128, (1 << 63) - 1, 1 << 63, (1 << 64) - 1,
                     smallest(ew), max(0, smallest(ew) - 1), min((1 << 64) - 1, (1 << (7 * ew)) - 1)}):
        add(f'epoch-{e}', e=e)
    for i in sorted({0, 127, 128, (1 << 28) - 1, 1 << 28, (1 << 32) - 1,
                     smallest(iw), max(0, smallest(iw) - 1), min((1 << 32) - 1, (1 << (7 * iw)) - 1)}):
        add(f'index-{i}', i=i)
    if chunk:
        for c in (0, 127, 128, 16383, 16384, 65535):
            add(f'chunk-index-{c}', c=c)
        add('chunk-zero', payload=bytes(32)); add('chunk-ones', payload=bytes([255]) * 32)
    return rows


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
    visit('TlsMpc.Signal.SpqrMessage')
    return sorted(found)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compile-backend', action='store_true')
    args = parser.parse_args()
    files = [*source_files(), Path(__file__), ROOT / 'SignalReference/SpqrMessageExport.lean',
             ROOT / 'scripts/check_lean_crypto.py', ROOT / 'scripts/clear_circuit.py',
             ROOT / 'test_support/circuit.py', ROOT / 'backend_adapter/aig.py',
             ROOT / 'backend_adapter/boolean.py', ROOT / 'programs/lean_artifact.mpc', ROOT / 'lean-toolchain',
             ROOT / '.deps/libsignal-vendor/spqr/src/v1/chunked/states/serialize.rs',
             ROOT / '.deps/libsignal-vendor/spqr/src/lib.rs', ROOT / '.deps/libsignal-v0.106.1/Cargo.lock']
    if args.compile_backend:
        backend = ROOT / '.deps/MP-SPDZ'
        files += [backend / 'compile.py', *sorted((backend / 'Compiler').rglob('*.py'))]
    snapshot = {str(p.relative_to(ROOT)): digest(p) for p in files}
    directory = ROOT / '.deps/signal-spqr-message-artifacts'; directory.mkdir(exist_ok=True)
    results = []
    for ew, iw, cw, chunk in profiles():
        arguments = ['signal-spqr-message', str(ew), str(iw), str(cw), 'present' if chunk else 'none']
        path = directory / ('-'.join(arguments) + '.json')
        started = time.perf_counter()
        with path.open('w') as output:
            subprocess.run(['lake', 'env', 'lean', '--run', 'SignalReference/SpqrMessageExport.lean', *arguments],
                           cwd=ROOT, stdout=output, check=True, timeout=300)
        elapsed = time.perf_counter() - started
        artifact = load(path); cases = fixtures(ew, iw, cw, chunk)
        inputs = [x for _, x, _ in cases]; expected = [y for _, _, y in cases]
        observed = evaluate_lanes(artifact, inputs)
        assert observed == expected, [label for (label, _, _), got, want in zip(cases, observed, expected) if got != want]
        fixture_path = path.with_name(path.stem + '-fixtures.json')
        fixture_path.write_text(json.dumps([{'label': label, 'input': x.hex(), 'output': y.hex()}
                                            for label, x, y in cases], indent=2) + '\n')
        row = {'arguments': arguments, 'artifact_sha256': digest(path), 'fixture_sha256': digest(fixture_path),
               'fixture_lanes': len(cases), 'export_seconds': elapsed, 'input_bits': artifact['input_bits'],
               'output_bits': len(artifact['outputs']), 'adapter_operations': statistics(artifact), 'all_outputs_match': True}
        if args.compile_backend and ((ew, iw, cw, chunk) in ((1, 1, 0, False), (10, 5, 3, True))):
            row['mpc_compilations'] = [compile_and_check(path, inputs, expected, batch) for batch in (1, 16)]
        results.append(row); print(json.dumps(row), flush=True)
    assert snapshot == {str(p.relative_to(ROOT)): digest(p) for p in files}, 'Sources changed during checks'
    report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'source_sha256': snapshot,
              'cases': results, 'native_mpc_executed': False, 'throughput_measured': False,
              'full_spqr_state_machine_refined': False,
              'scope': 'SPQR V1 serialization and secret canonical-width/kind checks; public chunk presence and varint widths.',
              'reference_commit': '06959b4708f9b7b1e94d0f8cc835f3958c077e94',
              'remaining': ['Actual Rust serializer/varint equivalence is separate ongoing work',
                            'SPQR epoch/KEM/chunk state transitions and Signal send composition']}
    target = ROOT / 'benchmarks/results/lean-signal-spqr-message-checks.json'
    target.write_text(json.dumps(report, indent=2) + '\n')
    print(f'Passed {len(results)} SPQR message profiles and {sum(r["fixture_lanes"] for r in results)} public fixture lanes.', flush=True)


if __name__ == '__main__':
    main()
