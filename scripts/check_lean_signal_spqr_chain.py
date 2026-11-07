#!/usr/bin/env python3
"""Independent public HKDF/state fixtures for the Lean SPQR chain advance."""
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


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def reference(key, counter):
    if counter == 0xffffffff:
        return b'\x00' + key + counter.to_bytes(4, 'big') + bytes(32)
    next_counter = (counter + 1).to_bytes(4, 'big')
    info = next_counter + b'Signal PQ Ratchet V1 Chain Next'
    prk = hmac.digest(bytes(32), key, 'sha256')
    first = hmac.digest(prk, info + b'\x01', 'sha256')
    second = hmac.digest(prk, first + info + b'\x02', 'sha256')
    return b'\xff' + first + next_counter + second


def sources():
    result = set()
    def visit(module):
        if not module.startswith('TlsMpc'):
            return
        path = ROOT / (module.replace('.', '/') + '.lean')
        if path in result:
            return
        result.add(path)
        for imported in re.findall(r'^import ([A-Za-z0-9_.]+)', path.read_text(), re.M):
            visit(imported)
    visit('TlsMpc.Signal.SpqrChain')
    return sorted(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compile-backend', action='store_true')
    args = parser.parse_args()
    files = [*sources(), Path(__file__), ROOT / 'SignalReference/SpqrChainExport.lean',
             ROOT / 'scripts/check_lean_crypto.py', ROOT / 'scripts/clear_circuit.py',
             ROOT / 'test_support/circuit.py', ROOT / 'backend_adapter/aig.py',
             ROOT / 'backend_adapter/boolean.py', ROOT / 'programs/lean_artifact.mpc',
             ROOT / 'lean-toolchain', ROOT / '.deps/libsignal-vendor/spqr/src/chain.rs',
             ROOT / '.deps/libsignal-vendor/spqr/src/kdf.rs', ROOT / '.deps/libsignal-v0.106.1/Cargo.lock']
    if args.compile_backend:
        backend = ROOT / '.deps/MP-SPDZ'
        files += [backend / 'compile.py', *sorted((backend / 'Compiler').rglob('*.py'))]
    snapshot = {str(p.relative_to(ROOT)): digest(p) for p in files}
    rows = []
    keys = [bytes(32), bytes([255]) * 32, bytes(range(32)), hashlib.sha256(b'public SPQR fixture').digest()]
    counters = [0, 1, 127, 128, 255, 256, 65535, 65536, 0xfffffff, 0x10000000, 0xfffffffe, 0xffffffff]
    for k, key in enumerate(keys):
        for counter in counters:
            rows.append((f'key{k}-counter{counter}', key + counter.to_bytes(4, 'big'), reference(key, counter)))
    # Consecutive transitions bind the next chain key and the incremented counter.
    key, counter = hashlib.sha256(b'public sequential SPQR fixture').digest(), 126
    for i in range(8):
        output = reference(key, counter)
        rows.append((f'sequential-{i}', key + counter.to_bytes(4, 'big'), output))
        key, counter = output[1:33], int.from_bytes(output[33:37], 'big')
    directory = ROOT / '.deps/signal-spqr-chain-artifacts'; directory.mkdir(exist_ok=True)
    artifact_path = directory / 'signal-spqr-chain.json'
    started = time.perf_counter()
    with artifact_path.open('w') as output:
        subprocess.run(['lake', 'env', 'lean', '--run', 'SignalReference/SpqrChainExport.lean', 'signal-spqr-chain'],
                       cwd=ROOT, stdout=output, check=True, timeout=300)
    elapsed = time.perf_counter() - started
    artifact = load(artifact_path)
    inputs = [x for _, x, _ in rows]; expected = [y for _, _, y in rows]
    observed = evaluate_lanes(artifact, inputs)
    assert observed == expected, [label for (label, _, _), got, want in zip(rows, observed, expected) if got != want]
    fixture_path = directory / 'fixtures.json'
    fixture_path.write_text(json.dumps([{'label': label, 'input': x.hex(), 'output': y.hex()}
                                        for label, x, y in rows], indent=2) + '\n')
    operations = statistics(artifact)
    print(json.dumps({'fixture_lanes': len(rows), 'export_seconds': elapsed, 'adapter_operations': operations}), flush=True)
    compiled = []
    if args.compile_backend:
        compiled = [compile_and_check(artifact_path, inputs, expected, batch) for batch in (1, 16)]
        for row in compiled:
            assert row['bit_triples'] == operations['executed_and_gates'] * row['batch']
    assert snapshot == {str(p.relative_to(ROOT)): digest(p) for p in files}, 'Sources changed during checks'
    report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'source_sha256': snapshot,
              'artifact_sha256': digest(artifact_path), 'fixture_sha256': digest(fixture_path),
              'input_bits': artifact['input_bits'], 'output_bits': len(artifact['outputs']),
              'public_fixture_lanes': len(rows), 'all_outputs_match': True,
              'export_seconds': elapsed, 'adapter_operations': operations,
              'mpc_compilations': compiled, 'native_mpc_executed': False, 'throughput_measured': False,
              'full_actual_spqr_refinement': False,
              'reference_commit': '06959b4708f9b7b1e94d0f8cc835f3958c077e94',
              'scope': 'Symmetric SPQR chain advance only; counter prefix uses incremented BE32. All inputs, status and state/key outputs remain shared.',
              'remaining': ['Actual HKDF/SPQR implementation-reference composition', 'Epoch selection and ratchet/KEM/chunk transitions',
                            'SPQR message serialization and full Signal send composition', 'Atomic persistence and proactive refresh']}
    target = ROOT / 'benchmarks/results/lean-signal-spqr-chain-checks.json'
    target.write_text(json.dumps(report, indent=2) + '\n')
    print(f'Passed {len(rows)} SPQR chain fixture lanes; backend compilations: {len(compiled)}.', flush=True)


if __name__ == '__main__':
    main()
