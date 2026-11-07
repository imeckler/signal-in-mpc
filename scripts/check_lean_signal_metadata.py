#!/usr/bin/env python3
"""Exercise the exported Signal identifier and tag circuits on public inputs."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from backend_adapter.boolean import execute, load
from backend_adapter.aig import statistics
from scripts.check_lean_crypto import compile_and_check


def cases():
    raw, expected = [], []
    for kind in (0, 1):
        for uuid in (bytes(16), bytes([255]) * 16, bytes(range(16)),
                     hashlib.sha256(b'public service id fixture').digest()[:16]):
            # Harness bytes are a transport envelope for 129 input bits.
            # The final seven bits are padding, outside the circuit input.
            value = ((kind << 128) | int.from_bytes(uuid, 'big')) << 7
            for padding in (0, 127):
                raw.append((value | padding).to_bytes(17, 'big'))
                expected.append(bytes([kind]) + uuid)
    yield ('signal-service-id',), raw, expected, [1] + [8] * 16
    for name, accepted in (('signal-service-id-kind', (0, 1)),
                           ('signal-ciphertext-message-type', (2, 3, 7, 8))):
        raw = [bytes([tag]) for tag in range(256)]
        expected = [bytes([int(tag in accepted), tag]) for tag in range(256)]
        yield (name,), raw, expected, [8]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--skip-backend', action='store_true')
    args = parser.parse_args()
    subprocess.run(['lake', 'build', 'emit_mpc'], cwd=ROOT, check=True)
    records = []
    with tempfile.TemporaryDirectory(prefix='signal-metadata-') as directory:
        for command, raw, expected, widths in cases():
            path = Path(directory) / (command[0] + '.json')
            with path.open('w') as output:
                subprocess.run([str(ROOT / '.lake/build/bin/emit_mpc'), *command],
                               stdout=output, check=True, timeout=30)
            image = load(path)
            if image['input_widths'] != widths:
                raise AssertionError('incorrect mixed-width input ABI')
            inputs = [sum(((x[i // 8] >> (7 - i % 8)) & 1) << lane for lane, x in enumerate(raw))
                      for i in range(image['input_bits'])]
            bits = execute(image, inputs, 0, (1 << len(raw)) - 1)
            observed = [bytes(sum(((bits[i + j] >> lane) & 1) << (7 - j) for j in range(8))
                              for i in range(0, len(bits), 8)) for lane in range(len(raw))]
            if observed != expected:
                raise AssertionError(f'metadata fixture mismatch: {command}')
            result = {'arguments': command, 'input_bits': image['input_bits'], 'input_widths': widths,
                      'output_bits': len(bits), 'adapter_operations': statistics(image),
                      'fixture_lanes': len(raw), 'all_outputs_match': True,
                      'artifact_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
            if not args.skip_backend:
                result['mpc_compilations'] = [compile_and_check(path, raw, expected, batch) for batch in (1, 16)]
            records.append(result)
            print(json.dumps(result), flush=True)
    names = ('TlsMpc/Signal/ServiceId.lean', 'TlsMpc/Signal/Tag.lean', 'TlsMpc/ByteCircuit.lean',
             'TlsMpc/AigExport.lean', 'Main.lean', 'backend_adapter/aig.py',
             'backend_adapter/boolean.py', 'programs/lean_artifact.mpc')
    paths = [ROOT / name for name in names] + [Path(__file__).resolve()]
    report = {'kind': 'lean_signal_metadata_checks', 'cases': records,
              'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
              'native_mpc_executed': False, 'throughput_measured': False,
              'implementation_refinement_audit': 'SignalReference/Extraction/proof-check.json',
              'limitations': ['Metadata operations only; no complete Signal session transition.',
                              'The actual implementation-equivalence proofs are audited separately.',
                              'Native export, JSON, adapter and MPC execution are unverified.']}
    (ROOT / 'benchmarks/results/lean-signal-metadata-checks.json').write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
