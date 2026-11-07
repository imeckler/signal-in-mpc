#!/usr/bin/env python3
"""Public artifact-to-artifact integration checks; no networked MPC claim."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def varint_size(value):
    return max(1, (value.bit_length() + 6) // 7)


def main():
    source_report = ROOT / 'benchmarks/results/lean-signal-send-checks.json'
    report = json.loads(source_report.read_text())
    for name, sha in report['source_sha256'].items():
        assert digest(ROOT / name) == sha, f'Send source snapshot changed: {name}'
    exporter = ROOT / '.lake/build/bin/emit_mpc'
    exporter_hash = digest(exporter)
    main_hash = digest(ROOT / 'Main.lean')
    directory = ROOT / '.deps/signal-send-artifacts'
    cases = []
    for row in report['cases']:
        args = row['arguments']
        if args[0] != 'signal-send':
            continue
        pt_size, pq_size, cw, pw = map(int, args[1:5])
        has_address = args[5] == 'present'
        ct_size = (pt_size // 16 + 1) * 16
        ct_offset = 1 + 35 + 1 + cw + 1 + pw + 1 + varint_size(ct_size)
        address_offset = ct_offset + ct_size + (1 + varint_size(pq_size) + pq_size if pq_size else 0) + 2
        sender_path = directory / ('-'.join(args) + '.json')
        fixture_path = sender_path.with_name(sender_path.stem + '-fixtures.json')
        assert digest(sender_path) == row['artifact_sha256']
        assert digest(fixture_path) == row['fixture_sha256']
        fixtures = json.loads(fixture_path.read_text())
        raw = [bytes.fromhex(f['input']) for f in fixtures]
        sent = evaluate_lanes(load(sender_path), raw)
        wire_size = len(sent[0]) - 1
        receiver_args = ['signal-open-span', str(wire_size), str(ct_offset), str(ct_size),
                         str(address_offset) if has_address else 'none']
        receiver_path = directory / ('roundtrip-' + '-'.join(args[1:]) + '.json')
        with receiver_path.open('w') as output:
            subprocess.run([str(exporter), *receiver_args], cwd=ROOT, stdout=output, check=True, timeout=300)
        inputs, expected = [], []
        for fields, output in zip(raw, sent):
            key_material = fields[41:185]
            addresses = fields[-36:] if has_address else b''
            inputs.append(key_material + output[1:] + addresses)
            plaintext = fields[185:185 + pt_size]
            accepted = output[0] == 255 and fields[0] & 15 in (3, 4)
            expected.append(b'\xff' + pt_size.to_bytes(8, 'big') + plaintext + bytes(ct_size - pt_size)
                            if accepted else bytes(9 + ct_size))
        observed = evaluate_lanes(load(receiver_path), inputs)
        if observed != expected:
            failures = [fixture['label'] for fixture, got, want in zip(fixtures, observed, expected) if got != want]
            raise AssertionError(f'Artifact send/receive mismatch {args}: {failures}')
        case = {'send_arguments': args, 'receive_arguments': receiver_args,
                'fixture_lanes': len(inputs), 'send_artifact_sha256': digest(sender_path),
                'receive_artifact_sha256': digest(receiver_path), 'all_outputs_match': True}
        cases.append(case)
        print(json.dumps(case), flush=True)
    assert digest(exporter) == exporter_hash and digest(ROOT / 'Main.lean') == main_hash
    result = {'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'cases': cases,
              'send_fixture_report_sha256': digest(source_report),
              'receive_exporter_sha256': exporter_hash, 'root_main_sha256': main_hash,
              'harness_sha256': digest(Path(__file__)),
              'native_mpc_executed': False, 'throughput_measured': False,
              'scope': 'The actual numeric send artifact output becomes input to the numeric bounded-span receive artifact; public profiles establish positions in these generated messages.',
              'limitations': ['This is public differential integration testing, not an encryption-inverse proof.',
                              'General protobuf parsing and complete actual Rust constructor equivalence remain separate obligations.']}
    target = ROOT / 'benchmarks/results/lean-signal-roundtrip-checks.json'
    target.write_text(json.dumps(result, indent=2) + '\n')
    print(f'Passed {sum(c["fixture_lanes"] for c in cases)} artifact-to-artifact fixture lanes.', flush=True)


if __name__ == '__main__':
    main()
