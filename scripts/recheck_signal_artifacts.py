#!/usr/bin/env python3
"""Confirm old Signal backend evidence still applies after exporter changes."""

import hashlib
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    subprocess.run(['lake', 'build', 'emit_mpc'], cwd=ROOT, check=True)
    reference = ROOT / 'benchmarks/results/lean-signal-checks.json'
    prior = json.loads(reference.read_text())
    executable = ROOT / '.lake/build/bin/emit_mpc'
    paths = [ROOT / name for name in prior['source_sha256']]
    paths += [executable, Path(__file__).resolve()]
    before = {str(path.relative_to(ROOT)): digest(path) for path in paths}
    adapter_paths = ['backend_adapter/aig.py', 'backend_adapter/boolean.py', 'programs/lean_artifact.mpc']
    adapter_unchanged = all(before[name] == prior['source_sha256'][name] for name in adapter_paths)
    destination = ROOT / '.deps/signal-artifacts-current'
    destination.mkdir(parents=True, exist_ok=True)
    records = []
    for previous in prior['cases']:
        args = previous['arguments']
        path = destination / ('-'.join(args) + '.json')
        start = time.perf_counter()
        with path.open('w') as output:
            subprocess.run([str(executable), *args], cwd=ROOT, stdout=output, check=True, timeout=300)
        record = {'arguments': args, 'artifact_sha256': digest(path),
                  'previous_artifact_sha256': previous['artifact_sha256'],
                  'native_export_seconds': time.perf_counter() - start}
        record['identical_artifact'] = record['artifact_sha256'] == record['previous_artifact_sha256']
        records.append(record)
        print(json.dumps(record), flush=True)
    after = {str(path.relative_to(ROOT)): digest(path) for path in paths}
    if before != after:
        raise RuntimeError('exporter or sources changed during recheck')
    report = {'kind': 'signal_artifact_evidence_recheck', 'cases': records,
              'previous_report': str(reference.relative_to(ROOT)),
              'previous_report_sha256': digest(reference), 'source_sha256': before,
              'adapter_sources_identical': adapter_unchanged,
              'previous_backend_evidence_applicable': adapter_unchanged and all(x['identical_artifact'] for x in records),
              'backend_reexecuted': False, 'native_mpc_executed': False, 'throughput_measured': False,
              'note': 'Byte-identical artifacts and adapter sources reuse the recorded backend compile/public-clear checks; this is not a new backend run.'}
    (ROOT / 'benchmarks/results/lean-signal-artifact-recheck.json').write_text(json.dumps(report, indent=2) + '\n')
    if not report['previous_backend_evidence_applicable']:
        raise RuntimeError('changed artifact or adapter needs fresh backend checks')


if __name__ == '__main__':
    main()
