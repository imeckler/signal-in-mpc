#!/usr/bin/env python3
"""Compile the proved schedule artifact and check public MPC-source fixtures.

This does not execute an MPC networking process or measure WAN throughput.
"""

from datetime import datetime, timezone
import json
from pathlib import Path
import sys
import tarfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(HERE.parent))
from extract import digest
from scripts.check_lean_crypto import compile_and_check


def main():
    audit_path = HERE / 'schedule-proof-check.json'
    audit = json.loads(audit_path.read_text())
    if not audit['complete_portable_aes256_key_schedule_refinement'] or audit['custom_axioms']:
        raise ValueError('Complete schedule proof audit is missing')
    artifact = HERE / 'Artifacts/aes256-key-schedule.json'
    fixture_path = HERE / 'Artifacts/aes256-key-schedule-fixtures.json'
    if digest(artifact) != audit['artifact']['sha256'] or digest(fixture_path) != audit['actual_translated_fixture_sha256']:
        raise ValueError('Artifact or actual translated fixtures differ from proof audit')
    for name, expected in audit['root_sources_sha256'].items():
        if digest(ROOT / name) != expected:
            raise ValueError(f'Proved root operation changed: {name}')
    for name, expected in audit['proof_sources_sha256'].items():
        if digest(HERE.parent / name) != expected:
            raise ValueError(f'Reference proof changed: {name}')
    backend = ROOT / '.deps/MP-SPDZ'
    sources = [ROOT / name for name in ('backend_adapter/aig.py', 'backend_adapter/boolean.py',
        'programs/lean_artifact.mpc', 'scripts/check_lean_crypto.py', 'scripts/clear_circuit.py',
        'test_support/circuit.py')]
    sources += [backend / 'compile.py', *sorted((backend / 'Compiler').rglob('*.py'))]
    before = {str(path.relative_to(ROOT)): digest(path) for path in sources}
    pin_path = ROOT / 'benchmarks/config/dependencies.json'
    pin = json.loads(pin_path.read_text())['mp_spdz']
    archive = ROOT / '.deps/mp-spdz-v0.4.4.tar.gz'
    if digest(archive) != pin['source_archive_sha256']:
        raise ValueError('Pinned backend source archive differs')
    with tarfile.open(archive) as bundle:
        entries = {member.name.split('/', 1)[-1]: member
                   for member in bundle.getmembers() if member.isfile()}
        for path in [backend / 'compile.py', *sorted((backend / 'Compiler').rglob('*.py'))]:
            name = path.relative_to(backend).as_posix()
            if name not in entries or bundle.extractfile(entries[name]).read() != path.read_bytes():
                raise ValueError(f'Backend compiler source differs from pinned archive: {name}')
    fixtures = json.loads(fixture_path.read_text())
    inputs = [bytes(row['input']) for row in fixtures]
    outputs = [bytes(row['output']) for row in fixtures]
    results = []
    for batch in (1, 16):
        result = compile_and_check(artifact, inputs, outputs, batch)
        if result['bit_triples'] != audit['artifact']['executed_and_gates'] * batch:
            raise ValueError('Unexpected schedule AND cost in backend compilation')
        results.append(result)
        print(json.dumps(result), flush=True)
    if before != {str(path.relative_to(ROOT)): digest(path) for path in sources}:
        raise ValueError('Compiler/adapter source changed during compilation')
    report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(),
              'operation': 'actual_portable_aes256_key_schedule',
              'proof_audit_sha256': digest(audit_path), 'artifact_sha256': digest(artifact),
              'fixture_sha256': digest(fixture_path), 'compiler_backend_commit': pin['commit'],
              'compiler_backend_pin': pin, 'compiler_source_matches_pinned_archive': True,
              'dependency_manifest_sha256': digest(pin_path),
              'source_sha256': before, 'compilations': results,
              'backend_bytecode_compiled': True, 'public_mpc_source_outputs_checked': True,
              'native_mpc_execution_tested': False, 'throughput_measured': False,
              'harness_source_sha256': digest(Path(__file__))}
    (HERE / 'schedule-backend-check.json').write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
