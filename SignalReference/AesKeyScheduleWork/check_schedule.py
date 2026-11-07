#!/usr/bin/env python3
"""Audit the actual portable AES256 entrypoint-to-numeric-circuit proof."""

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import time

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent
sys.path.insert(0, str(REFERENCE))
sys.path.insert(0, str(ROOT))
from extract import PINS, check_sources, digest
from AesKeyScheduleLeavesWork.check import audit_reference
from backend_adapter import aig


def dependencies():
    reference, root, order = {}, {}, []

    def visit(module):
        relative = module.replace('.', '/') + '.lean'
        if relative in reference or relative in root:
            return
        if module.startswith('TlsMpc'):
            source, destination = ROOT / relative, root
        elif module.startswith(('LibSignalReference', 'AesKeySchedule')):
            source, destination = REFERENCE / relative, reference
        else:
            return
        destination[relative] = digest(source)
        for imported in re.findall(r'^import ([A-Za-z0-9_.]+)', source.read_text(), re.M):
            visit(imported)
        if destination is reference and not module.startswith('LibSignalReference'):
            order.append(module.replace('.', '/'))

    visit('AesKeyScheduleWork.FullSchedule')
    return reference, root, order


def check_image(image, fixtures):
    aig.validate(image)
    if image['input_bits'] != 256 or image['input_widths'] != [8] * 32 or len(image['outputs']) != 7680:
        raise ValueError('Unexpected actual key-schedule ABI')
    if len(fixtures) != 16 or any(len(f['input']) != 32 or len(f['output']) != 960 for f in fixtures):
        raise ValueError('Missing actual translated entrypoint fixtures')
    packed_input = [sum(((f['input'][i // 8] >> (7 - i % 8)) & 1) << lane
                        for lane, f in enumerate(fixtures)) for i in range(256)]
    expected = [sum(((f['output'][i // 8] >> (7 - i % 8)) & 1) << lane
                    for lane, f in enumerate(fixtures)) for i in range(7680)]
    for optimize in (False, True):
        if aig.execute(image, packed_input, 0, (1 << len(fixtures)) - 1, optimize=optimize) != expected:
            raise ValueError('Numeric artifact differs from actual translated schedule fixture')
    return {'nodes': len(image['nodes']), **aig.statistics(image), 'input_bits': 256,
            'output_bits': 7680, 'public_fixtures': 16, 'raw_and_optimized_adapter_checked': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packages-dir', type=Path, required=True)
    args = parser.parse_args()
    check_sources()
    reference = audit_reference()
    canonical = json.loads((REFERENCE / 'Extraction/proof-check.json').read_text())
    leaf_audit = json.loads((REFERENCE / 'AesKeyScheduleLeavesWork/proof-check.json').read_text())
    reference_hashes, root_hashes, modules = dependencies()
    for name, expected_hash in reference_hashes.items():
        if name.startswith('LibSignalReference/') and canonical['proof_sources_sha256'].get(name) != expected_hash:
            raise ValueError(f'Reused canonical proof changed: {name}')
        if re.search(r'\b(sorry|admit|axiom|native_decide)\b', (REFERENCE / name).read_text()):
            raise ValueError(f'Incomplete or externally checked proof dependency: {name}')
    backend = (REFERENCE / PINS['aeneas']['directory'] / 'backends/lean').resolve()
    archive = ROOT / '.deps/aeneas-macos-aarch64-2026-08-27.tar.gz'
    if digest(archive) != PINS['aeneas']['macos_aarch64_archive_sha256']:
        raise ValueError('Official Aeneas archive differs')
    models = set(canonical['standard_model_sources_sha256']) | set(leaf_audit['standard_model_sources_sha256'])
    models.update(['Aeneas/Std/Core/Iter.lean', 'Aeneas/Std/Array/ArraySlice.lean'])
    with tarfile.open(archive) as bundle:
        for name in models:
            if bundle.extractfile('backends/lean/' + name).read() != (backend / name).read_bytes():
                raise ValueError(f'Official computational model changed: {name}')
    for path in (ROOT / 'lean-toolchain', REFERENCE / 'lean-toolchain', backend / 'lean-toolchain'):
        if path.read_text().strip() != PINS['aeneas']['lean_toolchain']:
            raise ValueError(f'Lean toolchain changed: {path}')
    paths = [REFERENCE / '.lake/build/lib/lean', ROOT / '.lake/build/lib/lean', backend / '.lake/build/lib/lean']
    package_revisions = {}
    for package in json.loads((backend / 'lake-manifest.json').read_text())['packages']:
        directory = args.packages_dir / package['name']
        revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=directory, text=True).strip()
        if revision != package['rev']:
            raise ValueError(f'Cached proof dependency changed: {directory}')
        package_revisions[package['name']] = revision
        path = directory / '.lake/build/lib/lean'
        if path.is_dir():
            paths.append(path)
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(map(str, paths))
    adapter_hash = digest(ROOT / 'backend_adapter/aig.py')
    subprocess.run(['lake', 'build', 'TlsMpc.Signal.AesKeyInput'], cwd=ROOT, check=True)
    for module in modules:
        target = paths[0] / (module + '.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(['lean', '-o', str(target), module + '.lean'], cwd=REFERENCE, env=env, check=True)
    audit = subprocess.check_output(['lean', 'AesKeyScheduleWork/ScheduleChecks.lean'],
                                    cwd=REFERENCE, env=env, text=True)
    print(audit, end='')
    expected_names = re.findall(r'^#print axioms (\S+)', (HERE / 'ScheduleChecks.lean').read_text(), re.M)
    reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", audit)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    if [name for name, _ in reports] != expected_names:
        raise ValueError('Missing or unexpected complete schedule theorem')
    if any({value.strip() for value in names.split(',') if value.strip()} - allowed for _, names in reports):
        raise ValueError('Complete schedule proof has nonstandard assumptions')
    (HERE / 'schedule-axiom-report.txt').write_text(audit)
    # Fixture generation has no imports with an executable main declaration.
    target = paths[0] / 'AesKeyScheduleWork/PublicInputs.olean'
    subprocess.run(['lean', '-o', str(target), 'AesKeyScheduleWork/PublicInputs.lean'],
                   cwd=REFERENCE, env=env, check=True)
    timings = {}
    for name, file in [('ScheduleExport', 'aes256-key-schedule.json'),
                       ('ScheduleFixtures', 'aes256-key-schedule-fixtures.json')]:
        started = time.perf_counter()
        output = subprocess.check_output(['lean', '--run', 'AesKeyScheduleWork/' + name + '.lean'],
                                         cwd=REFERENCE, env=env, text=True, timeout=180)
        (HERE / 'Artifacts' / file).write_text(output)
        timings[name] = time.perf_counter() - started
    artifact_path = HERE / 'Artifacts/aes256-key-schedule.json'
    fixture_path = HERE / 'Artifacts/aes256-key-schedule-fixtures.json'
    artifact = check_image(json.loads(artifact_path.read_text()), json.loads(fixture_path.read_text()))
    if (reference_hashes, root_hashes, modules) != dependencies() or digest(ROOT / 'backend_adapter/aig.py') != adapter_hash:
        raise ValueError('Proof/compiler/adapter sources changed during audit')
    report = {
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'complete_portable_aes256_key_schedule_refinement': True,
        'complete_signal_or_aes_cipher_refinement': False,
        'reference': reference,
        'operation': 'Actual aes0.9.1 portable soft::fixslice::aes256_key_schedule selected from pinned libsignal Cargo.lock',
        'domain': 'Every32-byte secret key; successful full120-word fixslice schedule; actual checked arithmetic, borrows, loop order, StepBy transitions and final exit preserved.',
        'final_theorem': 'LibSignalReference.Candidate.AesKeySchedule.key_schedule_refines_artifact',
        'all_array_inputs_theorem': 'LibSignalReference.Candidate.AesKeySchedule.key_schedule_all_arrays',
        'all_outputs_remain_secret': True, 'custom_axioms': [], 'source_patches': [],
        'cryptographic_stubs': [], 'standard_computational_models_unchanged': True,
        'allowed_foundational_axioms': sorted(allowed), 'theorems': expected_names,
        'checked_theorem_endpoints': len(reports), 'proof_sources_sha256': reference_hashes,
        'root_sources_sha256': root_hashes, 'proof_package_revisions': package_revisions,
        'standard_model_sources_sha256': {name: digest(backend / name) for name in sorted(models)},
        'axiom_report_sha256': digest(HERE / 'schedule-axiom-report.txt'),
        'artifact': {'sha256': digest(artifact_path), **artifact},
        'actual_translated_fixture_sha256': digest(fixture_path),
        'native_export_seconds': timings, 'native_mpc_execution_tested': False,
        'adapter_source_sha256': adapter_hash,
        'harness_sources_sha256': {name: digest(HERE / name) for name in
                                  ('ScheduleExport.lean', 'ScheduleFixtures.lean', 'PublicInputs.lean', 'ScheduleChecks.lean')},
        'audit_script_sha256': digest(Path(__file__)),
        'remaining_composition_boundaries': [
            'Actual add_round_key mutable Zip borrow write-back model',
            'Actual inv_bitslice hybrid-array initialization wrapper',
            'Complete AES block encryption and CBC wrapper equivalence',
            'Signal message MAC/serialization and established-session send-state composition'],
    }
    (HERE / 'schedule-proof-check.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Checked actual AES256 key schedule through numeric artifact: {len(reports)} endpoints; 16 translated fixtures.')


if __name__ == '__main__':
    main()
