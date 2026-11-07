#!/usr/bin/env python3
"""Audit the reviewed extraction, copy/column helpers and public fixtures.

The complete schedule theorem has its own check_schedule.py audit.
"""

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent
sys.path.insert(0, str(REFERENCE))
sys.path.insert(0, str(ROOT))
from extract import PINS, check_sources, digest
from AesKeyScheduleWork.inspect_metadata import select
from backend_adapter import aig


def check_helper_image(image):
    """Unverified ABI/serializer check on zero and the complete bit basis.

    This is additional evidence about native export, not the refinement proof.
    Each Python integer packs one lane per input basis vector.
    """
    aig.validate(image)
    length = len(image['input_widths'])
    width = 64 * length
    if image['input_widths'] != [64] * length or image['input_bits'] != width:
        raise ValueError('Unexpected key-helper input ABI')
    words = [[1 << (64 * word + 63 - bit) for bit in range(64)] for word in range(length)]
    offset = image['offset']
    if image['operation'] == 'copy':
        for i in reversed(range(8)):
            words[offset + 8 + i] = list(words[offset + i])
    elif image['operation'] == 'columns':
        rotation, distance = image['rotation'], image['distance']
        for i in range(8):
            previous, current = words[offset + i - distance], words[offset + i]
            rk = [previous[bit] ^ (current[(bit + rotation) % 64]
                  if (0x000f000f000f000f >> bit) & 1 else 0) for bit in range(64)]
            words[offset + i] = [rk[bit] ^
                (rk[bit - 4] if bit >= 4 and (0xfff0fff0fff0fff0 >> bit) & 1 else 0) ^
                (rk[bit - 8] if bit >= 8 and (0xff00ff00ff00ff00 >> bit) & 1 else 0) ^
                (rk[bit - 12] if bit >= 12 and (0xf000f000f000f000 >> bit) & 1 else 0)
                for bit in range(64)]
    else:
        raise ValueError('Unknown key helper operation')
    expected = [word[8 * byte + bit] for word in words for byte in range(8) for bit in reversed(range(8))]
    for optimize in (False, True):
        if aig.execute(image, [1 << bit for bit in range(width)], 0, (1 << width) - 1,
                       optimize=optimize) != expected:
            raise ValueError('Key-helper numeric export differs on the complete basis')
        if any(aig.execute(image, [0] * width, 0, 1, optimize=optimize)):
            raise ValueError('Key-helper zero fixture differs')
    stats = aig.statistics(image)
    if stats['executed_and_gates'] != 0:
        raise ValueError('Linear key-helper unexpectedly requires secret AND')
    destination = HERE / 'Artifacts' / (image['name'] + '.json')
    destination.parent.mkdir(exist_ok=True)
    destination.write_text(json.dumps(image, separators=(',', ':')) + '\n')
    return {'name': image['name'], 'artifact_sha256': digest(destination),
            'input_bits': width, 'nodes': len(image['nodes']), **stats,
            'zero_and_all_basis_vectors_checked': True, 'raw_and_optimized_adapter_checked': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packages-dir', type=Path, required=True)
    args = parser.parse_args()
    check_sources()
    original = REFERENCE / 'Extraction/libsignal_aes256_key_schedule.llbc'
    selected = HERE / 'selected.llbc'
    expected, changes = select(json.loads(original.read_text()))
    review = json.loads((HERE / 'review.json').read_text())
    if (expected != json.loads(selected.read_text()) or changes != review['changes'] or
            digest(original) != review['original_sha256'] or digest(selected) != review['selected_sha256']):
        raise ValueError('Reviewed extraction differs')
    for name, expected in review['generated_files'].items():
        if digest(REFERENCE / name) != expected:
            raise ValueError(f'Generated reference differs: {name}')
    if sorted(p.name for p in (HERE / 'Generated').glob('*.lean')) != ['Funs.lean', 'Types.lean']:
        raise ValueError('Unexpected generated files or external template')
    backend = (REFERENCE / PINS['aeneas']['directory'] / 'backends/lean').resolve()
    archive = ROOT / '.deps/aeneas-macos-aarch64-2026-08-27.tar.gz'
    if digest(archive) != PINS['aeneas']['macos_aarch64_archive_sha256']:
        raise ValueError('Official model archive differs')
    models = set(json.loads((REFERENCE / 'Extraction/proof-check.json').read_text())['standard_model_sources_sha256'])
    models.update(['Aeneas/Std/Array/ArraySlice.lean', 'Aeneas/Std/Scalar/Ops/Mul.lean'])
    with tarfile.open(archive) as bundle:
        for name in models:
            if bundle.extractfile('backends/lean/' + name).read() != (backend / name).read_bytes():
                raise ValueError(f'Official model differs: {name}')
    paths = [REFERENCE / '.lake/build/lib/lean', ROOT / '.lake/build/lib/lean',
             backend / '.lake/build/lib/lean']
    for package in json.loads((backend / 'lake-manifest.json').read_text())['packages']:
        directory = args.packages_dir / package['name']
        revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=directory, text=True).strip()
        if revision != package['rev']:
            raise ValueError(f'Cached package differs: {directory}')
        path = directory / '.lake/build/lib/lean'
        if path.is_dir():
            paths.append(path)
    for path in (ROOT / 'lean-toolchain', REFERENCE / 'lean-toolchain', backend / 'lean-toolchain'):
        if path.read_text().strip() != PINS['aeneas']['lean_toolchain']:
            raise ValueError(f'Toolchain differs: {path}')
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(map(str, paths))
    root_sources = ['TlsMpc/Signal/AesKeyCopy.lean', 'TlsMpc/Signal/AesKeyColumns.lean',
                    'TlsMpc/Signal/AesKeySchedule.lean', 'TlsMpc/Signal/AesKeyScheduleOps.lean',
                    'TlsMpc/ByteCircuit.lean', 'TlsMpc/AigExport.lean', 'TlsMpc/BvConstruct.lean',
                    'backend_adapter/aig.py']
    root_hashes = {name: digest(ROOT / name) for name in root_sources}
    subprocess.run(['lake', 'build', 'TlsMpc.Signal.AesMixPhases', 'TlsMpc.Signal.AesKeySchedule'], cwd=ROOT, check=True)
    for module in ('AesKeyScheduleWork/Generated/Types', 'AesKeyScheduleWork/Generated/Funs',
                   'AesKeyScheduleWork/CopyReference', 'AesKeyScheduleWork/CopyBridge',
                   'AesKeyScheduleWork/ColumnsReference', 'AesKeyScheduleWork/ColumnsBridge',
                   'AesKeyScheduleWork/PublicInputs'):
        target = paths[0] / (module + '.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(['lean', '-o', str(target), module + '.lean'], cwd=REFERENCE, env=env, check=True)
    assumptions = subprocess.check_output(['lean', 'AesKeyScheduleWork/Assumptions.lean'],
                                          cwd=REFERENCE, env=env, text=True)
    reports = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", assumptions)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    if len(reports) != 3 or any({x.strip() for x in names.split(',')} - allowed for _, names in reports):
        raise ValueError('Unexpected assumptions in actual generated operation')
    copy_audit = subprocess.check_output(['lean', 'AesKeyScheduleWork/Checks.lean'],
                                        cwd=REFERENCE, env=env, text=True)
    copy_reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", copy_audit)
    if len(copy_reports) != 12 or any({x.strip() for x in names.split(',') if x.strip()} - allowed for _, names in copy_reports):
        raise ValueError('Unexpected or missing copy refinement assumptions')
    columns_audit = subprocess.check_output(['lean', 'AesKeyScheduleWork/ColumnsChecks.lean'],
                                           cwd=REFERENCE, env=env, text=True)
    columns_reports = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", columns_audit)
    if len(columns_reports) != 14 or any({x.strip() for x in names.split(',') if x.strip()} - allowed for _, names in columns_reports):
        raise ValueError('Unexpected or missing column recurrence refinement assumptions')
    images = json.loads(subprocess.check_output(['lean', '--run', 'AesKeyScheduleWork/Export.lean'],
                                                cwd=REFERENCE, env=env, text=True))
    if len(images) != 4:
        raise ValueError('Missing key-helper numeric exports')
    artifacts = [check_helper_image(image) for image in images]
    public_output = subprocess.check_output(['lean', '--run', 'AesKeyScheduleWork/PublicCheck.lean'],
                                            cwd=REFERENCE, env=env, text=True)
    if '16 public AES256 schedule representation fixtures passed' not in public_output:
        raise ValueError('Public representation check did not report completion')
    if root_hashes != {name: digest(ROOT / name) for name in root_sources}:
        raise ValueError('Root compiler/adapter sources changed during checks')
    report = {'checked_at_utc': datetime.now(timezone.utc).isoformat(),
              'extraction_reviewed': True, 'complete_schedule_refinement_checked_here': False,
              'complete_schedule_proof_audit': 'AesKeyScheduleWork/schedule-proof-check.json',
              'audit_scope': 'Actual reverse copy and column recurrence numeric refinements; public schedule representation fixtures.',
              'canonical_reference_integrated': False, 'no_crypto_stubs': True,
              'allowed_foundational_axioms': sorted(allowed),
              'generated_operation_axiom_reports': [name for name, _ in reports],
              'copy_refinement_theorems_checked': [name for name, _ in copy_reports],
              'memshift32_numeric_refinement_established': True,
              'memshift32_domain': 'All word values, public aligned src with src+16 within public slice length; actual reverse iterator and checked copy preserved.',
              'copy_proof_sources_sha256': {name: digest(HERE / name) for name in ('CopyReference.lean', 'CopyBridge.lean')},
              'copy_circuit_source_sha256': digest(ROOT / 'TlsMpc/Signal/AesKeyCopy.lean'),
              'columns_refinement_theorems_checked': [name for name, _ in columns_reports],
              'xor_columns_numeric_refinement_established': True,
              'xor_columns_domain': 'All word values and u32 rotation distances; public distance <= offset and offset+8 within public slice length, including overlapping ranges. Checked arithmetic and original iteration order are preserved.',
              'columns_proof_sources_sha256': {name: digest(HERE / name) for name in ('ColumnsReference.lean', 'ColumnsBridge.lean')},
              'columns_circuit_source_sha256': digest(ROOT / 'TlsMpc/Signal/AesKeyColumns.lean'),
              'helper_artifacts': artifacts, 'export_source_sha256': digest(HERE / 'Export.lean'),
              'compiler_adapter_sources_sha256': root_hashes,
              'public_representation_fixtures': 16, 'public_checks_are_not_refinement_proofs': True,
              'selected_llbc_sha256': digest(selected), 'trusted_selection_source_sha256': digest(HERE / 'inspect_metadata.py'),
              'generated_files': review['generated_files'],
              'standard_model_sources_sha256': {name: digest(backend / name) for name in sorted(models)},
              'public_check_source_sha256': digest(HERE / 'PublicCheck.lean'),
              'public_inputs_source_sha256': digest(HERE / 'PublicInputs.lean'),
              'root_aes_source_sha256': digest(ROOT / 'TlsMpc/Aes.lean'),
              'audit_source_sha256': digest(Path(__file__)), 'native_mpc_execution_tested': False}
    (HERE / 'check-report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(assumptions, end='')
    print(copy_audit, end='')
    print(columns_audit, end='')
    print(public_output, end='')


if __name__ == '__main__':
    main()
