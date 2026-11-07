#!/usr/bin/env python3
"""Isolated candidate: drop unused new Step dictionary fields.

The August Aeneas model predates Rust's forward/backward_overflowing fields.
This script never changes a computational body. It only drops those two opaque
declarations and their dictionary slots, after checking no structured body
references them. The remaining dictionary operations use the pinned existing
Aeneas standard-library model. This extra extraction step is not mechanized
and does not automatically produce an accepted reference.
"""

import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent
REVIEWED_INPUT_SHA256 = '5491dec2d5420ab993363eec31c8097d28bf4a61420c2ffd3a371d6de0e128eb'
REVIEWED_INPUT_FINGERPRINT = '3514ab7abd8a8e37ce5abc87d1a172e6c9f782f29443d797c1708bf14cf11aac'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def walk(value):
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def reviewed_input_fingerprint(data):
    # Charon emits this diagnostic map in nondeterministic order. Its entries,
    # all semantic declarations and every other JSON value remain pinned.
    ordered = copy.deepcopy(data)
    ordered['translated']['short_names'].sort(key=lambda entry: json.dumps(entry['key'], sort_keys=True))
    return hashlib.sha256(json.dumps(ordered, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def normalize_data(before):
    if reviewed_input_fingerprint(before) != REVIEWED_INPUT_FINGERPRINT:
        raise ValueError('LLBC input differs from the independently reviewed graph')
    after = copy.deepcopy(before)
    tr = after['translated']
    trait_id, impl_id = 1, 2
    removed = {2: (96, 'forward_overflowing'), 6: (100, 'backward_overflowing')}
    changes = []
    for field, (function, name) in removed.items():
        method = tr['trait_decls'][trait_id]['methods'][field]
        assert method['skip_binder']['name'] == name
        assert tr['trait_impls'][impl_id]['methods'][field]['skip_binder']['id'] == function
        assert tr['fun_decls'][function]['body'] == 'Opaque'
        for kind, index in [('trait_decls', trait_id), ('trait_impls', impl_id)]:
            path = ['translated', kind, index, 'methods', field]
            changes.append({'path': path, 'before': copy.deepcopy(tr[kind][index]['methods'][field]), 'after': None})
            tr[kind][index]['methods'][field] = None
        changes.append({'path': ['translated', 'fun_decls', function],
                        'before': copy.deepcopy(tr['fun_decls'][function]), 'after': None})
        tr['fun_decls'][function] = None
    ordered = tr['ordered_decls']
    tr['ordered_decls'] = [x for x in ordered if x not in
                           [{'Fun': {'NonRec': 96}}, {'Fun': {'NonRec': 100}}]]
    changes.append({'path': ['translated', 'ordered_decls'],
                    'before': ordered, 'after': tr['ordered_decls']})
    restored = copy.deepcopy(after)
    for change in changes:
        slot = restored
        for component in change['path'][:-1]:
            slot = slot[component]
        slot[change['path'][-1]] = change['before']
    assert restored == before
    # Include globals, trait dictionaries, constants and function pointers. Only
    # diagnostic name maps are excluded; they retain harmless labels for removed
    # declarations. Reject any semantic reference to a removed function/field.
    semantic = {k: v for k, v in tr.items() if k not in ('item_names', 'short_names')}
    for node in walk(semantic):
        if isinstance(node, dict):
            assert node.get('Fun') not in [{'Regular': 96}, {'Regular': 100}]
            assert node.get('Regular') not in (96, 100)
            assert node.get('TraitMethod') not in [[1, 2], [1, 6]]
            if isinstance(node.get('skip_binder'), dict):
                assert node['skip_binder'].get('id') not in (96, 100)
    definitions, references = set(), set()
    for node in walk(after):
        if isinstance(node, dict):
            if 'HashConsedValue' in node:
                definitions.add(node['HashConsedValue'][0])
            if 'Deduplicated' in node:
                references.add(node['Deduplicated'])
    assert references <= definitions, references - definitions
    return after, changes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--canonical', action='store_true')
    canonical = parser.parse_args().canonical
    sys.path.insert(0, str(REFERENCE))
    from extract import PINS, check_sources, inventory
    check_sources()
    original = REFERENCE / 'Extraction/libsignal_sha256_compact.llbc'
    before = json.loads(original.read_text())
    after, changes = normalize_data(before)
    destination = REFERENCE / 'Extraction/sha256-compact-metadata' if canonical else HERE / 'Artifacts/ShaCompactStep'
    destination.mkdir(parents=True, exist_ok=True)
    normalized = REFERENCE / 'Extraction/libsignal_sha256_compact_reviewed.llbc' if canonical else destination / 'normalized.llbc'
    normalized.write_text(json.dumps(after, separators=(',', ':')))
    subdir = '/LibSignalReference/Generated/Sha256Compact' if canonical else '/MetadataWork/Generated/ShaCompactStep'
    generated = REFERENCE / subdir.lstrip('/')
    for previous in generated.glob('*.lean'):
        previous.unlink()
    command = [str(ROOT / '.deps/aeneas-2026-08-27/aeneas'), '-backend', 'lean', str(normalized),
               '-dest', str(REFERENCE), '-subdir', subdir,
               '-split-files', '-namespace', 'RustCryptoSha256Compact' if canonical else 'CandidateShaStep', '-warnings-as-errors', '-no-progress-bar']
    version = subprocess.check_output([command[0], '-version'], text=True).strip()
    if PINS['aeneas']['release'] not in version:
        raise ValueError('Aeneas binary differs from pinned release')
    with (destination / 'aeneas.log').open('w') as output:
        result = subprocess.run(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
    report = {'accepted_reference': False, 'canonical_reference_output': canonical, 'additional_trusted_step': True,
              'transformation_correctness_mechanized': False,
              'original_llbc_sha256': digest(original), 'normalized_llbc_sha256': digest(normalized),
              'changes': changes, 'all_other_json_values_identical': True,
              'all_structured_bodies_identical': True,
              'removed_functions_are_opaque_and_unreferenced_in_retained_semantic_graph': True,
              'reviewed_input_sha256': REVIEWED_INPUT_SHA256,
              'reviewed_input_fingerprint': REVIEWED_INPUT_FINGERPRINT,
              'fingerprint_normalization': 'Sort only diagnostic short_names by key before JSON serialization; no input or output LLBC field is reordered by this validation.',
              'independent_review': 'Parent helper inspected exact diff, all retained semantic JSON including globals/function pointers, and official Aeneas range model; no dependency on removed fields found.',
              'no_dangling_hashcons_references': True,
              'rust_source_changes': [], 'aeneas_exit_code': result.returncode,
              'command': [x.replace(str(ROOT), '$WORKSPACE') for x in command],
              'generated_files': {str(p.relative_to(REFERENCE)): digest(p)
                                  for p in sorted(generated.glob('*.lean'))},
              'remaining_external_templates': [p.name for p in generated.glob('*_Template.lean')],
              'script_sha256': digest(Path(__file__))}
    (destination / 'review.json').write_text(json.dumps(report, indent=2) + '\n')
    if canonical:
        audit = inventory(normalized)
        source = json.loads((REFERENCE / 'Extraction/sha256_compact.json').read_text())
        audit.update({key: source[key] for key in ('charon_command', 'charon_exit_code', 'rustflags', 'target')})
        audit.update({'source_profile': 'sha256_compact', 'source_llbc_sha256': digest(original),
                      'aeneas_exit_code': result.returncode, 'generated_files': report['generated_files'],
                      'trusted_preprocessing_review': str((destination / 'review.json').relative_to(REFERENCE)),
                      'trusted_preprocessing_review_sha256': digest(destination / 'review.json'),
                      'trusted_preprocessing_source_sha256': digest(Path(__file__)),
                      'aeneas_command': report['command']})
        (REFERENCE / 'Extraction/sha256_compact_reviewed.json').write_text(json.dumps(audit, indent=2) + '\n')
    if result.returncode or report['remaining_external_templates']:
        raise RuntimeError('Aeneas translation is incomplete')
    print(json.dumps({'aeneas_exit_code': result.returncode,
                      'external_templates': report['remaining_external_templates']}))


if __name__ == '__main__':
    main()
