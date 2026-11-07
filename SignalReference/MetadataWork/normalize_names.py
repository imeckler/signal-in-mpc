#!/usr/bin/env python3
"""Candidate workaround for Aeneas's monomorphized-type naming crash.

Only declaration names change. Rust-derived bodies, type definitions, IDs,
signatures, constants and control flow are byte-for-byte equal as JSON values.
This is an additional trusted extraction step, not a proved transformation.
No output from this script is automatically accepted as a reference.
"""

import copy
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('profile', nargs='?', default='sha256_compact_full_mir_mono',
                        choices=['sha256_compact_full_mir_mono', 'sha256_compact_full_mir_complete'])
    profile = parser.parse_args().profile
    tag = 'ShaCompactComplete' if profile.endswith('_complete') else 'ShaCompactNames'
    original = REFERENCE / 'Extraction' / ('libsignal_' + profile + '.llbc')
    before = json.loads(original.read_text())
    after = copy.deepcopy(before)
    changes = []
    for declaration in after['translated']['type_decls']:
        if declaration is None:
            continue
        name = declaration['item_meta']['name']
        if name and 'Instantiated' in name[-1]:
            previous = copy.deepcopy(name)
            if len(name) < 2 or 'Ident' not in name[-2]:
                raise ValueError('unexpected instantiated declaration-name shape')
            base, disambiguator = name[-2]['Ident']
            normalized_name = name[:-2] + [{'Ident': [f'{base}MpcInstantiation{declaration["def_id"]}', disambiguator]}]
            declaration['item_meta']['name'] = normalized_name
            changes.append({'type_id': declaration['def_id'], 'before': previous, 'after': normalized_name})
    restored = copy.deepcopy(after)
    for change in changes:
        restored['translated']['type_decls'][change['type_id']]['item_meta']['name'] = change['before']
    if restored != before:
        raise AssertionError('normalization changed more than reviewed declaration-name slots')
    destination = HERE / 'Artifacts' / tag
    destination.mkdir(parents=True, exist_ok=True)
    normalized = destination / 'normalized.llbc'
    normalized.write_text(json.dumps(after, separators=(',', ':')))
    aeneas = ROOT / '.deps/aeneas-2026-08-27/aeneas'
    generated = HERE / 'Generated' / tag
    for previous in generated.glob('*.lean'):
        previous.unlink()
    command = [str(aeneas), '-backend', 'lean', str(normalized), '-dest', str(REFERENCE),
               '-subdir', '/MetadataWork/Generated/' + tag, '-split-files',
               '-namespace', 'CandidateShaMetadata', '-warnings-as-errors', '-no-progress-bar']
    with (destination / 'aeneas.log').open('w') as output:
        result = subprocess.run(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
    report = {'accepted_reference': False, 'additional_trusted_step': True,
              'transformation_correctness_mechanized': False,
              'original_llbc_sha256': digest(original), 'normalized_llbc_sha256': digest(normalized),
              'changes': changes, 'all_other_json_values_identical': True,
              'rust_source_changes': [], 'aeneas_exit_code': result.returncode,
              'command': [x.replace(str(ROOT), '$WORKSPACE') for x in command],
              'generated_files': {str(p.relative_to(REFERENCE)): digest(p)
                                  for p in sorted(generated.glob('*.lean'))},
              'remaining_external_templates': [p.name for p in generated.glob('*_Template.lean')],
              'script_sha256': digest(Path(__file__))}
    (destination / 'review.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'renamed_types': len(changes), 'aeneas_exit_code': result.returncode,
                      'external_templates': report['remaining_external_templates']}))


if __name__ == '__main__':
    main()
