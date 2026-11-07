#!/usr/bin/env python3
"""Select the actual to_u32s closure without its unsupported from_fn caller.

Charon cannot address closure methods directly as entry paths. This candidate
selection deletes only the unproved caller and its external array constructor;
all retained LLBC declarations remain identical. It is an explicit, trusted
extraction selection step, not a proof of array::from_fn or to_u32s.
"""

import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent
sys.path.insert(0, str(REFERENCE))
from extract import PINS, check_sources, digest, inventory
from MetadataWork.trim_step_metadata import reviewed_input_fingerprint, walk


def select(data):
    out = copy.deepcopy(data)
    tr = out['translated']
    changes = []
    expected = {0: ['sha2', 'sha256', 'soft', 'to_u32s'], 1: ['core', 'array', 'from_fn']}
    for index, name in expected.items():
        assert [part['Ident'][0] for part in tr['fun_decls'][index]['item_meta']['name']] == name
        changes.append({'path': ['translated', 'fun_decls', index],
                        'before': tr['fun_decls'][index], 'after': None})
        tr['fun_decls'][index] = None
    ordered = tr['ordered_decls']
    tr['ordered_decls'] = [entry for entry in ordered
                           if entry not in [{'Fun': {'NonRec': i}} for i in expected]]
    changes.append({'path': ['translated', 'ordered_decls'],
                    'before': ordered, 'after': tr['ordered_decls']})
    restored = copy.deepcopy(out)
    for change in changes:
        slot = restored
        for component in change['path'][:-1]:
            slot = slot[component]
        slot[change['path'][-1]] = change['before']
    assert restored == data
    semantic = {k: v for k, v in tr.items() if k not in ('item_names', 'short_names')}
    for node in walk(semantic):
        if isinstance(node, dict):
            assert not (type(node.get('Regular')) is int and node['Regular'] in expected)
            assert not (set(node) == {'Fun'} and type(node['Fun']) is int and node['Fun'] in expected)
    return out, changes


def main():
    check_sources()
    original = REFERENCE / 'Extraction/libsignal_sha256_to_words.llbc'
    before = json.loads(original.read_text())
    data, changes = select(before)
    artifact = HERE / 'selected.llbc'
    artifact.write_text(json.dumps(data, separators=(',', ':')) + '\n')
    aeneas = (REFERENCE / PINS['aeneas']['directory'] / 'aeneas').resolve()
    generated = HERE / 'Generated'
    generated.mkdir(exist_ok=True)
    for old in generated.glob('*.lean'):
        old.unlink()
    command = [str(aeneas), '-backend', 'lean', str(artifact), '-dest', str(REFERENCE),
               '-subdir', '/ShaWordsWork/Generated', '-split-files',
               '-namespace', 'RustCryptoSha256ToWords', '-warnings-as-errors', '-no-progress-bar']
    with (HERE / 'aeneas.log').open('w') as log:
        status = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    report = {'candidate_only': True, 'accepted_reference': False,
              'original_llbc': str(original.relative_to(REFERENCE)),
              'original_sha256': digest(original), 'input_fingerprint': reviewed_input_fingerprint(before),
              'selected_sha256': digest(artifact), 'changes': changes,
              'computational_bodies_modified': [], 'source_patches': [],
              'unproved_deleted_callers': ['sha2::sha256::soft::to_u32s', 'core::array::from_fn'],
              'selected_actual_operation': 'sha2::sha256::soft::to_u32s closure FnMut::call_mut',
              'selection_is_trusted_not_mechanized': True,
              'aeneas_exit_code': status.returncode,
              'generated_files': {str(p.relative_to(REFERENCE)): digest(p) for p in generated.glob('*.lean')},
              'inventory': inventory(artifact), 'script_sha256': digest(Path(__file__))}
    (HERE / 'review.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Selected real closure; Aeneas exit={status.returncode}; caller remains unproved.')
    return status.returncode


if __name__ == '__main__':
    raise SystemExit(main())
