#!/usr/bin/env python3
"""Candidate metadata compatibility probe; never an accepted AES reference."""

import copy
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent
sys.path.insert(0, str(REFERENCE))
from extract import PINS, check_sources, digest, inventory, name_of
from MetadataWork.trim_step_metadata import walk, reviewed_input_fingerprint

REVIEWED_INPUT_FINGERPRINT = 'cf346ded47a8a8f46d79b330878e47a424e1d4e3e8d877fade35896732c3c457'


def select(before):
    if reviewed_input_fingerprint(before) != REVIEWED_INPUT_FINGERPRINT:
        raise ValueError('key-schedule graph differs from the independently reviewed input')
    data = copy.deepcopy(before)
    tr = data['translated']
    changes = []
    def remove(path):
        value = data
        for key in path[:-1]:
            value = value[key]
        changes.append({'path': path, 'before': value[path[-1]], 'after': None})
        value[path[-1]] = None
    assert name_of(tr['trait_decls'][3]['item_meta']) == 'core::iter::traits::iterator::Iterator'
    assert name_of(tr['trait_decls'][4]['item_meta']) == 'core::iter::range::Step'
    assert tr['trait_decls'][3]['methods'][54]['skip_binder']['name'] == 'rev'
    assert name_of(tr['fun_decls'][40]['item_meta']) == 'core::iter::traits::iterator::Iterator::rev'
    remove(['translated', 'trait_decls', 3, 'methods', 54])
    for impl, impl_name in ((7, 'core::iter::range::{impl}'),
                            (10, 'core::iter::adapters::step_by::{impl}'),
                            (12, 'core::iter::adapters::rev::{impl}'),
                            (20, 'core::slice::iter::{impl}')):
        assert name_of(tr['trait_impls'][impl]['item_meta']) == impl_name
        assert tr['trait_impls'][impl]['methods'][54]['skip_binder']['id'] == 40
        assert tr['trait_impls'][impl]['methods'][54]['kind'] == {'TraitMethod': [3, 54]}
        remove(['translated', 'trait_impls', impl, 'methods', 54])
    for field, function in ((2, 132), (6, 136)):
        assert tr['fun_decls'][function]['body'] == 'Opaque'
        assert tr['trait_decls'][4]['methods'][field]['skip_binder']['name'] == (
            'forward_overflowing' if field == 2 else 'backward_overflowing')
        assert tr['trait_impls'][8]['methods'][field]['skip_binder']['id'] == function
        remove(['translated', 'trait_decls', 4, 'methods', field])
        remove(['translated', 'trait_impls', 8, 'methods', field])
        remove(['translated', 'fun_decls', function])
    old = tr['ordered_decls']
    tr['ordered_decls'] = [x for x in old if x not in [{'Fun': {'NonRec': i}} for i in (132, 136)]]
    changes.append({'path': ['translated', 'ordered_decls'], 'before': old, 'after': tr['ordered_decls']})
    restored = copy.deepcopy(data)
    for change in changes:
        slot = restored
        for component in change['path'][:-1]:
            slot = slot[component]
        slot[change['path'][-1]] = change['before']
    assert restored == before
    semantic = {k: v for k, v in tr.items() if k not in ('item_names', 'short_names')}
    removed_slots = ([3, 54], [4, 2], [4, 6])
    for node in walk(semantic):
        if isinstance(node, dict):
            assert node.get('Regular') not in (132, 136)
            assert node.get('TraitMethod') not in removed_slots
            if isinstance(node.get('skip_binder'), dict):
                assert node['skip_binder'].get('id') not in (132, 136)
            default = node.get('TraitDefault')
            if isinstance(default, dict) and [default['trait_ref']['id'], default['item_id']] in removed_slots:
                assert node is tr['fun_decls'][40]['src']
                assert default['trait_ref']['id'] == 3 and default['item_id'] == 54
    # A reference to the retained default method is required, not erased.
    assert any(isinstance(node, dict) and node.get('Regular') == 40
               for node in walk(tr['fun_decls'][4]['body']))
    return data, changes


def main():
    check_sources()
    original = REFERENCE / 'Extraction/libsignal_aes256_key_schedule.llbc'
    before = json.loads(original.read_text())
    data, changes = select(before)
    selected = HERE / 'selected.llbc'
    selected.write_text(json.dumps(data, separators=(',', ':')) + '\n')
    aeneas = (REFERENCE / PINS['aeneas']['directory'] / 'aeneas').resolve()
    generated = HERE / 'Generated'
    generated.mkdir(exist_ok=True)
    for path in generated.glob('*.lean'):
        path.unlink()
    command = [str(aeneas), '-backend', 'lean', str(selected), '-dest', str(REFERENCE),
               '-subdir', '/AesKeyScheduleWork/Generated', '-split-files',
               '-namespace', 'RustCryptoAesKeySchedule', '-warnings-as-errors', '-no-progress-bar']
    with (HERE / 'aeneas.log').open('w') as log:
        status = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    report = {'candidate_only': True, 'accepted_reference': False,
              'original_llbc': str(original.relative_to(REFERENCE)), 'original_sha256': digest(original),
              'selected_sha256': digest(selected), 'changes': changes,
              'input_fingerprint': REVIEWED_INPUT_FINGERPRINT,
              'independent_review': 'AesInverseLayoutWork/key-schedule-metadata-review.json',
              'computational_bodies_modified': [], 'source_patches': [],
              'rev_function_40_retained': data['translated']['fun_decls'][40] == before['translated']['fun_decls'][40],
              'trait_default_provenance_retained': True, 'aeneas_exit_code': status.returncode,
              'generated_files': {str(p.relative_to(REFERENCE)): digest(p) for p in generated.glob('*.lean')},
              'inventory': inventory(selected), 'script_sha256': digest(Path(__file__))}
    (HERE / 'review.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Candidate metadata probe exit={status.returncode}; no accepted AES key schedule reference.')
    return status.returncode


if __name__ == '__main__':
    raise SystemExit(main())
