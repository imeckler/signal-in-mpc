#!/usr/bin/env python3
"""Candidate dead-metadata selection of actual Prost uint32 field encoding.

Every computational declaration remains identical. This exact graph requires
its own independent review before acceptance, separately from the earlier
varint graph. No Rust body or generated Lean body is edited.
"""
import copy
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent


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


def main():
    original = HERE / 'Artifacts/UInt32Field/signal_message.llbc'
    assert digest(original) == '81547c219ca760c0d2ba2902d1af5b21e6b727184978338ea7287d2cfc49de7e'
    before = json.loads(original.read_text())
    after = copy.deepcopy(before)
    tr = after['translated']
    changes = []

    def replace(path, value):
        target = after
        for key in path[:-1]:
            target = target[key]
        changes.append({'path': path, 'before': target[path[-1]], 'after': value})
        target[path[-1]] = value

    for slot, function, name in [(2, 246, 'forward_overflowing'), (6, 250, 'backward_overflowing')]:
        assert tr['trait_decls'][4]['methods'][slot]['skip_binder']['name'] == name
        assert tr['trait_impls'][4]['methods'][slot]['skip_binder']['id'] == function
        assert tr['fun_decls'][function]['body'] == 'Opaque'
        replace(['translated', 'trait_decls', 4, 'methods', slot], None)
        replace(['translated', 'trait_impls', 4, 'methods', slot], None)
        replace(['translated', 'fun_decls', function], None)
    for slot, name in [(0, 'remaining_mut'), (1, 'advance_mut'), (3, 'chunk_mut')]:
        assert tr['trait_decls'][0]['methods'][slot]['skip_binder']['name'] == name
        replace(['translated', 'trait_decls', 0, 'methods', slot], None)
    omitted_roots = [{'Fun': {'NonRec': i}} for i in (5, 246, 250)] + [{'Type': {'NonRec': 2}}]
    replace(['translated', 'ordered_decls'], [d for d in tr['ordered_decls'] if d not in omitted_roots])
    restored = copy.deepcopy(after)
    for change in reversed(changes):
        target = restored
        for key in change['path'][:-1]:
            target = target[key]
        target[change['path'][-1]] = change['before']
    assert restored == before
    computational = []
    for index, fun in enumerate(before['translated']['fun_decls']):
        if fun and fun['body'] != 'Opaque':
            computational.append(index)
            assert tr['fun_decls'][index] == fun
            for node in walk(fun['body']):
                if isinstance(node, dict):
                    assert node.get('Regular') not in (5, 246, 250)
                    assert node.get('TraitMethod') not in [[0, 0], [0, 1], [0, 3], [4, 2], [4, 6]]
                    call = node.get('Trait')
                    if isinstance(call, list) and len(call) == 2:
                        declaration = call[0]['Untagged']['trait_decl_ref']['skip_binder']['id']
                        assert (declaration, call[1]) not in [(0, 0), (0, 1), (0, 3), (4, 2), (4, 6)]
    assert computational == [0, 1, 2, 7, 48, 145, 256, 257, 286, 287]
    assert before['translated']['fun_decls'][5] == tr['fun_decls'][5]
    assert before['translated']['type_decls'][2] == tr['type_decls'][2]
    destination = HERE / 'Artifacts/UInt32Selected'
    destination.mkdir(parents=True, exist_ok=True)
    selected = destination / 'selected.llbc'
    selected.write_text(json.dumps(after, separators=(',', ':')) + '\n')
    changes_path = destination / 'changes.json'
    changes_path.write_text(json.dumps(changes, indent=2) + '\n')
    generated = HERE / 'Generated/UInt32Selected'
    generated.mkdir(parents=True, exist_ok=True)
    for old in generated.glob('*.lean'):
        old.unlink()
    command = [str(ROOT / '.deps/aeneas-2026-08-27/aeneas'), '-backend', 'lean', str(selected),
               '-dest', str(REFERENCE), '-subdir', '/SignalMessageWork/Generated/UInt32Selected',
               '-split-files', '-namespace', 'ProstUInt32', '-warnings-as-errors', '-no-progress-bar']
    with (destination / 'aeneas.log').open('w') as log:
        result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    report = {'candidate_only': True, 'accepted_reference': False, 'independent_review': 'pending',
              'original_sha256': digest(original), 'selected_sha256': digest(selected),
              'script_sha256': digest(Path(__file__)), 'changes_sha256': digest(changes_path),
              'reversible_changes': len(changes), 'unchanged_computational_declarations': computational,
              'unused_put_slice_and_uninit_declarations_retained': True,
              'additional_trusted_preprocessing': True, 'source_patches': [],
              'aeneas_exit_code': result.returncode,
              'aeneas_command': [x.replace(str(ROOT), '$WORKSPACE') for x in command],
              'generated_files': {str(p.relative_to(REFERENCE)): digest(p) for p in generated.glob('*.lean')},
              'remaining_external_templates': [p.name for p in generated.glob('*_Template.lean')]}
    (destination / 'review.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'UInt32 candidate: Aeneas exit {result.returncode}; templates {report["remaining_external_templates"]}')
    return result.returncode


if __name__ == '__main__':
    raise SystemExit(main())
