#!/usr/bin/env python3
"""Independent exact-input review of the bounded generic Prost selection.

This checks a trusted selection boundary, not a mechanized compiler proof.
It does not discharge any concrete buffer implementation contract.
"""
import copy
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
WORK = HERE / 'ProstEncodingWork'


def sha(path):
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
    original_path = WORK / 'Artifacts/EncodeBody/prost_encoding.llbc'
    selected_path = WORK / 'Artifacts/EncodeSelected/selected.llbc'
    changes_path = WORK / 'Artifacts/EncodeSelected/changes.json'
    review_path = WORK / 'Artifacts/EncodeSelected/review.json'
    before = json.loads(original_path.read_text())
    after = json.loads(selected_path.read_text())
    changes = json.loads(changes_path.read_text())
    report = json.loads(review_path.read_text())
    assert sha(original_path) == '3c98f69e873c84399932d74cddc08e347ab35403e16470b14428b208dd2cf4cc'
    assert sha(selected_path) == '0a11308d2c265eef9460f62eb41b92ef7bcb52d225ff2ffcd45d8d5e67c235c4'
    assert sha(changes_path) == 'f1d4c6ef8196b69b94c0aaf7802e39849fb7183cc1cca4671a5d8cc739a6e247'
    expected_paths = [
        ['translated', 'trait_decls', 2, 'methods', 2],
        ['translated', 'trait_impls', 2, 'methods', 2],
        ['translated', 'fun_decls', 139],
        ['translated', 'trait_decls', 2, 'methods', 6],
        ['translated', 'trait_impls', 2, 'methods', 6],
        ['translated', 'fun_decls', 143],
        ['translated', 'ordered_decls'],
        ['translated', 'trait_decls', 0, 'methods', 0],
        ['translated', 'trait_decls', 0, 'methods', 1],
        ['translated', 'trait_decls', 0, 'methods', 3],
        ['translated', 'ordered_decls'],
    ]
    assert [c['path'] for c in changes] == expected_paths
    replay = copy.deepcopy(before)
    for change in changes:
        target = replay
        for key in change['path'][:-1]:
            target = target[key]
        assert target[change['path'][-1]] == change['before']
        target[change['path'][-1]] = change['after']
    assert replay == after
    restored = copy.deepcopy(after)
    for change in reversed(changes):
        target = restored
        for key in change['path'][:-1]:
            target = target[key]
        assert target[change['path'][-1]] == change['after']
        target[change['path'][-1]] = change['before']
    assert restored == before
    b, a = before['translated'], after['translated']
    computational = [i for i, fun in enumerate(b['fun_decls']) if fun and fun['body'] != 'Opaque']
    assert computational == [0, 7]
    assert all(b['fun_decls'][i] == a['fun_decls'][i] for i in computational)
    assert b['fun_decls'][139]['body'] == b['fun_decls'][143]['body'] == 'Opaque'
    assert b['fun_decls'][5] == a['fun_decls'][5]
    assert b['type_decls'][3] == a['type_decls'][3]
    for slot, name in [(0, 'remaining_mut'), (1, 'advance_mut'), (3, 'chunk_mut')]:
        assert b['trait_decls'][0]['methods'][slot]['skip_binder']['name'] == name
        assert a['trait_decls'][0]['methods'][slot] is None
    for slot, name in [(5, 'put_slice'), (7, 'put_u8')]:
        assert b['trait_decls'][0]['methods'][slot] == a['trait_decls'][0]['methods'][slot]
        assert a['trait_decls'][0]['methods'][slot]['skip_binder']['name'] == name
    # Check actual retained bodies against removed functions and dictionary slots.
    called_fields = set()
    for index in computational:
        for node in walk(a['fun_decls'][index]['body']):
            if not isinstance(node, dict):
                continue
            assert node.get('Regular') not in (5, 139, 143)
            assert node.get('TraitMethod') not in [[0, 0], [0, 1], [0, 3], [2, 2], [2, 6]]
            call = node.get('Trait')
            if isinstance(call, list) and len(call) == 2:
                declaration = call[0]['Untagged']['trait_decl_ref']['skip_binder']['id']
                assert (declaration, call[1]) not in [(0, 0), (0, 1), (0, 3), (2, 2), (2, 6)]
                if declaration == 0:
                    called_fields.add(call[1])
    assert called_fields == {5, 7}
    assert report['aeneas_exit_code'] == 0 and report['remaining_external_templates'] == []
    for filename, digest in report['generated_files'].items():
        assert sha(HERE / filename) == digest
    paths = [original_path, selected_path, changes_path, WORK / 'select_buffer.py',
             WORK / 'inspect_metadata.py', Path(__file__),
             ROOT / '.deps/libsignal-vendor/prost-0.14.4/src/encoding/varint.rs',
             ROOT / '.deps/libsignal-vendor/bytes-1.12.0/src/buf/buf_mut.rs',
             ROOT / '.deps/libsignal-v0.106.1/Cargo.lock']
    output = {
        'reviewer': '/root/signal_lean_aeneas',
        'author': '/root/signal_lean_aeneas/pkcs7_reference',
        'accepted_scope': 'Actual generic encode_varint and default put_u8 selected semantics only',
        'additional_trusted_preprocessing': True,
        'mechanized_selection_correctness': False,
        'full_original_bodies_unchanged': computational,
        'exact_reversible_changes': len(changes),
        'retained_called_buffer_fields': ['put_slice', 'put_u8'],
        'unused_opaque_default_put_slice_metadata_retained': True,
        'source_patches': [],
        'custom_crypto_or_buffer_models_added': [],
        'remaining_obligations': [
            'Prove the selected generic loop under its supplied BufMut operations.',
            'Discharge any successful-append contract for the actual concrete Vec implementation before claiming Vec equivalence.',
            'Compose actual Prost fields/derive-generated message encoding and SignalMessage::new before claiming whole-message reference equivalence.',
        ],
        'sha256': {str(p.relative_to(ROOT)): sha(p) for p in paths},
        'checks_passed': True,
    }
    target = HERE / 'prost-selection-independent-review.json'
    target.write_text(json.dumps(output, indent=2) + '\n')
    print('Passed: exact 11-change replay/reversal, both actual bodies, retained buffer calls, generated outputs.')


if __name__ == '__main__':
    main()
