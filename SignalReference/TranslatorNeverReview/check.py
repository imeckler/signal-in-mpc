#!/usr/bin/env python3
"""Independent review of the isolated Never-continuation translator candidate.

No author artifact is edited. This is a reproducible trusted review, not a
mechanized proof of the OCaml translator or closed-declaration selection.
"""
from datetime import datetime, timezone
import copy
import difflib
import hashlib
import json
from pathlib import Path
import re
import tarfile

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent
WORK = REFERENCE / 'ProstEncodingWork/AdvanceWork/TranslatorCandidate'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def walk(value, path=()):
    yield path, value
    if isinstance(value, dict):
        for key, child in value.items():
            yield from walk(child, (*path, key))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from walk(child, (*path, index))


def main():
    patch_report = json.loads((WORK / 'candidate-patch.json').read_text())
    manifest = json.loads((WORK / 'original-source-manifest.json').read_text())
    assert manifest['aeneas_commit'] == '5b9dcf33dccdb1560ea7203ac57ea202476b6ed3'
    assert manifest['charon_commit'] == '4ad295c1bf982b5533ce7d85f4ddc889ff3127f8'
    archive = WORK / 'aeneas-5b9dcf33.tar.gz'
    assert digest(archive) == manifest['archive_sha256']
    source = WORK / ('aeneas-' + manifest['aeneas_commit'])
    changed = []
    original_bytes = {}
    with tarfile.open(archive) as tar:
        for member in tar.getmembers():
            if not member.isfile():
                continue
            relative = member.name.split('/', 1)[1]
            contents = tar.extractfile(member).read()
            original_bytes[relative] = contents
            assert hashlib.sha256(contents).hexdigest() == manifest['source_sha256'][relative]
            if (source / relative).read_bytes() != contents:
                changed.append(relative)
    assert set(original_bytes) == set(manifest['source_sha256'])
    assert changed == ['src/interp/InterpStatements.ml']
    before = original_bytes[changed[0]].decode()
    after = (source / changed[0]).read_text()
    assert hashlib.sha256(before.encode()).hexdigest() == patch_report['before_sha256']
    assert hashlib.sha256(after.encode()).hexdigest() == patch_report['after_sha256']
    actual_patch = ''.join(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
                                               fromfile='a/' + changed[0], tofile='b/' + changed[0]))
    patch_file = WORK / 'never-continuation.patch'
    assert actual_patch == patch_file.read_text()
    assert digest(patch_file) == patch_report['patch_sha256']
    # Removing comments leaves exactly one semantic change: select the result
    # by the fully instantiated output type and retain the original cc.
    strip_comments = lambda s: re.sub(r'\(\*.*?\*\)', '', s, flags=re.S)
    old_code, new_code = strip_comments(before), strip_comments(after)
    old_line = '  ([ (ctx, Unit) ], cc_singleton __FILE__ __LINE__ span cc)'
    new_line = ('  let result = if inst_sg.output = TNever then Panic else Unit in\n'
                '  ([ (ctx, result) ], cc_singleton __FILE__ __LINE__ span cc)')
    start = old_code.index('and eval_function_call_symbolic_from_inst_sig')
    end = old_code.index('and eval_function_body', start)
    region = old_code[start:end]
    assert region.count(old_line) == 1
    assert old_code[:start] + region.replace(old_line, new_line) + old_code[end:] == new_code

    original = WORK.parent / 'Artifacts/SliceImplsClosed/slice_advance.llbc'
    selected = WORK / 'SliceSelected/slice.llbc'
    selection = json.loads((WORK / 'SliceSelected/review.json').read_text())
    assert digest(original) == 'c13e133c1a838b4ebbfc88e1f6026b41f4df8f21ed2eaa9f573f3d319e3ddd63'
    assert digest(selected) == '80191557e1046652abcf940360244f50901404b1699db1d2af0ee2f92cdd840b'
    original_json, selected_json = (json.loads(p.read_text()) for p in (original, selected))
    changes_file = WORK / 'SliceSelected/changes.json'
    changes = json.loads(changes_file.read_text())
    assert len(changes) == 1 and changes[0]['path'] == ['translated', 'ordered_decls']
    replay = copy.deepcopy(original_json)
    assert replay['translated']['ordered_decls'] == changes[0]['before']
    replay['translated']['ordered_decls'] = changes[0]['after']
    assert replay == selected_json
    replay['translated']['ordered_decls'] = changes[0]['before']
    assert replay == original_json
    tr = selected_json['translated']
    removed_functions = {0, 1, 3, 4, 5, 6, 7, 8}
    removed_types = {4, 5, 6, 10, 11, 12}
    removed_roots = ([{'Fun': {'NonRec': i}} for i in sorted(removed_functions)] +
                     [{'Type': {'NonRec': i}} for i in sorted(removed_types)] +
                     [{'TraitDecl': {'NonRec': 0}}])
    assert tr['ordered_decls'] == [r for r in changes[0]['before'] if r not in removed_roots]
    for kind in ('fun_decls', 'type_decls', 'trait_decls', 'trait_impls', 'global_decls'):
        assert tr[kind] == original_json['translated'][kind]
    for index in removed_functions:
        assert tr['fun_decls'][index]['body'] == 'Opaque'
    computational = [i for i, f in enumerate(tr['fun_decls']) if f and f['body'] != 'Opaque']
    assert computational == [2, 264]
    calls, semantic_nodes = set(), 0
    # Scan full selected computational signatures, parameters, locals and bodies.
    # Owner-name metadata may mention the omitted Buf trait; that is not a call.
    for index in computational:
        declaration = tr['fun_decls'][index]
        for key in ('signature', 'item_binder', 'body'):
            if key not in declaration:
                continue
            for path, node in walk(declaration[key], (index, key)):
                semantic_nodes += 1
                if not isinstance(node, dict):
                    continue
                regular = node.get('Regular')
                if isinstance(regular, int):
                    assert regular not in removed_functions, path
                    calls.add(regular)
                adt = node.get('Adt')
                if isinstance(adt, int):
                    assert adt not in removed_types, path
                trait = node.get('Trait')
                if isinstance(trait, list) and len(trait) == 2:
                    ref = trait[0].get('Untagged', {}).get('trait_decl_ref', {}).get('skip_binder', {})
                    assert ref.get('id') != 0, path
    assert calls == {262, 263, 264, 290, 291}

    baseline = json.loads((WORK / 'baseline-comparison.json').read_text())
    candidate = json.loads((WORK / 'candidate-comparison.json').read_text())
    assert digest(WORK / 'Bin/candidate') == candidate['binary_sha256']
    assert digest(ROOT / '.deps/aeneas-2026-08-27/aeneas') == candidate['accepted_binary_sha256']
    generated_files = []
    for name in ('Regressions', 'Slice', 'Varint', 'UInt32'):
        b, c = baseline['targets'][name], candidate['targets'][name]
        assert b['llbc_sha256'] == c['llbc_sha256']
        assert c['exit_code'] == 0 and c['external_templates'] == []
        assert b['exit_code'] == (2 if name in ('Regressions', 'Slice') else 0)
        for filename, expected in c['generated_sha256'].items():
            path = WORK / 'Generated/Candidate' / name / filename
            assert digest(path) == expected
            generated_files.append(path)
            assert not re.search(r'\b(axiom|sorry|admit|native_decide)\b', path.read_text())
            if name in ('Varint', 'UInt32'):
                baseline_path = WORK / 'Generated/Baseline' / name / filename
                assert digest(baseline_path) == b['generated_sha256'][filename]
                normalize = lambda text: text.replace('.Generated.Baseline.', '.Generated.REVIEW.') \
                                             .replace('.Generated.Candidate.', '.Generated.REVIEW.')
                assert normalize(path.read_text()) == normalize(baseline_path.read_text())
    slice_text = (WORK / 'Generated/Candidate/Slice/Funs.lean').read_text()
    assert 'let _ ← panic_advance { requested := cnt, available := i1 }\n    fail panic' in slice_text
    assert '(core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) self\n      { start := cnt }' in slice_text
    generic_text = (WORK / 'Generated/Candidate/Regressions/Funs.lean').read_text()
    assert generic_text.count('let _ ← StopsInst.stop value') == 2
    assert 'if proceed\n  then ok 7#u8' in generic_text
    assert 'let _ ← panic_stop\n  fail panic' in generic_text

    files = [Path(__file__), archive, source / changed[0], patch_file,
             WORK / 'candidate-patch.json', WORK / 'original-source-manifest.json',
             WORK / 'candidate-comparison.json', WORK / 'baseline-comparison.json',
             WORK / 'select_slice.py', WORK / 'SliceSelected/review.json', changes_file,
             original, selected, WORK / 'NeverContinuation.lean',
             WORK / 'RegressionRust/src/lib.rs', WORK / 'Regressions/calls.llbc',
             *generated_files]
    report = {
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'independent_review': True, 'reviewer': '/root/signal_lean_aeneas',
        'author': '/root/signal_lean_aeneas/pkcs7_reference', 'checks_passed': True,
        'review_scope': 'Exact one-file Never continuation patch, actual slice root-only selection, unchanged existing extraction regression output, retained fail/div calls.',
        'source_files_checked_against_exact_pin_archive': len(original_bytes),
        'changed_source_files': changed,
        'semantic_code_change': 'If instantiated return type is TNever, synthesize an unreachable panic continuation after retaining the original symbolic function call; other calls retain Unit.',
        'source_rust_edits': [], 'standard_model_edits': [], 'generated_lean_edits': [],
        'selected_actual_functions': ['bytes::Buf for &[u8]::advance', 'bytes::panic_advance'],
        'all_slice_declarations_identical': True,
        'reversible_root_selection_changes': 1,
        'slice_computational_semantic_nodes_scanned': semantic_nodes,
        'slice_actual_direct_call_ids': sorted(calls),
        'unchanged_regression_targets': ['Prost varint', 'Prost uint32 fields'],
        'trusted_preprocessing_and_translator_review': True,
        'mechanized_translator_or_selection_correctness': False,
        'accepted_toolchain_replaced': False,
        'full_byte_field_or_signalmessage_refinement': False,
        'required_before_selected_profile_acceptance': ['Candidate kernel proof audit and complete exact provenance report; parent integration decision'],
        'sha256': {str(p.relative_to(ROOT)): digest(p) for p in files},
    }
    (HERE / 'review.json').write_text(json.dumps(report, indent=2) + '\n')
    print('Independent Never candidate review passed: exact one-file patch, root-only selection, retained calls and unchanged successful extraction regressions.')


if __name__ == '__main__':
    main()
