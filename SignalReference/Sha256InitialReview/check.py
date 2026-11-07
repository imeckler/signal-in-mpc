#!/usr/bin/env python3
"""Independent, exact-input review of SHA constructor-only metadata selection."""
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tarfile
import tomllib

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent
WORK = REFERENCE / 'Sha256WrapperWork'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def walk(value, path=()):
    yield path, value
    if isinstance(value, dict):
        for key, child in value.items():
            yield from walk(child, (*path, key))
    elif isinstance(value, list):
        for key, child in enumerate(value):
            yield from walk(child, (*path, key))


def main():
    pins = {
        WORK / 'Artifacts/core_new_closed/sha_wrapper.llbc': '1cef7a79f3a78e97b72801e84ec0edb26219f0070654ed3b031574bf8033a534',
        WORK / 'InitialSelected/selected.llbc': 'd3e64beb5c6287f5f49c5d529471133b47662af08ec62bfbd0651187b442eb33',
        WORK / 'InitialSelected/changes.json': 'e3214701474474d9ebccad5e6e1939a91d5d0ce61546088d54deb300386edc77',
        WORK / 'select_initial.py': '689d0def9fe4ab43f8a111e2f36ab0ab247e47280981d043c38529e4f012d3f3',
        WORK / 'proof-report.json': 'eab147ae87a415c12fdb0a76da6cd5c8fbaa4f2bbab5984dcee89bdfa321a14d',
        ROOT / '.deps/aeneas-2026-08-27/aeneas': '323e2e1ce117cccf866c9e1fb9925671ec25312006f6d51da72ef95638612ed7',
        REFERENCE / 'ProstEncodingWork/AdvanceWork/TranslatorCandidate/aeneas-5b9dcf33.tar.gz':
            'ceb3a9a8114488f7deef705599316d1282133b4aea203cbf902117c11175d453',
    }
    for path, expected in pins.items():
        assert digest(path) == expected, path
    before = json.loads((WORK / 'Artifacts/core_new_closed/sha_wrapper.llbc').read_text())
    after = json.loads((WORK / 'InitialSelected/selected.llbc').read_text())
    changes = json.loads((WORK / 'InitialSelected/changes.json').read_text())
    selection = json.loads((WORK / 'InitialSelected/review.json').read_text())
    assert [c['path'] for c in changes] == [['translated', 'trait_impls', i] for i in (6, 9, 80)]
    assert all(c['after'] is None for c in changes)
    replay = copy.deepcopy(before)
    for c in changes:
        index = c['path'][-1]
        assert replay['translated']['trait_impls'][index] == c['before']
        replay['translated']['trait_impls'][index] = None
    assert replay == after
    restored = copy.deepcopy(after)
    for c in reversed(changes):
        restored['translated']['trait_impls'][c['path'][-1]] = c['before']
    assert restored == before
    b, a = before['translated'], after['translated']
    expected_roots = [{'Type': {'NonRec': i}} for i in (1, 2, 0)] + [
        {'Fun': {'NonRec': 161}}, {'Fun': {'NonRec': 17}}, {'Fun': {'NonRec': 16}},
        {'Global': {'NonRec': 2}}, {'Fun': {'NonRec': 15}}, {'Global': {'NonRec': 1}},
        {'Fun': {'NonRec': 0}}]
    assert b['ordered_decls'] == a['ordered_decls'] == expected_roots
    assert a['trait_decls'][8] is None
    for i in (6, 9, 80):
        impl = b['trait_impls'][i]
        assert impl['impl_trait']['id'] == 8 and impl['methods'] == [] and impl['consts'] == []
    functions, types, globals_ = {0, 15, 16, 17, 161}, {0, 1, 2}, {1, 2}
    calls, type_refs, global_refs = set(), set(), set()
    nodes = 0
    for kind, identifiers in (('fun_decls', functions), ('type_decls', types), ('global_decls', globals_)):
        for i in identifiers:
            assert a[kind][i] == b[kind][i]
            semantic = {k: v for k, v in a[kind][i].items() if k not in ('item_meta', 'src', 'layout', 'ptr_metadata')}
            for path, node in walk(semantic):
                nodes += 1
                if not isinstance(node, dict):
                    continue
                # No selected signature, constant, local type or body supplies
                # any dictionary, including any of the three removed impls.
                assert not any(k in node for k in ('HashConsedValue', 'Deduplicated', 'TraitMethod', 'TraitImpl', 'TraitRef'))
                if type(node.get('Regular')) is int:
                    calls.add(node['Regular'])
                if type(node.get('Adt')) is int:
                    type_refs.add(node['Adt'])
                if isinstance(node.get('Global'), dict):
                    global_refs.add(node['Global']['id'])
    assert calls == {15, 16, 17, 161} and type_refs == types and global_refs == globals_
    assert all('Structured' in a['fun_decls'][i]['body'] for i in functions)
    assert {a['global_decls'][i]['value']['Untagged'][0]['Call'][0]['kind']['Fun']['Regular']
            for i in globals_} == {15, 16}
    # Remaining references belong to non-emitted diagnostics. They are
    # explicitly retained and excluded from the accepted reference scope.
    excluded = []
    for path, node in walk(a):
        if not isinstance(node, dict) or not isinstance(node.get('TraitImpl'), dict):
            continue
        impl = node['TraitImpl']
        index = impl.get('id', impl.get('impl_ref', {}).get('id'))
        if index in (6, 9, 80):
            assert path[0] in ('fun_decls', 'trait_impls')
            assert path[0] != 'fun_decls' or path[1] not in functions
            excluded.append({'path': list(path + ('TraitImpl',)), 'removed_impl': index})
    assert excluded == selection['excluded_non_emitted_references_to_removed_metadata'] and len(excluded) == 11
    assert selection['aeneas_exit_code'] == 0 and selection['remaining_external_templates'] == []
    for filename, expected in selection['generated_files'].items():
        assert digest(REFERENCE / filename) == expected
    proof = json.loads((WORK / 'proof-report.json').read_text())
    for filename, expected in proof['source_sha256'].items():
        assert digest(ROOT / filename) == expected, filename
    lock = tomllib.loads((ROOT / '.deps/libsignal-v0.106.1/Cargo.lock').read_text())
    compared = {}
    for name, record in proof['registry_archives'].items():
        version = record['version']
        archive_path = ROOT / '.deps/libsignal-crates' / f'{name}-{version}.crate'
        package = next(p for p in lock['package'] if p['name'] == name and p['version'] == version)
        assert digest(archive_path) == record['sha256'] == package['checksum']
        directory = ROOT / '.deps/libsignal-vendor' / f'{name}-{version}'
        files = set()
        with tarfile.open(archive_path) as archive:
            for member in archive.getmembers():
                if member.isfile():
                    prefix, filename = member.name.split('/', 1)
                    assert prefix == f'{name}-{version}'
                    path = directory / filename
                    assert path.read_bytes() == archive.extractfile(member).read()
                    files.add(path)
        assert {p for p in directory.rglob('*') if p.is_file()} - files == {directory / '.cargo-checksum.json'}
        assert len(files) == record['upstream_files_compared_byte_for_byte']
        compared[name] = len(files)
    assert compared == {'sha2': 49, 'digest': 26, 'block-buffer': 12, 'crypto-common': 11, 'hybrid-array': 24}
    official = ROOT / '.deps/aeneas-2026-08-27'
    models = sorted((official / 'backends/lean/Aeneas/Std').rglob('*.lean'))
    with tarfile.open(REFERENCE / 'ProstEncodingWork/AdvanceWork/TranslatorCandidate/aeneas-5b9dcf33.tar.gz') as archive:
        members = {m.name.split('/', 1)[1]: m for m in archive.getmembers() if m.isfile() and '/' in m.name}
        for path in models:
            assert path.read_bytes() == archive.extractfile(members[str(path.relative_to(official))]).read()
    assert len(models) == 87
    cache = Path('/Users/izzy/repos/eco-theorem-combined/.lake/packages')
    paths = [REFERENCE / '.lake/build/lib/lean', ROOT / '.lake/build/lib/lean', official / 'backends/lean/.lake/build/lib/lean']
    paths += sorted(p / '.lake/build/lib/lean' for p in cache.iterdir() if (p / '.lake/build/lib/lean').is_dir())
    env = os.environ.copy(); env['LEAN_PATH'] = os.pathsep.join(str(p) for p in paths)
    checked = subprocess.run(['lean', 'Sha256WrapperWork/Checks.lean'], cwd=REFERENCE, env=env,
                             capture_output=True, text=True, check=True)
    expected = re.findall(r'^#print axioms (\S+)', (WORK / 'Checks.lean').read_text(), re.M)
    found = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", checked.stdout)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    assert [name for name, _ in found] == expected and len(found) == 8
    for name, axioms in found:
        assert not ({x.strip() for x in axioms.split(',') if x.strip()} - allowed), name
    for filename, expected in proof['source_sha256'].items():
        assert digest(ROOT / filename) == expected, filename
    result = {'independent_review': True, 'checks_passed': True, 'reviewer': '/root/signal_lean_aeneas',
              'author': '/root/signal_lean_aeneas/pkcs7_reference',
              'scope': 'Actual SHA core constructor/constants/empty drop; composition with separately accepted compact compression.',
              'reversible_metadata_changes': 3, 'ordered_roots_unchanged': 10,
              'selected_computational_declarations_unchanged': sorted(functions),
              'selected_type_declarations_unchanged': sorted(types), 'selected_globals_unchanged': sorted(globals_),
              'selected_semantic_nodes_scanned': nodes, 'selected_callgraph_closed': True,
              'non_emitted_removed_metadata_references': excluded,
              'whole_llbc_graph_claimed_closed': False, 'registry_archive_files_compared': compared,
              'official_standard_model_files_compared': len(models), 'fresh_kernel_axiom_endpoints': len(found),
              'allowed_foundational_axioms': sorted(allowed), 'custom_models_or_crypto_axioms': [],
              'additional_trusted_preprocessing': True, 'selection_correctness_mechanized': False,
              'full_digest_update_finalize_equivalence': False,
              'source_sha256': {str(p.relative_to(ROOT)): digest(p) for p in [*pins, WORK / 'InitialSelected/review.json', Path(__file__)]}}
    (HERE / 'review.json').write_text(json.dumps(result, indent=2) + '\n')
    print('Independent SHA initializer review passed: 3 metadata deletions, 5 unchanged selected bodies, 8 standard-axiom endpoints.')


if __name__ == '__main__':
    main()
