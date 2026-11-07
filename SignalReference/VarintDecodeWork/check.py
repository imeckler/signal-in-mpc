#!/usr/bin/env python3
"""Reproduce pinned decoder translation; compile and audit its artifact bridges.

Does not grant independent acceptance or modify source/generated Lean files.
"""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tarfile
import tempfile

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    inventory_path = HERE / 'Artifacts/spqr/inventory.json'
    inventory = json.loads(inventory_path.read_text())
    pins_path = REFERENCE / 'pins.json'
    pins = json.loads(pins_path.read_text())
    assert inventory['charon_exit_code'] == inventory['aeneas_exit_code'] == 0
    assert not inventory['has_errors'] and inventory['counts']['ordered_decls'] == 24
    assert inventory['source_patches'] == [] and not inventory['hax_cfg_enabled']
    assert inventory['remaining_external_templates'] == []
    assert inventory['explicit_exclusions'] == inventory['explicit_opaque_patterns'] == []
    assert inventory['entry_patterns'] == ['crate::decode_varint']
    assert inventory['script_sha256'] == digest(HERE / 'extract.py')
    llbc = HERE / 'Artifacts/spqr/spqr.llbc'
    assert digest(llbc) == inventory['llbc_sha256'] == '7449749f2f675c2324b5ffcaa50200dac170c52974636bc662cb3ad8fbda4b76'
    for name, expected in inventory['source_sha256'].items():
        assert digest(ROOT / name) == expected, name
    for name, expected in inventory['generated_files'].items():
        assert digest(REFERENCE / name) == expected, name

    # Cargo records no git-source checksums here: compare all upstream files.
    spqr = ROOT / '.deps/libsignal-vendor/spqr'
    archive = ROOT / '.deps/spqr-06959b4.tar.gz'
    assert digest(archive) == 'f8fd4b1356a678fa49bbf4c51801c38d3b53ea800178579bef9ff47321b2058f'
    upstream_sources = []
    with tarfile.open(archive) as bundle:
        for member in bundle.getmembers():
            if member.isfile():
                prefix, name = member.name.split('/', 1)
                assert prefix == 'SparsePostQuantumRatchet-' + inventory['spqr_commit']
                path = spqr / name
                assert path.read_bytes() == bundle.extractfile(member).read(), name
                upstream_sources.append(path)
    assert len(upstream_sources) == 99
    assert set(p for p in spqr.rglob('*') if p.is_file()) - set(upstream_sources) == {spqr / '.cargo-checksum.json'}
    translated = json.loads(llbc.read_text())['translated']
    selected = [d for d in translated['fun_decls'] if d is not None and d['def_id'] == 0]
    assert len(selected) == 1
    assert selected[0]['item_meta']['source_text'] in (spqr / 'src/lib.rs').read_text()

    # Re-run the unchanged accepted translator on the unchanged original LLBC.
    aeneas = (REFERENCE / pins['aeneas']['directory'] / 'aeneas').resolve()
    binary_archive = ROOT / '.deps/aeneas-macos-aarch64-2026-08-27.tar.gz'
    assert digest(binary_archive) == pins['aeneas']['macos_aarch64_archive_sha256']
    with tarfile.open(binary_archive) as bundle:
        assert aeneas.read_bytes() == bundle.extractfile('aeneas').read()
    version = subprocess.check_output([str(aeneas), '-version'], text=True).strip()
    assert version == inventory['versions']['aeneas']
    assert pins['aeneas']['release'] in version
    with tempfile.TemporaryDirectory(prefix='spqr-decoder-') as temporary:
        command = [str(aeneas), '-backend', 'lean', str(llbc), '-dest', temporary,
                   '-subdir', '/VarintDecodeWork/Generated/spqr', '-split-files',
                   '-namespace', 'SpqrVarintDecode', '-warnings-as-errors', '-no-progress-bar']
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, check=True)
        generated = Path(temporary) / 'VarintDecodeWork/Generated/spqr'
        assert {p.name for p in generated.glob('*.lean')} == {'Types.lean', 'Funs.lean'}
        for path in generated.glob('*.lean'):
            assert path.read_bytes() == (HERE / 'Generated/spqr' / path.name).read_bytes(), path.name

    # Compare every standard-model source with the pinned upstream archive.
    model_archive = REFERENCE / 'ProstEncodingWork/AdvanceWork/TranslatorCandidate/aeneas-5b9dcf33.tar.gz'
    assert digest(model_archive) == 'ceb3a9a8114488f7deef705599316d1282133b4aea203cbf902117c11175d453'
    model_root = ROOT / '.deps/aeneas-2026-08-27'
    models = sorted((model_root / 'backends/lean/Aeneas/Std').rglob('*.lean'))
    with tarfile.open(model_archive) as bundle:
        members = {m.name.split('/', 1)[1]: m for m in bundle.getmembers() if '/' in m.name and m.isfile()}
        for path in models:
            assert path.read_bytes() == bundle.extractfile(members[str(path.relative_to(model_root))]).read(), path

    modules = ['Generated/spqr/Types', 'Generated/spqr/Funs', 'Reference', 'Bridge', 'OffsetReference', 'OffsetBridge']
    sources = {Path(__file__), HERE / 'extract.py', inventory_path, llbc, pins_path,
               HERE / 'Checks.lean', ROOT / '.deps/run-signal-lean.py', archive, model_archive, binary_archive, aeneas, *models,
               *upstream_sources, *[HERE / (m + '.lean') for m in modules],
               *[ROOT / name for name in inventory['source_sha256']]}
    root_modules = []
    def visit(module):
        if not module.startswith('TlsMpc'):
            return
        path = ROOT / (module.replace('.', '/') + '.lean')
        if path in sources:
            return
        sources.add(path)
        for imported in re.findall(r'^import ([A-Za-z0-9_.]+)', path.read_text(), re.M):
            visit(imported)
        root_modules.append(module.replace('.', '/'))
    visit('TlsMpc.Signal.SpqrDecodeAt')
    snapshot = {str(p.relative_to(ROOT)): digest(p) for p in sorted(sources)}
    cache = Path('/Users/izzy/repos/eco-theorem-combined/.lake/packages')
    build = HERE / 'Artifacts/Lean'
    paths = [build, model_root / 'backends/lean/.lake/build/lib/lean']
    paths += sorted(p / '.lake/build/lib/lean' for p in cache.iterdir() if (p / '.lake/build/lib/lean').is_dir())
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(str(p) for p in paths)
    for cwd, names in [(ROOT, root_modules), (REFERENCE, ['VarintDecodeWork/' + m for m in modules])]:
        for name in names:
            target = build / (name + '.olean')
            target.parent.mkdir(parents=True, exist_ok=True)
            subprocess.run(['lean', '-o', str(target), name + '.lean'], cwd=cwd, env=env, check=True)
    result = subprocess.run(['lean', 'VarintDecodeWork/Checks.lean'], cwd=REFERENCE, env=env,
                            text=True, capture_output=True, check=True)
    expected = re.findall(r'^#print axioms (\S+)', (HERE / 'Checks.lean').read_text(), re.M)
    found = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", result.stdout)
    assert [name for name, _ in found] == expected
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for name, axioms in found:
        assert not ({a.strip() for a in axioms.split(',') if a.strip()} - allowed), (name, axioms)
    assert snapshot == {str(p.relative_to(ROOT)): digest(p) for p in sorted(sources)}
    (HERE / 'axioms.txt').write_text(result.stdout)
    report = {
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'accepted_reference': False,
        'independent_review': 'Pending separate review and acceptance by parent agent.',
        'author': '/root/signal_astra_high/decoder_reference',
        'spqr_commit': inventory['spqr_commit'], 'versions': inventory['versions'],
        'source_sha256': snapshot, 'original_llbc_sha256': digest(llbc),
        'unchanged_original_llbc_translated': True,
        'aeneas_regeneration_byte_identical': True,
        'aeneas_binary_matches_pinned_release_archive': True,
        'llbc_preprocessing': [], 'rust_source_changes': [], 'custom_standard_models': [],
        'upstream_spqr_files_compared_byte_for_byte': len(upstream_sources),
        'all_standard_model_files_match_pinned_archive': len(models),
        'checked_endpoints': len(found), 'theorems': expected,
        'root_source_modules_recompiled_in_isolation': root_modules,
        'reference_modules_recompiled_in_isolation': modules,
        'allowed_foundational_axioms': sorted(allowed), 'custom_axioms': [],
        'axiom_report_sha256': digest(HERE / 'axioms.txt'),
        'scope': 'Actual pinned SPQR1.6.0 decode_varint at zero or arbitrary Usize offsets; exact result, error and cursor; prefix and shared-offset numeric AIG bridges.',
        'operation_domain': 'Every official Slice U8 and every Usize start, including starts at or past end; no success or canonicality assumption.',
        'artifact_domain': 'Shared bytes evaluate to the Slice; shared offset evaluates to eight-byte big-endian Usize. Every exported AIG output bit equals actual result encoding.',
        'prefix_numeric_artifact_theorem': 'LibSignalReference.Candidate.VarintDecode.decode_refines_artifact',
        'offset_numeric_artifact_theorem': 'LibSignalReference.Candidate.VarintDecode.decode_at_refines_artifact',
        'error_behavior': 'Actual MsgDecode for empty or unterminated available prefix (max10 bytes), original offset preserved; actual truncation of tenth-byte payload retained.',
        'hax_configuration': 'Normal cfg(not(hax)): invariant/decreases macros expand to unit; no hax assumption introduced.',
        'standard_model_boundary': 'Unchanged official scalar checked arithmetic, Slice reads, core min, and Result/loop models.',
        'full_spqr_message_parser_refined': False,
        'full_spqr_state_machine_refined': False,
        'native_mpc_executed_by_this_check': False,
    }
    (HERE / 'proof-report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Checked {len(found)} actual-SPQR decoder endpoints; unchanged translation; standard axioms only; independent acceptance pending.')


if __name__ == '__main__':
    main()
