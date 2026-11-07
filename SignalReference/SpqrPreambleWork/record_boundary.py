#!/usr/bin/env python3
"""Freeze the actual single-route msg_preamble translator failure; no proof claim."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import tarfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    artifact = HERE / 'Artifacts/spqr'
    inventory_path = artifact / 'inventory.json'
    inventory = json.loads(inventory_path.read_text())
    pins_path = HERE.parent / 'pins.json'
    pins = json.loads(pins_path.read_text())
    assert inventory['entry_patterns'] == ['crate::msg_preamble']
    assert inventory['charon_exit_code'] == 0 and not inventory['has_errors']
    assert inventory['aeneas_exit_code'] == 2
    assert inventory['generated_files'] == {}
    assert inventory['source_patches'] == inventory['explicit_exclusions'] == inventory['explicit_opaque_patterns'] == []
    assert not inventory['hax_cfg_enabled']
    assert digest(HERE / 'extract.py') == inventory['script_sha256']
    llbc = artifact / 'spqr.llbc'
    assert digest(llbc) == inventory['llbc_sha256']
    for name, expected in inventory['source_sha256'].items():
        assert digest(ROOT / name) == expected, name
    text = re.sub(r'\x1b\[[0-9;]*m', '', (artifact / 'aeneas.log').read_text())
    assert 'There should be no bottoms in the value' in text
    assert "Could not translate the body of function 'spqr::msg_preamble" in text
    assert not list((HERE / 'Generated/spqr').glob('*.lean'))
    translated = json.loads(llbc.read_text())['translated']
    preamble = next(d for d in translated['fun_decls'] if d is not None and d['def_id'] == 0)
    source = ROOT / '.deps/libsignal-vendor/spqr/src/lib.rs'
    assert preamble['item_meta']['source_text'] in source.read_text()
    assert 'fn msg_preamble' in preamble['item_meta']['source_text']

    spqr = source.parent.parent
    archive = ROOT / '.deps/spqr-06959b4.tar.gz'
    assert digest(archive) == 'f8fd4b1356a678fa49bbf4c51801c38d3b53ea800178579bef9ff47321b2058f'
    upstream = []
    with tarfile.open(archive) as bundle:
        for member in bundle.getmembers():
            if member.isfile():
                prefix, name = member.name.split('/', 1)
                assert prefix == 'SparsePostQuantumRatchet-' + inventory['spqr_commit']
                path = spqr / name
                assert path.read_bytes() == bundle.extractfile(member).read(), name
                upstream.append(path)
    assert len(upstream) == 99
    assert set(p for p in spqr.rglob('*') if p.is_file()) - set(upstream) == {spqr / '.cargo-checksum.json'}
    binary_archive = ROOT / '.deps/aeneas-macos-aarch64-2026-08-27.tar.gz'
    assert digest(binary_archive) == pins['aeneas']['macos_aarch64_archive_sha256']
    aeneas = ROOT / '.deps/aeneas-2026-08-27/aeneas'
    with tarfile.open(binary_archive) as bundle:
        assert aeneas.read_bytes() == bundle.extractfile('aeneas').read()
    sources = [Path(__file__), HERE / 'extract.py', inventory_path, llbc, artifact / 'charon.log',
               artifact / 'aeneas.log', pins_path, archive, binary_archive, aeneas, *upstream,
               *[ROOT / name for name in inventory['source_sha256']]]
    report = {
        'recorded_at_utc': datetime.now(timezone.utc).isoformat(),
        'accepted_reference': False, 'status': 'blocked at unchanged accepted Aeneas translation',
        'entry': 'spqr::msg_preamble', 'spqr_commit': inventory['spqr_commit'],
        'versions': inventory['versions'],
        'source_sha256': {str(p.relative_to(ROOT)): digest(p) for p in sources},
        'source_location': 'spqr/src/lib.rs:563-590',
        'upstream_source': preamble['item_meta']['source_text'],
        'charon_exit_code': 0, 'charon_has_errors': False,
        'inventory_counts': inventory['counts'], 'body_kinds': inventory['body_kinds'],
        'aeneas_exit_code': 2, 'diagnostic': 'There should be no bottoms in the value',
        'failed_function': 'spqr::msg_preamble',
        'diagnostic_log_without_ansi': text,
        'root_cause_claim': 'The exact accepted-translator diagnostic is recorded; no more specific internal root cause is established.',
        'generated_lean_files': [], 'closed_translation': False,
        'extraction_routes_attempted': 1, 'llbc_preprocessing': [],
        'rust_source_changes': [], 'translator_changes': [], 'custom_standard_models': [],
        'custom_axioms': [], 'never_translator_repair_used': False,
        'aeneas_binary_matches_pinned_release_archive': True,
        'upstream_spqr_files_compared_byte_for_byte': len(upstream),
        'hax_configuration': 'Normal cfg(not(hax)); original sources unchanged.',
        'proof_status': 'No msg_preamble theorem or actual-Rust parser equivalence established.',
        'pending_boundary': 'A closed accepted translation of actual msg_preamble is required before composing the already accepted actual decode_varint proof into a whole-preamble reference theorem.',
        'source_semantics_observed_not_proved': [
            'Empty message returns version0, epoch0, index0 and empty remaining slice.',
            'Nonempty message takes version from byte0 and begins decoding epoch at offset1.',
            'Epoch decoder error or zero epoch returns MsgDecode.',
            'Second decoder error or failed u64-to-u32 conversion returns MsgDecode.',
            'Success returns version, epoch, index and original message suffix at final cursor.'
        ],
    }
    output = HERE / 'boundary-report.json'
    output.write_text(json.dumps(report, indent=2) + '\n')
    print('Recorded complete Charon extraction and actual accepted-Aeneas failure; no reference accepted.')
    print('boundary-report.json SHA256: ' + digest(output))


if __name__ == '__main__':
    main()
