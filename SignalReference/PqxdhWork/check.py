#!/usr/bin/env python3
"""Compile/audit PQXDH KDF circuit and compare complete outputs with Python HMAC.

Fixtures are mathematical HKDF checks, not actual Rust/KEM equivalence evidence.
"""
from datetime import datetime, timezone
import hashlib
import hmac
import json
from pathlib import Path
import re
import subprocess
import tarfile
import tomllib

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
LABEL = b'WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def oracle(parts):
    secret = b'\xff' * 32 + b''.join(parts)
    prk = hmac.digest(bytes(32), secret, 'sha256')
    previous = b''
    output = b''
    for counter in range(1, 4):
        previous = hmac.digest(prk, previous + LABEL + bytes([counter]), 'sha256')
        output += previous
    return output


def main():
    pins_path = HERE.parent / 'pins.json'
    pins = json.loads(pins_path.read_text())
    rust_root = ROOT / '.deps/libsignal-v0.106.1'
    references = [rust_root / name for name in ['rust/protocol/src/pqxdh.rs',
        'rust/protocol/src/kem.rs', 'rust/protocol/src/kem/kyber1024.rs',
        'rust/protocol/src/kem/mlkem1024.rs', 'rust/protocol/Cargo.toml', 'Cargo.lock']]
    archive = ROOT / '.deps/libsignal-v0.106.1.tar.gz'
    assert digest(archive) == pins['libsignal']['archive_sha256']
    with tarfile.open(archive) as bundle:
        for path in references:
            member = 'signalapp-libsignal-904c8dc/' + str(path.relative_to(rust_root))
            assert bundle.extractfile(member).read() == path.read_bytes(), path
    source_text = references[0].read_text()
    assert LABEL.decode() in source_text
    assert 'pub(crate) type InitialPQRKey = [u8; 32]' in source_text
    lock = tomllib.loads((rust_root / 'Cargo.lock').read_text())
    kem_package = next(p for p in lock['package'] if p['name'] == 'libcrux-ml-kem')
    kem_dir = ROOT / ('.deps/libsignal-vendor/libcrux-ml-kem-' + kem_package['version'])
    checksums = json.loads((kem_dir / '.cargo-checksum.json').read_text())
    assert checksums['package'] == kem_package['checksum']
    for name, expected in checksums['files'].items():
        assert digest(kem_dir / name) == expected, name

    artifact = HERE / 'Artifacts/derive'
    inventory_path = artifact / 'inventory.json'
    inventory = json.loads(inventory_path.read_text())
    assert inventory['charon_exit_code'] == 101 and inventory['has_errors']
    assert inventory['entry_patterns'] == ['crate::pqxdh::*::derive_with_label']
    assert inventory['explicit_exclusions'] == inventory['explicit_opaque_patterns'] == inventory['source_patches'] == []
    assert digest(HERE / 'extract.py') == inventory['script_sha256']
    assert digest(artifact / 'pqxdh.llbc') == inventory['llbc_sha256']
    for name, expected in inventory['source_sha256'].items():
        assert digest(ROOT / name) == expected, name
    charon_log = (artifact / 'charon.log').read_text()
    assert 'GATs cannot work with the `--lift-associated-types` option' in charon_log
    assert 'hybrid-array-0.4.13/src/traits.rs:22:1' in charon_log
    assert not (artifact / 'aeneas.log').exists()
    translated = json.loads((artifact / 'pqxdh.llbc').read_text())['translated']
    declaration = next(d for d in translated['fun_decls'] if d is not None and d['def_id'] == 0)
    assert declaration['item_meta']['source_text'] in source_text

    sources = {Path(__file__), HERE / 'Fixtures.lean', HERE / 'Checks.lean', HERE / 'extract.py',
               pins_path, inventory_path, artifact / 'charon.log', artifact / 'pqxdh.llbc',
               archive, *references, kem_dir / '.cargo-checksum.json',
               *[kem_dir / name for name in checksums['files']]}
    def visit(module):
        if not module.startswith('TlsMpc'):
            return
        path = ROOT / (module.replace('.', '/') + '.lean')
        if path in sources:
            return
        sources.add(path)
        for imported in re.findall(r'^import ([A-Za-z0-9_.]+)', path.read_text(), re.M):
            visit(imported)
    visit('TlsMpc.Signal.Pqxdh')
    snapshot = {str(p.relative_to(ROOT)): digest(p) for p in sorted(sources)}
    subprocess.run(['lake', 'build', 'TlsMpc.Signal.Pqxdh'], cwd=ROOT, check=True)
    result = subprocess.run(['lake', 'env', 'lean', str(HERE / 'Checks.lean')], cwd=ROOT,
                            capture_output=True, text=True, check=True)
    expected = re.findall(r'^#print axioms (\S+)', (HERE / 'Checks.lean').read_text(), re.M)
    found = re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", result.stdout)
    assert [name for name, _ in found] == expected
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for name, assumptions in found:
        assert not ({a.strip() for a in assumptions.split(',') if a.strip()} - allowed), name
    (HERE / 'axioms.txt').write_text(result.stdout)

    fixtures = []
    for pattern in range(6):
        if pattern == 0:
            full = [bytes(32)] * 5
        elif pattern == 1:
            full = [b'\xff' * 32] * 5
        else:
            full = [bytes((i * (2 * pattern + 1) + 53 * field + 19 * pattern) % 256 for i in range(32)) for field in range(5)]
        for present in [False, True]:
            parts = full[:3] + [full[3] if present else b''] + full[4:]
            fixtures.append((f'pattern{pattern}-oneTime{int(present)}', parts, True))
    base = fixtures[-1][1]
    swapped = [base[1],base[0],*base[2:]]
    fixtures.append(('swapped-dh1-dh2', swapped, True))
    changed_kem = [*base[:4], bytes([base[4][0] ^ 1]) + base[4][1:]]
    fixtures.append(('changed-kem-bit', changed_kem, True))
    assert oracle(base) != oracle(swapped) and oracle(base) != oracle(changed_kem)
    for field in range(5):
        for length in [31, 33]:
            parts = list(base)
            parts[field] = bytes(length)
            fixtures.append((f'invalid-field{field}-length{length}', parts, False))
    records = []
    for name, parts, valid in fixtures:
        result = subprocess.run(['lake', 'env', 'lean', '--run', str(HERE / 'Fixtures.lean'),
                                 *[p.hex() for p in parts]], cwd=ROOT, capture_output=True, text=True, check=True)
        record = {'name': name, 'input_hex': [p.hex() for p in parts], 'accepted': valid}
        if valid:
            lines = result.stdout.strip().splitlines()
            assert len(lines) == 2, result.stdout
            actual, state = (bytes(json.loads(line)) for line in lines)
            expected_keys = oracle(parts)
            assert actual == expected_keys, name
            assert state == expected_keys[:64] + bytes(4) + expected_keys[64:], name
            record.update({'keys_hex': actual.hex(), 'initial_state_hex': state.hex()})
        else:
            assert result.stdout.strip() == 'none', (name, result.stdout)
        records.append(record)
    fixture_path = HERE / 'fixture-results.json'
    fixture_path.write_text(json.dumps({'oracle': 'Python stdlib hmac.digest with SHA256; full HKDF96 and initialization100 comparison',
                                      'fixtures': records}, indent=2) + '\n')
    assert snapshot == {str(p.relative_to(ROOT)): digest(p) for p in sorted(sources)}
    report = {
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'accepted_actual_rust_reference': False,
        'libsignal_commit': pins['libsignal']['commit'], 'source_sha256': snapshot,
        'checked_endpoints': len(found), 'theorems': expected,
        'allowed_foundational_axioms': sorted(allowed), 'custom_axioms': [],
        'axiom_report_sha256': digest(HERE / 'axioms.txt'),
        'fixture_report_sha256': digest(fixture_path),
        'valid_fixtures': sum(v for _, _, v in fixtures), 'invalid_shape_fixtures': sum(not v for _, _, v in fixtures),
        'scope': 'Concrete and symbolic PQXDH input construction, HKDF-SHA256 root32/chain32/PQR32, initial chain counter0, public shape rejection, every numeric AIG output bit.',
        'public_shape': 'Three DH32 and KEM32 agreements; optional one-time DH has public length0 or32; all values and outputs stay shared.',
        'label': LABEL.decode(), 'input_order': 'FF32 || DH1 || DH2 || DH3 || optionalDH4 || KyberSharedSecret32',
        'output_layout': 'keys: root32||chain32||PQR32; initialState: root32||chain32||counterBE4zero||PQR32',
        'kem_path': {'crate': 'libcrux-ml-kem', 'version': kem_package['version'], 'checksum': kem_package['checksum'],
                     'entrypoints': ['libcrux_ml_kem::kyber1024::encapsulate', 'libcrux_ml_kem::kyber1024::decapsulate'],
                     'distinction': 'Default Kyber1024 implementation, not the distinct feature-gated MLKEM1024 profile.',
                     'vendor_source_checksum_entries_verified': len(checksums['files'])},
        'actual_extraction': {'route_count': 1, 'entry': 'crate::pqxdh::*::derive_with_label',
            'charon_exit_code': inventory['charon_exit_code'], 'has_errors': True, 'inventory_counts': inventory['counts'],
            'body_kinds': inventory['body_kinds'], 'aeneas_invoked': False, 'closed_translation': False,
            'diagnostic': 'GATs cannot work with --lift-associated-types (implied by --preset=aeneas), hybrid-array-0.4.13/src/traits.rs:22:1',
            'opaque_crypto_dependency_observed': ['hkdf::Hkdf::new', 'hkdf::Hkdf::expand'],
            'rust_source_changes': [], 'translator_changes': [], 'llbc_preprocessing': [], 'custom_models': [],
            'never_candidate_used': False},
        'actual_pqxdh_or_hkdf_wrapper_equivalence': False,
        'dh_or_kem_computation_implemented_here': False,
        'native_mpc_execution': False,
        'pending': ['Compose actual X25519 agreement outputs and Kyber1024 encapsulation/decapsulation into this KDF.',
                    'Close actual HKDF/PQXDH wrapper translation and implementation-reference proof.',
                    'Identity and signed-prekey validation, canonical base-key check, agreement/KEM failure handling.',
                    'Full ratchet/session initialization, prekey handling, persistence, and distributed execution.']}
    output = HERE / 'proof-report.json'
    output.write_text(json.dumps(report, indent=2) + '\n')
    print(f'Checked {len(found)} PQXDH KDF endpoints and {len(fixtures)} fixtures; actual wrapper remains blocked.')
    print('proof-report.json SHA256: ' + digest(output))


if __name__ == '__main__':
    main()
