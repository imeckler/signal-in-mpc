#!/usr/bin/env python3
"""Select the actual pinned PreKey constructor and content conversion.

All source and dependency files are unchanged. Incomplete dependency graphs
are diagnostic artifacts, never accepted implementation refinements.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parent
ROOT = REFERENCE.parent
module = importlib.util.spec_from_file_location('canonical_extract', REFERENCE / 'extract.py')
canonical = importlib.util.module_from_spec(module)
module.loader.exec_module(canonical)
PINS = canonical.PINS
digest = canonical.digest

PROFILES = {
    'Construct': ['--start-from=crate::state::bundle::*::new'],
    'Content': ['--start-from={core::convert::TryFrom for crate::state::bundle::PreKeyBundle}::try_from',
                '--include=core::option::*::zip', '--include=core::option::*::ok_or_else'],
}

PROFILES['ConstructScoped'] = [*PROFILES['Construct'],
    '--opaque=crate::kem::*::key_length', '--opaque=crate::error::SignalProtocolError']
PROFILES['ContentScoped'] = [*PROFILES['Content'], '--opaque=crate::kem::*::key_length']

PROFILES['ContentVisible'] = [*PROFILES['ContentScoped'], '--include=core::convert::TryFrom',
    '--start-from-if-exists=crate::state::bundle::*::try_from']
PROFILES['ConstructTyped'] = [*PROFILES['ConstructScoped'],
    '--include=libsignal_core::curve::PublicKey', '--include=libsignal_core::curve::PublicKeyData',
    '--include=libsignal_core::address::DeviceId']

PROFILES['ContentPresent'] = [*PROFILES['ContentVisible'],
    '--opaque=crate::error::SignalProtocolError',
    '--opaque=crate::state::bundle::*::try_from::*::call_once',
    '--include=libsignal_core::curve::PublicKey', '--include=libsignal_core::curve::PublicKeyData',
    '--include=libsignal_core::address::DeviceId']

PROFILES['ContentModels'] = [x for x in PROFILES['ContentPresent'] if not x.startswith('--include=core::option')]
PROFILES['ContentModels'] += ['--opaque=core::option::*::zip', '--opaque=core::option::*::ok_or_else']

PROFILES['ConstructData'] = [*PROFILES['ConstructTyped'],
    '--include=core::num::nonzero::NonZero', '--include=core::num::niche_types::NonZeroU8Inner']

PROFILES['ContentZipMono'] = [x for x in PROFILES['ContentModels'] if x != '--opaque=core::option::*::zip']
PROFILES['ContentZipMono'] += ['--include=core::option::*::zip', '--monomorphize']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('profile', choices=PROFILES)
    parser.add_argument('--charon-only', action='store_true')
    args = parser.parse_args()
    source = canonical.check_sources()
    rust = ROOT / '.deps/rust-nightly-2026-08-18'
    charon = (REFERENCE / PINS['charon']['directory'] / 'target/release/charon').resolve()
    aeneas = (REFERENCE / PINS['aeneas']['directory'] / 'aeneas').resolve()
    versions = {'charon': subprocess.check_output([str(charon), 'version'], text=True).strip(),
                'aeneas': subprocess.check_output([str(aeneas), '-version'], text=True).strip(),
                'rustc': subprocess.check_output([str(rust / 'bin/rustc'), '--version'], text=True).strip()}
    assert PINS['charon']['commit'] in versions['charon']
    assert PINS['aeneas']['release'] in versions['aeneas']
    assert PINS['charon']['rustc_version'] == versions['rustc']
    env = os.environ.copy()
    env.update({'PATH': str(rust / 'bin') + os.pathsep + env.get('PATH', ''),
                'CHARON_TOOLCHAIN_IS_IN_PATH': '1', 'DYLD_LIBRARY_PATH': str(rust / 'lib'),
                'LD_LIBRARY_PATH': str(rust / 'lib'), 'CARGO_HOME': str(ROOT / '.deps/libsignal-cargo-home'),
                'CARGO_TARGET_DIR': str(HERE / 'Build/Charon'), 'RUSTFLAGS': ''})
    destination = HERE / 'Artifacts' / args.profile
    destination.mkdir(parents=True, exist_ok=True)
    llbc = destination / 'prekey.llbc'
    llbc.unlink(missing_ok=True)
    command = [str(charon), 'cargo', '--preset=aeneas', '--no-dedup-serialized-ast',
               '--sysroot=default', '--error-on-warnings',
               *PROFILES[args.profile], '--dest-file=' + str(llbc), '--',
               '--package', 'libsignal-protocol', '--lib', '--locked', '--offline']
    with (destination / 'charon.log').open('w') as log:
        result = subprocess.run(command, cwd=source, env=env, stdout=log, stderr=subprocess.STDOUT)
    source_files = [source / 'rust/protocol/src/state/bundle.rs',
                    source / 'rust/protocol/src/error.rs', source / 'rust/protocol/src/kem.rs',
                    source / 'rust/protocol/src/identity_key.rs', source / 'rust/core/src/curve.rs',
                    source / 'rust/core/src/address.rs', source / 'rust/protocol/src/state/prekey.rs',
                    source / 'rust/protocol/src/state/signed_prekey.rs',
                    source / 'rust/protocol/src/state/kyber_prekey.rs', source / 'Cargo.lock']
    report = {'candidate_only': True, 'accepted_reference': False, 'versions': versions, 'source_patches': [],
              'source_sha256': {str(p.relative_to(ROOT)): digest(p) for p in source_files},
              'charon_command': [x.replace(str(ROOT), '$WORKSPACE') for x in command],
              'charon_exit_code': result.returncode, 'script_sha256': digest(Path(__file__))}
    if llbc.exists():
        report.update(canonical.inventory(llbc))
    target = destination / 'inventory.json'
    target.write_text(json.dumps(report, indent=2) + '\n')
    if result.returncode or not llbc.exists() or report['has_errors']:
        print(f'Incomplete selected PreKey extraction; see {target.relative_to(ROOT)}')
        return 1
    if args.charon_only:
        return 0
    generated = HERE / 'Generated' / args.profile
    generated.mkdir(parents=True, exist_ok=True)
    for previous in generated.glob('*.lean'):
        if previous.name in ('Types.lean','Funs.lean') or previous.name.endswith('_Template.lean'):
            previous.unlink()
    command = [str(aeneas), '-backend', 'lean', str(llbc), '-dest', str(REFERENCE),
               '-subdir', '/PreKeyReferenceWork/Generated/' + args.profile, '-split-files',
               '-namespace', 'PreKeyReference', '-warnings-as-errors', '-no-progress-bar', '-all-computable']
    with (destination / 'aeneas.log').open('w') as log:
        result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    report['aeneas_command'] = [x.replace(str(ROOT), '$WORKSPACE') for x in command]
    report['aeneas_exit_code'] = result.returncode
    report['generated_files'] = {str(p.relative_to(REFERENCE)): digest(p) for p in generated.glob('*.lean') if p.name in ('Types.lean','Funs.lean') or p.name.endswith('_Template.lean')}
    report['remaining_external_templates'] = [p.name for p in generated.glob('*_Template.lean')]
    target.write_text(json.dumps(report, indent=2) + '\n')
    print(f'Actual PreKey constructor: Aeneas exit {result.returncode}; templates {report["remaining_external_templates"]}')
    return result.returncode


if __name__ == '__main__':
    raise SystemExit(main())
