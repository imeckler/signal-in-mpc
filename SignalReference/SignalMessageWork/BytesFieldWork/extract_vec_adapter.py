#!/usr/bin/env python3
"""Extract actual pinned Prost Vec bytes-adapter methods.

This profile keeps generic buffer/bytes-adapter dictionaries explicit. It is
not an accepted full SignalMessage or concrete Vec-buffer reference until the
called concrete adapter operations are discharged separately.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parents[1]
ROOT = REFERENCE.parent
spec = importlib.util.spec_from_file_location('canonical_extract', REFERENCE / 'extract.py')
canonical = importlib.util.module_from_spec(spec)
spec.loader.exec_module(canonical)
digest = canonical.digest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--charon-only', action='store_true')
    args = parser.parse_args()
    source = canonical.check_sources()
    pins = canonical.PINS
    rust = ROOT / '.deps/rust-nightly-2026-08-18'
    charon = (REFERENCE / pins['charon']['directory'] / 'target/release/charon').resolve()
    aeneas = (REFERENCE / pins['aeneas']['directory'] / 'aeneas').resolve()
    versions = {'charon': subprocess.check_output([str(charon), 'version'], text=True).strip(),
                'aeneas': subprocess.check_output([str(aeneas), '-version'], text=True).strip(),
                'rustc': subprocess.check_output([str(rust / 'bin/rustc'), '--version'], text=True).strip()}
    assert pins['charon']['commit'] in versions['charon']
    assert pins['aeneas']['release'] in versions['aeneas']
    assert pins['charon']['rustc_version'] == versions['rustc']
    env = os.environ.copy()
    env.update({'PATH': str(rust / 'bin') + os.pathsep + env.get('PATH', ''),
                'CHARON_TOOLCHAIN_IS_IN_PATH': '1', 'DYLD_LIBRARY_PATH': str(rust / 'lib'),
                'LD_LIBRARY_PATH': str(rust / 'lib'), 'CARGO_HOME': str(ROOT / '.deps/libsignal-cargo-home'),
                'CARGO_TARGET_DIR': str(ROOT / '.deps/libsignal-charon-target'), 'RUSTFLAGS': ''})
    destination = HERE / 'VecAdapterArtifacts'
    destination.mkdir(parents=True, exist_ok=True)
    llbc = destination / 'vec_adapter.llbc'
    llbc.unlink(missing_ok=True)
    subprocess.run([str(rust / 'bin/cargo'), 'clean', '--package', 'prost@0.14.4',
                    '--target', 'aarch64-apple-darwin'], cwd=source, env=env, check=True,
                   stdout=subprocess.DEVNULL)
    command = [str(charon), 'cargo', '--preset=aeneas', '--no-dedup-serialized-ast',
               '--sysroot=default', '--error-on-warnings',
               '--start-from={crate::encoding::sealed::BytesAdapter for alloc::vec::Vec}::len,{crate::encoding::sealed::BytesAdapter for alloc::vec::Vec}::append_to',
               '--dest-file=' + str(llbc), '--', '--package', 'prost@0.14.4', '--lib', '--locked', '--offline']
    with (destination / 'charon.log').open('w') as log:
        result = subprocess.run(command, cwd=source, env=env, stdout=log, stderr=subprocess.STDOUT)
    sources = [source / 'Cargo.lock',
               ROOT / '.deps/libsignal-vendor/prost-0.14.4/src/encoding.rs',
               ROOT / '.deps/libsignal-vendor/prost-0.14.4/src/encoding/varint.rs',
               ROOT / '.deps/libsignal-vendor/bytes-1.12.0/src/buf/buf_mut.rs',
               ROOT / '.deps/libsignal-vendor/bytes-1.12.0/src/buf/buf_impl.rs']
    report = {'candidate_only': True, 'accepted_reference': False, 'source_patches': [],
              'versions': versions, 'script_sha256': digest(Path(__file__)),
              'source_sha256': {str(p.relative_to(ROOT)): digest(p) for p in sources},
              'charon_command': [x.replace(str(ROOT), '$WORKSPACE') for x in command],
              'charon_exit_code': result.returncode}
    if llbc.exists():
        report.update(canonical.inventory(llbc))
    target = destination / 'inventory.json'
    target.write_text(json.dumps(report, indent=2) + '\n')
    if result.returncode or not llbc.exists() or report['has_errors']:
        print('Incomplete Charon extraction; see ' + str(target.relative_to(ROOT)))
        return 1
    if args.charon_only:
        return 0
    generated = HERE / 'VecAdapterGenerated'
    generated.mkdir(parents=True, exist_ok=True)
    for old in generated.glob('*.lean'):
        old.unlink()
    command = [str(aeneas), '-backend', 'lean', str(llbc), '-dest', str(REFERENCE),
               '-subdir', '/SignalMessageWork/BytesFieldWork/VecAdapterGenerated', '-split-files',
               '-namespace', 'ProstVecAdapter', '-warnings-as-errors', '-no-progress-bar']
    with (destination / 'aeneas.log').open('w') as log:
        result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    report.update({'aeneas_exit_code': result.returncode,
                   'aeneas_command': [x.replace(str(ROOT), '$WORKSPACE') for x in command],
                   'generated_files': {str(p.relative_to(REFERENCE)): digest(p) for p in generated.glob('*.lean')},
                   'remaining_external_templates': [p.name for p in generated.glob('*_Template.lean')]})
    target.write_text(json.dumps(report, indent=2) + '\n')
    print('Actual bytes-field composition: Aeneas exit ' + str(result.returncode))
    return result.returncode


if __name__ == '__main__':
    raise SystemExit(main())
