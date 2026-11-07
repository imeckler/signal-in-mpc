#!/usr/bin/env python3
"""Unaccepted unchanged-source optimized-MIR inverse-layout probe.

This profile asks rustc to inline and simplify the real hybrid-array code.
It does not change Rust, standard models or the accepted extraction profile.
"""

import json
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REFERENCE = HERE.parents[1]
ROOT = REFERENCE.parent
sys.path.insert(0, str(REFERENCE))
from extract import PINS, check_sources, digest, inventory


def main():
    source = check_sources()
    rust = ROOT / '.deps/rust-nightly-2026-08-18'
    charon = (REFERENCE / PINS['charon']['directory'] / 'target/release/charon').resolve()
    aeneas = (REFERENCE / PINS['aeneas']['directory'] / 'aeneas').resolve()
    versions = {'charon': subprocess.check_output([str(charon), 'version'], text=True).strip(),
                'aeneas': subprocess.check_output([str(aeneas), '-version'], text=True).strip(),
                'rustc': subprocess.check_output([str(rust / 'bin/rustc'), '--version'], text=True).strip()}
    if (PINS['charon']['commit'] not in versions['charon'] or
            PINS['aeneas']['release'] not in versions['aeneas'] or
            versions['rustc'] != PINS['charon']['rustc_version']):
        raise ValueError('Tool versions differ')
    sysroot = REFERENCE / 'PaddingWork/Unpad/Sysroot'
    provenance_path = REFERENCE / 'PaddingWork/Unpad/sysroot-provenance.json'
    provenance = json.loads(provenance_path.read_text())
    for name, expected in provenance['sysroot_artifact_sha256'].items():
        if digest(sysroot / name) != expected:
            raise ValueError('Full-MIR sysroot differs')
    flags = ['--cfg', 'aes_backend="soft"',
             '-Zmir-enable-passes=+Inline,+GVN,+SimplifyLocals-final',
             '-Cdebug-assertions=yes', '-Coverflow-checks=yes']
    env = os.environ.copy()
    env.update({'PATH': str(rust / 'bin') + os.pathsep + env.get('PATH', ''),
                'CHARON_TOOLCHAIN_IS_IN_PATH': '1', 'DYLD_LIBRARY_PATH': str(rust / 'lib'),
                'LD_LIBRARY_PATH': str(rust / 'lib'), 'CHARON_MIRI_SYSROOTS': str(sysroot),
                'CARGO_HOME': str(ROOT / '.deps/libsignal-cargo-home'),
                'CARGO_TARGET_DIR': str(HERE / 'Build'), 'RUSTFLAGS': ' '.join(flags)})
    llbc = HERE / 'wrapper.llbc'
    command = [str(charon), 'cargo', '--preset=aeneas', '--sysroot=miri',
               '--no-dedup-serialized-ast', '--error-on-warnings', '--monomorphize',
               '--mir=optimized', '--exclude=hybrid_array::traits::ArraySize',
               '--include=hybrid_array::*', '--start-from=crate::soft::fixslice::inv_bitslice',
               '--dest-file=' + str(llbc), '--', '--package', 'aes@0.9.1', '--lib',
               '--locked', '--offline', '--target', 'aarch64-apple-darwin']
    llbc.unlink(missing_ok=True)
    with (HERE / 'charon.log').open('w') as log:
        status = subprocess.run(command, cwd=source, env=env, stdout=log, stderr=subprocess.STDOUT)
    report = {'accepted_reference': False, 'versions': versions, 'source_patches': [],
              'custom_models': [], 'rustflags': flags, 'preserve_debug_assertions': True,
              'preserve_overflow_checks': True,
              'charon_command': [x.replace(str(ROOT), '$WORKSPACE') for x in command],
              'charon_exit_code': status.returncode,
              'sysroot_provenance_file': str(provenance_path.relative_to(REFERENCE)),
              'sysroot_provenance_sha256': digest(provenance_path)}
    if llbc.exists():
        report.update(inventory(llbc))
    if status.returncode == 0 and llbc.exists() and not report['has_errors']:
        generated = HERE / 'Generated'
        generated.mkdir(exist_ok=True)
        command = [str(aeneas), '-backend', 'lean', str(llbc), '-dest', str(REFERENCE),
                   '-subdir', '/AesInverseLayoutWork/OptimizedProbe/Generated', '-split-files',
                   '-namespace', 'RustCryptoAesInverseOptimizedProbe', '-warnings-as-errors', '-no-progress-bar']
        with (HERE / 'aeneas.log').open('w') as log:
            status = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
        report['aeneas_command'] = command
        report['aeneas_exit_code'] = status.returncode
        report['generated_files'] = {str(p.relative_to(REFERENCE)): digest(p)
                                     for p in sorted(generated.glob('*.lean'))}
    report['probe_script_sha256'] = digest(Path(__file__))
    (HERE / 'inventory.json').write_text(json.dumps(report, indent=2) + '\n')
    print(f'Optimized-MIR full-wrapper candidate exit={status.returncode}; no accepted reference claimed')
    return status.returncode


if __name__ == '__main__':
    raise SystemExit(main())
