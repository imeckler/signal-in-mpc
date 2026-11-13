#!/usr/bin/env python3
"""Build what a computation node runs, by calling the repository's own build scripts.

    build_artifacts.py plan                                   print every step and command (default; does nothing)
    build_artifacts.py native  [--mode M] [--out DIR] --yes   build on this machine (macOS build machine) into DIR/bin
    build_artifacts.py circuits --deployment JSON --out DIR [--max-gb N] --yes
                                                              produce the circuit set + manifest (scripts/produce_circuits.py)
    build_artifacts.py word    --out DIR --yes                copy the word circuits and V3 field programs, with their digest
    build_artifacts.py context --out DIR [--commit C] --yes   stage the Docker build context (sources at a commit + engines bundle)
    build_artifacts.py image   --context DIR --mode M --tag T [--dockerfile F] [--target S] [--timeout S] --yes
                                                              docker build of the worker (or database) image

Safe by default: without --yes every subcommand prints what it would run and stops. Idempotent:
the underlying builds are incremental (lake, cargo, make), a circuit already in the cache is not
produced again, and a staged directory is rebuilt from scratch only when --out does not exist
(an existing one is refused unless --replace).

Heavy steps (Lean builds, engine builds, cargo builds, circuit production, image builds) run one
at a time under scripts/guarded.py --heavy (the machine-wide lock; parallel lowering crashed this
machine twice). --no-guard skips the wrapper (a dedicated build machine).

M is malicious (default; statistical 128) or semi-honest; `native --mode both` builds both workers.
Nothing here contacts a Signal host. `context` and `image` download toolchains, distribution
packages and the database client's crates (crates.io, github.com); `native` is offline.
"""
import argparse
import io
import json
import os
import shutil
import subprocess
import sys
import tarfile
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import deploylib as dl  # noqa: E402

ROOT = dl.ROOT
GUARD = ROOT / 'scripts/guarded.py'
LOGS = ROOT / '.deps/deploy-logs'
WORD_SOURCE = ROOT / '.deps/emp-hybrid-word-v1'
SSDB = ROOT / '.deps/secret-shared-db-handoff'
VARIANT = {'malicious': 'v3', 'semi-honest': 'sh-v3'}
RUST_NIGHTLY = 'nightly-2025-09-24'
# Tracked paths the image is built from (git ls-files under these prefixes, at --commit).
SOURCE_PREFIXES = ['TlsMpc/', 'TlsMpc.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'handshake_backend/',
                   'signal_backend/TextNotificationWork/', 'signal_backend/Oracle/src/session_send_projection.rs',   # (the KEM tool's #[path] module)
                   'node_worker/', 'node_daemon/', 'local_signal_server/provision/',
                   'deploy/', 'deployment/vm_pair_test/']
NEVER_STAGE = ('real_signal/', 'local_signal_server/state', 'Player-Data')


def guarded(gb, seconds, command, no_guard):
    return list(map(str, command)) if no_guard else [sys.executable, str(GUARD), '--heavy', str(gb), str(seconds), *map(str, command)]


def run_step(name, command, yes, log_name, timeout=None, cwd=ROOT, env=None):
    print(f'[{name}] ' + ' '.join(map(str, command)), flush=True)
    if not yes:
        return 0
    started = time.monotonic()
    status, tail = dl.run_logged(command, LOGS / log_name, timeout or 6 * 3600, cwd=cwd, env=env)
    print(f'[{name}] exit {status} after {time.monotonic() - started:.0f} s; log {LOGS / log_name}', flush=True)
    if status:
        for line in tail:
            print('    ' + line)
    return status


def openssl_prefix():
    sys.path.insert(0, str(ROOT / 'scripts'))
    try:
        from check_full_handshake import OPENSSL   # the Homebrew OpenSSL the harness compiles public_auth against
        return Path(OPENSSL)
    except Exception:  # noqa: BLE001
        return None


def native(a):
    modes = ['malicious', 'semi-honest'] if a.mode == 'both' else [a.mode]
    out = Path(a.out)
    steps = [
        ('controller', guarded(16, 5400, ['lake', 'build', 'public_service_controller'], a.no_guard), 'native-lake.log'),
        ('engine library', guarded(12, 3600, [sys.executable, ROOT / 'handshake_backend/EmpHybridWork/build_hybrid_v3.py', '--engine-abi',
                                              *[VARIANT[m] for m in modes]], a.no_guard), 'native-engine-abi.log'),
    ]
    for m in modes:
        steps.append((f'worker {m}', guarded(12, 3600, ['bash', ROOT / 'node_worker/build.sh', VARIANT[m]], a.no_guard), f'native-worker-{VARIANT[m]}.log'))
    steps.append(('daemon', guarded(12, 3600, ['bash', ROOT / 'node_daemon/build.sh'], a.no_guard), 'native-daemon.log'))
    # provision.sh builds then RUNS the tool (it would provision against the local server): only its build line.
    crate = ROOT / 'local_signal_server/provision'
    steps.append(('KEM tool (scaffolding)', guarded(12, 3600, ['cargo', '+' + RUST_NIGHTLY, '--config', crate / '.cargo/config.toml', 'build', '--offline',
                                                               '--quiet', '--ignore-rust-version', '--manifest-path', crate / 'Cargo.toml'], a.no_guard),
                  'native-provision.log'))
    steps.append(('database client', guarded(12, 3600, ['cargo', 'build', '--locked', '--release', '--manifest-path', SSDB / 'Cargo.toml',
                                                        '--target-dir', ROOT / '.deps/deploy-ssdb-target', '-p', 'server', '--bin', 'handoff_client',
                                                        '--bin', 'server', '-p', 'pki'], a.no_guard), 'native-ssdb.log'))
    ssl = openssl_prefix()
    public_auth = ['c++', '-std=c++20', '-O2', ROOT / 'handshake_backend/public_auth.cpp', '-lssl', '-lcrypto', '-o', out / 'bin/public_auth']
    if ssl:
        public_auth[3:3] = ['-I' + str(ssl / 'include'), '-L' + str(ssl / 'lib')]
    steps.append(('certificate checker', public_auth, 'native-public-auth.log'))
    if a.yes:
        (out / 'bin').mkdir(parents=True, exist_ok=True)
    for name, command, log in steps:
        if run_step(name, command, a.yes, log):
            return 1
    if not a.yes:
        print('(plan only: add --yes to build)')
        return 0
    produced = {
        'public_service_controller': ROOT / '.lake/build/bin/public_service_controller',
        'node-daemon': ROOT / 'node_daemon/target/debug/node-daemon',
        'notify-app': ROOT / 'node_daemon/target/debug/notify-app',
        'lss-provision': crate / 'target/debug/lss-provision',
        'handoff_client': ROOT / '.deps/deploy-ssdb-target/release/handoff_client',
        'server': ROOT / '.deps/deploy-ssdb-target/release/server',
        'pki': ROOT / '.deps/deploy-ssdb-target/release/pki',
    }
    for m in modes:
        produced[f'node-worker-{VARIANT[m]}'] = ROOT / f'node_worker/target/{VARIANT[m]}/release/node-worker'
    info = dict(format='tls-mpc-native-build-v1', built_at=int(time.time()), modes=modes, binaries={})
    for name, path in produced.items():
        if not path.is_file():
            print(f'missing after the build: {path}')
            return 1
        shutil.copy2(path, out / 'bin' / name)
        info['binaries'][name] = dl.sha256_file(out / 'bin' / name)
    info['binaries']['public_auth'] = dl.sha256_file(out / 'bin/public_auth')
    info['git'] = subprocess.run(['git', '-C', str(ROOT), 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
    (out / 'build-info.json').write_text(json.dumps(info, indent=1, sort_keys=True) + '\n')
    print(f'binaries in {out / "bin"}; hashes in {out / "build-info.json"} (MP-SPDZ library: .deps/two-party-comparison/data61-MP-SPDZ-113c4e4)')
    return 0


def circuits(a):
    command = guarded(a.max_gb + 2, 4 * 3600, [sys.executable, ROOT / 'scripts/produce_circuits.py', a.deployment, a.out, '--max-gb', a.max_gb], a.no_guard)
    print('production deployment: about 1.5-2 h from an empty cache, 414 kernels, 31 GB, one kernel at a time; '
          'tls-open-typed 12288 peaks at 23.6 GB (hence --max-gb 26 for the production and compact sets)')
    status = run_step('circuits', command, a.yes, 'circuits.log')
    if a.yes and status == 0:
        manifest = Path(a.out) / 'manifest.txt'
        digest, rows = dl.read_manifest(manifest)
        print(f'manifest {manifest}: {len(rows)} kernels, sha256 {digest}  <- EXPECTED_MANIFEST_SHA256 on both nodes')
    return status


def word(a):
    out = Path(a.out)
    files = sorted(p for p in WORD_SOURCE.iterdir() if p.is_file() and p.suffix in ('.flat', '.v3'))
    print(f'copy {len(files)} files ({sum(p.stat().st_size for p in files) / 1e6:.0f} MB: word circuits *.flat, V3 field programs *.v3) '
          f'from {WORD_SOURCE} to {out}')
    if not a.yes:
        print('(plan only: add --yes)')
        return 0
    out.mkdir(parents=True, exist_ok=True)
    for p in files:
        target = out / p.name
        if target.exists() and dl.sha256_file(target) == dl.sha256_file(p):
            continue
        shutil.copy2(p, target)
    problems, stats = dl.word_dir_summary(out)
    (out / 'WORD_DIR.json').write_text(json.dumps(stats, indent=1, sort_keys=True) + '\n')
    for problem in problems:
        print('problem:', problem)
    print(f'word dir digest {stats.get("word_dir_sha256")}  <- EXPECTED_WORD_DIR_SHA256 on both nodes')
    return 1 if problems else 0


def git_archive(repo, commit, paths, destination):
    """Extract `git archive COMMIT -- paths` of `repo` into `destination` (tracked content at that commit)."""
    data = subprocess.run(['git', '-C', str(repo), 'archive', '--format=tar', commit, '--', *paths], capture_output=True, check=True).stdout
    names = []
    with tarfile.open(fileobj=io.BytesIO(data)) as tar:
        members = []
        for m in tar.getmembers():
            if m.issym() or m.islnk() or m.name.startswith('/') or '..' in Path(m.name).parts:
                continue
            if any(bad in m.name for bad in NEVER_STAGE):
                continue
            members.append(m)
            names.append(m.name)
        tar.extractall(destination, members=members, filter='data')
    return names


def context(a):
    out = Path(a.out).resolve()
    commit = a.commit
    head = subprocess.run(['git', '-C', str(ROOT), 'rev-parse', commit], capture_output=True, text=True).stdout.strip()
    paths = [p for p in subprocess.run(['git', '-C', str(ROOT), 'ls-files'], capture_output=True, text=True).stdout.splitlines()
             if any(p == q or p.startswith(q) for q in SOURCE_PREFIXES)]
    bundle_cmd = guarded(12, 3600, [sys.executable, ROOT / 'deployment/vm_pair_test/make_bundle.py', '--with-workers', '--no-archive',
                                    '--out', out / 'bundle-work'], a.no_guard)
    print(f'stage the Docker build context in {out}:')
    print(f'  src/      {len(paths)} tracked files at {commit} ({head[:12]}), under: {" ".join(SOURCE_PREFIXES)}')
    print(f'  src/.deps/libsignal-vendor, libsignal-v0.106.1 (vendored crates, path dependencies), secret-shared-db-handoff (git archive HEAD)')
    print('  bundle/   ' + ' '.join(map(str, bundle_cmd)))
    print('  pins.json (node_worker loader pins), context.json (provenance)')
    if not a.yes:
        print('(plan only: add --yes)')
        return 0
    if out.exists():
        if not a.replace:
            print(f'{out} exists: remove it or pass --replace')
            return 1
        shutil.rmtree(out)
    (out / 'src').mkdir(parents=True)
    staged = git_archive(ROOT, commit, SOURCE_PREFIXES, out / 'src')
    # Key-looking files never enter the context (the build needs none).
    sys.path.insert(0, str(ROOT / 'deployment/vm_pair_test'))
    import make_bundle
    removed = []
    for name in staged:
        path = out / 'src' / name
        if path.is_file() and (make_bundle.REFUSE_SUFFIX.search(path.name) or
                               (path.stat().st_size <= (4 << 20) and make_bundle.REFUSE_TEXT.search(path.read_bytes()))):
            path.unlink()
            removed.append(name)
    if removed:
        print(f'left out {len(removed)} key-looking tracked files: ' + ', '.join(removed[:8]) + (' …' if len(removed) > 8 else ''))
    deps = out / 'src/.deps'
    deps.mkdir()
    print('copying the vendored crates (about 460 MB) …', flush=True)
    shutil.copytree(ROOT / '.deps/libsignal-vendor', deps / 'libsignal-vendor', symlinks=False)
    shutil.copytree(ROOT / '.deps/libsignal-v0.106.1', deps / 'libsignal-v0.106.1', symlinks=False,
                    ignore=shutil.ignore_patterns('target', '.git'))
    ssdb_head = subprocess.run(['git', '-C', str(SSDB), 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
    (deps / 'secret-shared-db-handoff').mkdir()
    git_archive(SSDB, 'HEAD', ['.'], deps / 'secret-shared-db-handoff')
    status = run_step('bundle', bundle_cmd, True, 'context-bundle.log')
    if status:
        return status
    (out / 'bundle-work' / 'vm-pair').rename(out / 'bundle')
    shutil.rmtree(out / 'bundle-work', ignore_errors=True)
    pins = dl.parse_loader_pins(out / 'src/node_worker/src/loader.rs')
    (out / 'pins.json').write_text(json.dumps(pins, indent=1, sort_keys=True) + '\n')
    provenance = dict(format='tls-mpc-build-context-v1', commit=head, staged_at=int(time.time()), files=len(staged) - len(removed),
                      left_out=removed, secret_shared_db_commit=ssdb_head,
                      bundle_manifest_sha256=dl.sha256_file(out / 'bundle/MANIFEST.sha256'), pins=len(pins))
    (out / 'context.json').write_text(json.dumps(provenance, indent=1, sort_keys=True) + '\n')
    print(f'context ready: {out} (commit {head[:12]}, database {ssdb_head[:12]}, {len(pins)} pins)')
    return 0


def image(a):
    docker = dl.docker_binary()
    dockerfile = Path(a.dockerfile or (ROOT / 'deploy/docker/worker.Dockerfile'))
    command = [docker or 'docker', 'build', '--progress=plain', '-f', dockerfile, '--build-arg', f'MODE={a.mode}', '-t', a.tag]
    if a.target:
        command += ['--target', a.target]
    if a.platform:
        command += ['--platform', a.platform]
    command.append(a.context)
    print('note: the build downloads Ubuntu packages, elan/Lean, rustup and the database client\'s crates; it is CPU-heavy for a long time')
    if not a.yes:
        print('[image] ' + ' '.join(map(str, command)))
        print('(plan only: add --yes)')
        return 0
    if not docker:
        print('docker not found')
        return 1
    try:
        probe = subprocess.run([docker, 'version', '--format', '{{.Server.Version}}'], capture_output=True, text=True, timeout=20)
    except subprocess.TimeoutExpired:
        print('docker did not answer within 20 s: not building (do not restart it from here; see DEPLOYMENT.md "Status")')
        return 1
    if probe.returncode:
        print('docker is not usable: ' + probe.stderr.strip()[:300])
        return 1
    log = f'image-{a.tag.replace(":", "-").replace("/", "-")}.log'
    return run_step('image', guarded(4, a.timeout, command, a.no_guard), True, log, timeout=a.timeout + 600)


def plan(_):
    print(__doc__)
    print('Order for a deployment (DEPLOYMENT.md, "Build"):')
    print('  1. build_artifacts.py context --out /path/ctx --yes      (or `native --mode both --yes` on the macOS build machine)')
    print('  2. build_artifacts.py image --context /path/ctx --mode malicious --tag tls-mpc-node:malicious --yes')
    print('  3. build_artifacts.py circuits --deployment real_signal/deployment-production.json --out /path/circuits --max-gb 26 --yes')
    print('  4. build_artifacts.py word --out /path/word --yes')
    print('  5. verify_artifacts.py export on both nodes, then compare')
    return 0


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--no-guard', action='store_true', help='do not wrap heavy steps in scripts/guarded.py --heavy')
    sub = p.add_subparsers(dest='command')
    sub.add_parser('plan')
    n = sub.add_parser('native')
    n.add_argument('--mode', default='malicious', choices=['malicious', 'semi-honest', 'both'])
    n.add_argument('--out', default=str(ROOT / '.deps/deploy-native'))
    n.add_argument('--yes', action='store_true')
    c = sub.add_parser('circuits')
    c.add_argument('--deployment', required=True)
    c.add_argument('--out', required=True)
    c.add_argument('--max-gb', type=float, default=16.0)
    c.add_argument('--yes', action='store_true')
    w = sub.add_parser('word')
    w.add_argument('--out', required=True)
    w.add_argument('--yes', action='store_true')
    x = sub.add_parser('context')
    x.add_argument('--out', required=True)
    x.add_argument('--commit', default='HEAD')
    x.add_argument('--replace', action='store_true')
    x.add_argument('--yes', action='store_true')
    i = sub.add_parser('image')
    i.add_argument('--context', required=True)
    i.add_argument('--mode', default='malicious', choices=['malicious', 'semi-honest'])
    i.add_argument('--tag', required=True)
    i.add_argument('--dockerfile')
    i.add_argument('--target', help='build only up to this stage (base, engines, lean, rust, runtime)')
    i.add_argument('--platform', help='e.g. linux/amd64 or linux/arm64 (default: the Docker host\'s)')
    i.add_argument('--timeout', type=int, default=4 * 3600)
    i.add_argument('--yes', action='store_true')
    a = p.parse_args()
    handlers = dict(plan=plan, native=native, circuits=circuits, word=word, context=context, image=image)
    sys.exit(handlers.get(a.command or 'plan', plan)(a))


if __name__ == '__main__':
    main()
