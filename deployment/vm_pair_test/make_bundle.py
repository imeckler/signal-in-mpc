#!/usr/bin/env python3
"""Assemble the source bundle for the two-machine test (README.md, part 3). Run on the build machine:

    python3 scripts/guarded.py 12 3600 python3 deployment/vm_pair_test/make_bundle.py

Output (default .deps/vm-pair-bundle/): the directory `vm-pair/` and `vm-pair-bundle.tar.gz`.
The rented machines need no Lean: the benchmark's circuits are produced here, by the Lean
executable `flat_kernel_emitter` through handshake_backend/EmpHybridWork/circuit_cache.py (from
its cache when they are already there), and shipped as gate lists with their SHA-256 pins.

What goes in (and nothing else; see `refuse` for what stops the script):
  repo/      our sources the benchmark binaries are built from: exactly the files their compiler
             dependency records (.d) name, so build both fixtures here first (build_hybrid_v3.py
             pair-bench pair-bench-sh rounds rounds-sh).  --with-workers adds the two workers'
             sources, which include signal_backend/TextNotificationWork/PublicTextFixture.h: hex
             records of a throwaway test conversation ("PUBLIC DISPOSABLE FIXTURES ONLY"). Off by
             default so that the default bundle carries no key material of any kind.
  pins/      the pinned Lean field programs and small circuits (.flat) and their pin headers
  engines/   emp-tool and emp-ot (source trees), the validated-v3 Boolean engine headers, the
             field engine's library source (MP-SPDZ at the pinned commit, with SimplestOT_C,
             libOTe and the clones libOTe's build fetched: coproto, macoro, function2)
  circuits/  the per-message kernels as gate lists, and circuits.list
  kit/       this directory's scripts
  MANIFEST.sha256
"""
import argparse, hashlib, json, os, pathlib, re, shutil, subprocess, sys, tarfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
HERE = pathlib.Path(__file__).resolve().parent
BASE = ROOT / '.deps/two-party-comparison'
WORK = ROOT / 'handshake_backend/EmpHybridWork'
MP = BASE / 'data61-MP-SPDZ-113c4e4'

# One message to a prepared contact, smallest size class, as the harness runs it (PERFORMANCE.md,
# "Per message"): widths, the sealed-sender send circuit, the request frame with its record
# sealing and tag, the response record (tag check, typed open, masked reveal), storing the
# contact's state. About 2.65M AND gates together.
KERNELS = [
    'signal-widths 244',
    'signal-seal-built 244 1 1 1 1 1',
    'signal-request-ctr 244 1000 33 976 797 829',
    'gcm-tag',
    'gcm-check',
    'tls-open-typed 160',
    'tls-reveal-masked 139',
    'contact-seal 314',
]
BENCH_TARGETS = ['pair-bench-v3.d', 'pair-bench-sh-v3.d', 'rounds-v3.d', 'rounds-sh-v3.d', 'field_engine-v3.d', 'field_engine-sh.d']
WORKER_TARGETS = ['tls-worker-v3.d', 'tls-worker-sh-v3.d']
CODE_SUFFIXES = {'.cpp', '.h', '.hpp', '.c', '.cc', '.inc', '.s', '.S', '.q', '.py', '.cmake', '.in', '.asm', '.macros', '.inl', '.def', '.empbc'}
SOURCE_SUFFIXES = CODE_SUFFIXES | {'.txt', '.md', '.json', '.sh', '.data'}
SOURCE_NAMES = {'Makefile', 'CONFIG', 'LICENSE', 'License.txt', 'CMakeLists.txt', 'README', 'run', 'HOSTS.example'}
# Never copied, whatever tree they are in. (Player-Data holds the local test certificates' keys.)
NEVER_DIRS = {'.github', '.vscode', '__pycache__', 'CMakeFiles', 'Player-Data', 'Programs', 'logs', 'Persistence', 'Memory'}
SKIP_DIRS = NEVER_DIRS | {'.git', 'Compiler', 'doc', 'docs', 'bin', 'local', 'audit-report', 'bench', 'test', 'tests', 'Testing', 'Scripts'}
SKIP_FILES = {'CMakeCache.txt', 'cmake_install.cmake', 'CONFIG.mine'}
BUILT_SUFFIXES = {'.o', '.d', '.a', '.so', '.dylib', '.x', '.PNG', '.png'}
# By extension, always; by a word in the name, for anything that is not program source.
REFUSE_SUFFIX = re.compile(r'\.(key|pem|p12|pfx|der|crt|sqlite|sqlite3|db|log|env)$|^id_(rsa|ed25519|ecdsa)', re.I)
REFUSE_WORD = re.compile(r'(^|[-_.])(secret|secrets|password|credentials?|export|exports|account|accounts|state)([-_.]|$)', re.I)
REFUSE_TEXT = re.compile(rb'-----BEGIN [A-Z ]*PRIVATE KEY-----')
# Bundle paths that trip a rule above but were read and are not key material (none so far).
ALLOW = set()


def sha(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for block in iter(lambda: f.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


class Bundle:
    def __init__(self, out):
        self.out = out
        self.count = {}
        self.refused = []

    def refuse(self, rel, source):
        """Anything that looks like key material, an account, an export, a log or state stops the bundle."""
        if rel in ALLOW:
            return False
        name = pathlib.PurePosixPath(rel).name
        if REFUSE_SUFFIX.search(name) or (source.suffix not in CODE_SUFFIXES and '/.git/' not in rel and REFUSE_WORD.search(name)):
            return True
        if source.stat().st_size <= (4 << 20):
            if REFUSE_TEXT.search(source.read_bytes()):
                return True
        return False

    def add(self, source, rel, group):
        source = pathlib.Path(source)
        if source.is_symlink() or not source.is_file():
            return
        if self.refuse(rel, source):
            self.refused.append(rel)
            return
        target = self.out / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        if os.access(source, os.X_OK):
            target.chmod(0o755)
        self.count[group] = self.count.get(group, 0) + 1

    def tree(self, source, rel, group, keep=lambda p: True, skip_dirs=SKIP_DIRS, everything=False):
        """Source files of a tree. `everything`: every file that is not a build product (a
        library whose own build decides what it needs, and git clones it checks out)."""
        source = pathlib.Path(source)
        for directory, names, files in os.walk(source):
            names[:] = sorted(n for n in names if n not in skip_dirs and not (pathlib.Path(directory) / n).is_symlink())
            for name in sorted(files):
                path = pathlib.Path(directory) / name
                wanted = path.suffix not in BUILT_SUFFIXES if everything else (path.suffix in SOURCE_SUFFIXES or name in SOURCE_NAMES)
                if name in SKIP_FILES or not wanted or not keep(path):
                    continue
                self.add(path, str(pathlib.PurePosixPath(rel) / path.relative_to(source).as_posix()), group)


def dependencies(names):
    """Repo files (outside the engine trees) the named build targets were compiled from."""
    found = set()
    for name in names:
        record = BASE / name
        if not record.exists():
            sys.exit(f'{record} is missing: build the fixtures first (build_hybrid_v3.py pair-bench pair-bench-sh rounds rounds-sh)')
        for item in record.read_text().replace('\\\n', ' ').split(':', 1)[1].split():
            try:
                rel = pathlib.Path(item).resolve().relative_to(ROOT)
            except ValueError:
                continue                                  # system and Homebrew headers: distribution packages on Linux
            if rel.parts[0] != '.deps':
                found.add(rel)
    return sorted(found)


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--out', default=str(ROOT / '.deps/vm-pair-bundle'))
    p.add_argument('--with-workers', action='store_true', help="add the workers' sources (they include the public disposable text fixture)")
    p.add_argument('--no-archive', action='store_true')
    p.add_argument('--circuits-only', action='store_true', help='only circuits/ (for a local run of the benchmark)')
    args = p.parse_args()
    top = pathlib.Path(args.out).resolve()
    out = top / 'vm-pair'
    if out.exists():
        shutil.rmtree(out)
    out.mkdir(parents=True)
    b = Bundle(out)

    # Circuits: produced (or found in its cache) by the Lean emitter, one at a time.
    rows = ['PAIR_BENCH_CIRCUITS_V1']
    total_and = 0
    for kernel in KERNELS:
        reply = subprocess.run([sys.executable, str(WORK / 'circuit_cache.py'), 'kernel', *kernel.split()], capture_output=True, text=True)
        if reply.returncode != 0:
            sys.exit(f'circuit_cache.py failed for {kernel}: {reply.stderr[-400:]}')
        path, digest = reply.stdout.split()[:2]
        path = pathlib.Path(path)
        if sha(path) != digest:
            sys.exit(f'{path} does not match its pin')
        b.add(path, f'circuits/{path.name}', 'circuits')
        record = json.loads(path.with_suffix('.json').read_text())
        total_and += record['and_gates']
        rows.append(f'{digest} {path.name}')
        print(f'circuit {kernel}: {record["and_gates"]} AND, {path.stat().st_size / 1e6:.1f} MB')
    (out / 'circuits/circuits.list').write_text('\n'.join(rows) + '\n')
    (out / 'circuits/README.txt').write_text(
        'Gate lists (EMP_HYBRID_BOOL_V1) written by the Lean executable flat_kernel_emitter and named by\n'
        'handshake_backend/EmpHybridWork/circuit_cache.py. circuits.list pins each by SHA-256; the benchmark\n'
        'refuses a file that does not match. One iteration runs each once: %d AND gates.\n'
        'Kernels: %s\n' % (total_and, '; '.join(KERNELS)))
    print(f'circuits: {total_and} AND gates per iteration')
    if not args.circuits_only:
        # Our sources: exactly what the binaries were compiled from.
        for rel in dependencies(BENCH_TARGETS + (WORKER_TARGETS if args.with_workers else [])):
            b.add(ROOT / rel, 'repo/' + rel.as_posix(), 'repo')
        for name in ['pair_bench_fixture.cpp', 'rounds_fixture.cpp', 'field_engine.cpp'] + (['tls_worker_v3.cpp'] if args.with_workers else []):
            if not (out / f'repo/handshake_backend/EmpHybridWork/{name}').exists():      # (the records name their own source too)
                b.add(WORK / name, f'repo/handshake_backend/EmpHybridWork/{name}', 'repo')
        # Pins: headers, and the field programs and small circuits the headers name (the large
        # .flat files there belong to older fixtures).
        words = ROOT / '.deps/emp-hybrid-word-v1'
        for path in sorted(words.iterdir()):
            if path.is_file() and (path.suffix == '.h' or (path.suffix == '.flat' and path.stat().st_size < (2 << 20))):
                b.add(path, f'pins/word/{path.name}', 'pins')
        for path in sorted((ROOT / '.deps/emp-hybrid-curve-v1').iterdir()):
            if path.is_file():
                b.add(path, f'pins/curve/{path.name}', 'pins')
        # Engines.
        b.tree(BASE / 'emp-tool-339bde8479842c88d115cec16ffca90a4c050c3f', 'engines/emp-tool', 'engines')
        b.tree(BASE / 'emp-ot-5072bdab546c89a24be3368a7ce2bab1cdefec1f', 'engines/emp-ot', 'engines')
        b.tree(BASE / 'emp-ag2pc-validated-v3', 'engines/emp-ag2pc-validated-v3', 'engines')
        b.tree(MP, 'engines/MP-SPDZ', 'engines', skip_dirs=SKIP_DIRS | {'deps'})
        b.tree(MP / 'deps/SimplestOT_C', 'engines/MP-SPDZ/deps/SimplestOT_C', 'engines', keep=lambda q: q.name != 'Makefile')
        b.tree(MP / 'deps/simde', 'engines/MP-SPDZ/deps/simde', 'engines')
        b.tree(MP / 'deps/sse2neon', 'engines/MP-SPDZ/deps/sse2neon', 'engines')
        # libOTe and what its build cloned, as plain source trees at the commits they are checked
        # out at here: no git history, and not upstream's test certificates and keys (cert/, certs/).
        # libOTe's build runs `git checkout PIN` in each clone; build_linux.sh answers that for a
        # tree carrying .bundle-pinned (which records the commit).
        ote = MP / 'deps/libOTe2'
        plain = NEVER_DIRS | {'.git', 'out', 'cert', 'certs'}
        b.tree(ote, 'engines/MP-SPDZ/deps/libOTe2', 'engines', skip_dirs=plain, everything=True, keep=lambda q: q.name != '.git')
        pins = {row['name']: row['commit'] for row in json.loads((BASE / 'dependency-pins.json').read_text()) if 'name' in row}
        for clone in ('coproto', 'macoro', 'function2'):
            head = subprocess.run(['git', '-C', str(ote / 'out' / clone), 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
            dirty = subprocess.run(['git', '-C', str(ote / 'out' / clone), 'status', '--porcelain', '--untracked-files=no'], capture_output=True, text=True).stdout.strip()
            if head != pins.get(clone) or dirty:
                sys.exit(f'{clone}: checked out at {head or "?"} (pin {pins.get(clone)}), modified files: {bool(dirty)}')
            b.tree(ote / 'out' / clone, f'engines/MP-SPDZ/deps/libOTe2/out/{clone}', 'engines', skip_dirs=plain, everything=True, keep=lambda q: q.name != '.git')
            (out / f'engines/MP-SPDZ/deps/libOTe2/out/{clone}/.bundle-pinned').write_text(head + '\n')
        # The macOS tree's CONFIG ends with settings for this machine; the Linux ones come from
        # CONFIG.mine, which build_linux.sh writes.
        config = (MP / 'CONFIG').read_text()
        marker = '# Isolated two-party comparison, secure SoftSpoken path.'
        if config.count(marker) != 1:
            sys.exit('MP-SPDZ CONFIG: the local settings block was not found where expected')
        (out / 'engines/MP-SPDZ/CONFIG').write_text(config.split(marker)[0] + '# (bundle) machine settings: CONFIG.mine, written by kit/build_linux.sh.\n')
        for record in ('dependency-pins.json', 'validation-v3-build-source.json', 'emp-tool-modern-commit.json', 'emp-ot-modern-commit.json'):
            if (BASE / record).exists() and (BASE / record).stat().st_size < 100000:
                b.add(BASE / record, f'engines/pins/{record}', 'engines')
        # The kit itself.
        for path in sorted(HERE.rglob('*')):
            if path.is_file() and '__pycache__' not in path.parts:
                b.add(path, 'kit/' + path.relative_to(HERE).as_posix(), 'kit')
    if b.refused:
        print('REFUSED (looks like key material, an account, an export, a log or state):')
        for rel in b.refused:
            print('  ' + rel)
        sys.exit('bundle not written; remove these from the inputs or add a reviewed path to ALLOW')
    # Manifest, then one more pass over what was actually written.
    lines, size = [], 0
    for path in sorted(q for q in out.rglob('*') if q.is_file()):
        rel = path.relative_to(out).as_posix()
        lines.append(f'{sha(path)}  {rel}')
        size += path.stat().st_size
    (out / 'MANIFEST.sha256').write_text('\n'.join(lines) + '\n')
    print('files by part:', json.dumps(b.count), f'total {len(lines)} files, {size / 1e6:.0f} MB')
    if not args.no_archive and not args.circuits_only:
        archive = top / 'vm-pair-bundle.tar.gz'
        def anonymous(info):                 # no local user name or id in the archive
            info.uid = info.gid = 0
            info.uname = info.gname = 'root'
            return info
        with tarfile.open(archive, 'w:gz', compresslevel=6) as tar:
            tar.add(out, arcname='vm-pair', filter=anonymous)
        print(f'archive {archive} {archive.stat().st_size / 1e6:.0f} MB sha256 {sha(archive)}')
    print(f'bundle at {out}')


if __name__ == '__main__':
    main()
