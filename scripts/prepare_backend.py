#!/usr/bin/env python3
"""Fetch pinned benchmark dependencies and build native backends locally.

Requires Python 3.12+, curl, make, a C++20 compiler, GMP, libsodium, Boost,
and OpenSSL 3 development libraries. Does not install system packages.
All generated files, including local test certificates, stay under .deps/.
"""

import argparse
import hashlib
import json
from pathlib import Path
import platform
import shutil
import subprocess
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[1]
DEPS = ROOT / '.deps'


def install_archive(name, url, digest, destination, offline):
    archive = DEPS / f'{name}.tar.gz'
    if not archive.exists():
        if offline:
            raise RuntimeError(f'missing cached archive: {archive}')
        # Download to a distinct temporary file so a failed fetch never creates
        # a cache entry that looks complete on a subsequent invocation.
        temporary = archive.with_suffix('.download')
        subprocess.run(['curl', '--fail', '--location', '--silent', '--show-error',
                        url, '-o', str(temporary)], check=True)
        temporary.replace(archive)
    actual = hashlib.sha256(archive.read_bytes()).hexdigest()
    if actual != digest:
        raise RuntimeError(f'archive digest mismatch: {archive}; expected {digest}, got {actual}')
    with tarfile.open(archive) as source:
        prefix = source.getmembers()[0].name.split('/')[0]
        if destination.exists():
            # Reuse builds, but verify every regular source file against the
            # pinned archive. Additional generated files are intentionally OK.
            for member in source.getmembers():
                if not member.isfile():
                    continue
                relative = Path(member.name).relative_to(prefix)
                target = destination / relative
                if not target.is_file() or target.read_bytes() != source.extractfile(member).read():
                    raise RuntimeError(f'installed dependency differs from pinned source: {target}')
        else:
            with tempfile.TemporaryDirectory(dir=DEPS) as staging:
                source.extractall(staging, filter='data')
                destination.parent.mkdir(parents=True, exist_ok=True)
                (Path(staging) / prefix).rename(destination)
    print(f'verified {name}: {digest}', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--offline', action='store_true', help='require cached source archives')
    parser.add_argument('--jobs', type=int, default=4)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('jobs must be positive')
    DEPS.mkdir(exist_ok=True)
    manifest = json.loads((ROOT / 'benchmarks/config/dependencies.json').read_text())
    backend = DEPS / 'MP-SPDZ'
    pinned = manifest['mp_spdz']
    install_archive('mp-spdz-v0.4.4', pinned['source_archive_url'],
                    pinned['source_archive_sha256'], backend, args.offline)
    for module in manifest['mp_spdz_submodules']:
        url = f'https://api.github.com/repos/{module["repository"]}/tarball/{module["commit"]}'
        install_archive(module['name'], url, module['archive_sha256'],
                        backend / module['destination'], args.offline)
    configuration = 'GDEBUG =\n'
    if platform.system() == 'Darwin':
        brew = Path(subprocess.check_output(['brew', '--prefix'], text=True).strip())
        openssl = next((brew / 'opt' / name for name in ['openssl@3.5', 'openssl@3.6', 'openssl@3']
                        if (brew / 'opt' / name / 'include/openssl/ssl.h').exists()), None)
        if openssl is None:
            raise RuntimeError('OpenSSL 3 development files are required')
        configuration += f'BREW_CFLAGS = -I{openssl}/include -I{brew}/include\n'
        configuration += f'BREW_LDLIBS = -L{openssl}/lib -L{brew}/lib\n'
        configuration += 'MY_CFLAGS += -Wno-error=deprecated-literal-operator\n'
    config = backend / 'CONFIG.mine'
    if not config.exists() or config.read_text() != configuration:
        config.write_text(configuration)
    subprocess.run(['make', f'-j{args.jobs}', 'malicious-ccd-party.x',
                    'malicious-rep-bin-party.x'], cwd=backend, check=True)
    player_data = backend / 'Player-Data'
    if not all((player_data / f'P{i}.{extension}').exists()
               for i in range(5) for extension in ('pem', 'key')):
        subprocess.run(['bash', 'Scripts/setup-ssl.sh', '5'], cwd=backend, check=True)
    shutil.copy2(ROOT / 'benchmarks/programs/crypto.mpc', backend / 'Programs/Source/crypto.mpc')
    print('Native MPC backends are ready. Networking is required only for MPC runs.')


if __name__ == '__main__':
    main()
