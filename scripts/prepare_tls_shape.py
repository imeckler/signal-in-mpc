#!/usr/bin/env python3
"""Trusted local, public-length-only compiler for TLS handshake receive kernels.

Install offline, then pin Worker-Public/tls-shape-{compiler,toolchain.json} in
the worker's boot manifest. Runtime invocation accepts only a wire byte count.
The compiler and interpreter remain unverified; this is not a circuit proof.
Host filesystem integrity during verification/use is an explicit assumption.
"""
import argparse
import fcntl
import hashlib
import json
import os
import platform
from pathlib import Path
import runpy
import shutil
import subprocess
import sys
import tempfile

P = str(2**255 - 19)
PUBLIC = Path('Worker-Public')
CONFIG = PUBLIC / 'tls-shape-toolchain.json'
SOURCE_DIRS = ('Compiler', 'backend_adapter', 'handshake_backend')


def digest(path):
    with path.open('rb') as stream:
        state = hashlib.sha256()
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            state.update(chunk)
        return state.hexdigest()


def sources(base):
    result = []
    for folder in SOURCE_DIRS:
        result.extend(sorted((base / folder).rglob('*.py')))
    result.extend(base / name for name in (
        'compile.py', 'Programs/Source/tls_shape_export.mpc',
        'Worker-Public/tls-shape-emitter', 'Worker-Public/tls_shape_pinning.py'))
    return {str(p.relative_to(base)): digest(p) for p in result}


def atomic_write(path, data):
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as stream:
        temporary = Path(stream.name)
        try:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        except BaseException:
            temporary.unlink(missing_ok=True)
            raise
    os.replace(temporary, path)


def install(backend, emitter):
    root = Path(__file__).resolve().parents[1]
    backend = backend.resolve()
    public = backend / PUBLIC
    public.mkdir(exist_ok=True)
    for module in ('handshake_backend', 'backend_adapter'):
        shutil.copytree(root / module, backend / module, dirs_exist_ok=True)
    # A distinct program name prevents replacement of the fixed boot kernels.
    source = (root / 'programs/tls_export.mpc').read_text()
    (backend / 'Programs/Source/tls_shape_export.mpc').write_text(
        'program.set_security(128)\n' + source)
    shutil.copy2(emitter, public / 'tls-shape-emitter')
    shutil.copy2(root / 'scripts/pin_tls_worker.py', public / 'tls_shape_pinning.py')
    shutil.copy2(__file__, public / 'tls-shape-compiler')
    (public / 'tls-shape-compiler').chmod(0o755)
    executable = Path(sys.executable).resolve()
    config = {'format': 'tls-mpc-shape-toolchain-v1', 'files': sources(backend),
              'python': {'path': str(executable), 'sha256': digest(executable),
                         'version': platform.python_version()}}
    atomic_write(backend / CONFIG, (json.dumps(config, sort_keys=True, indent=2) + '\n').encode())
    print('Pin Worker-Public/tls-shape-compiler and Worker-Public/tls-shape-toolchain.json in the boot manifest.')


def validate_manifest(base, text):
    lines = text.splitlines()
    if not lines or lines[0] != 'tls-mpc-pinned-files-v1':
        raise ValueError('invalid shape cache manifest')
    paths = set()
    for line in lines[1:]:
        expected, path = line.split(' ', 1)
        relative = Path(path)
        if (relative.is_absolute() or '..' in relative.parts or
                len(relative.parts) != 3 or relative.parts[0] != 'Programs' or
                relative.parts[1] not in ('Functions', 'Schedules', 'Bytecode') or path in paths):
            raise ValueError('invalid shape cache path')
        paths.add(path)
        if digest(base / relative) != expected:
            raise ValueError('shape cache digest mismatch')
    if not paths:
        raise ValueError('empty shape cache')


def prepare(size):
    if not 22 <= size <= 16406:
        raise ValueError('AES-GCM wire size must be 22..16406')
    base = Path.cwd()
    config_bytes = CONFIG.read_bytes()
    config = json.loads(config_bytes)
    interpreter = config['python']
    executable = Path(interpreter['path'])
    if not executable.is_absolute() or digest(executable) != interpreter['sha256']:
        raise ValueError('TLS compiler interpreter changed')
    if Path(sys.executable).resolve() != executable:
        # The boot-pinned configuration selects the interpreter. No shell, no
        # caller-supplied executable, and no private inputs are involved.
        os.execv(str(executable), [str(executable), str(Path(__file__).resolve()), str(size)])
    if platform.python_version() != interpreter['version']:
        raise ValueError('TLS compiler Python version changed')
    if config.get('format') != 'tls-mpc-shape-toolchain-v1' or config.get('files') != sources(base):
        raise ValueError('TLS shape toolchain changed')
    identity = hashlib.sha256(config_bytes).hexdigest()
    manifest = PUBLIC / f'tls-shape-{size}.manifest'
    receipt = PUBLIC / f'tls-shape-{size}.receipt.json'
    # Serialize writers, including separate worker processes sharing one cache.
    with (PUBLIC / 'tls-shape.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if receipt.exists():
            record = json.loads(receipt.read_text())
            if record != {'toolchain': identity, 'wire_bytes': size, 'manifest': digest(manifest)}:
                raise ValueError('TLS shape receipt mismatch; provision a fresh cache')
            validate_manifest(base, manifest.read_text())
            return manifest
        stem = f'tls-open-handshake-record-{size}'
        descriptor = f'tls_binary_{stem.replace("-", "_")}-sbv:[{(36+size)*8}x1]-sbv:[{(size-17)*8}x1]'
        with tempfile.TemporaryDirectory(prefix='.tls-shape-build-', dir=base) as directory:
            stage = Path(directory)
            for folder in SOURCE_DIRS:
                (stage / folder).symlink_to(base / folder, target_is_directory=True)
            shutil.copy2(base / 'compile.py', stage / 'compile.py')
            (stage / 'Programs/Source').mkdir(parents=True)
            shutil.copy2(base / 'Programs/Source/tls_shape_export.mpc', stage / 'Programs/Source/tls_shape_export.mpc')
            (stage / PUBLIC).mkdir()
            artifact = PUBLIC / (stem + '.json')
            with (stage / artifact).open('wb') as output:
                subprocess.run([str(base / PUBLIC / 'tls-shape-emitter'), 'tls-open-handshake-record', str(size)],
                               stdout=output, check=True, timeout=900)
            image = json.loads((stage / artifact).read_bytes())
            if (image['format'] != 'tls-mpc-aig-v1' or image['name'] != 'tls-open-handshake-record' or
                    image['input_bits'] != (36+size)*8 or len(image['outputs']) != (size-17)*8):
                raise ValueError('Lean artifact shape mismatch')
            environment = dict(os.environ, PYTHONHASHSEED='0', PYTHONDONTWRITEBYTECODE='1')
            for key in ('PYTHONPATH', 'PYTHONHOME'):
                environment.pop(key, None)
            # Relative paths make descriptors and schedules independent of the
            # host checkout/cache location, so honest parties can agree hashes.
            subprocess.run([sys.executable, '-B', 'compile.py', '-M', '-X', '-P', P,
                            'tls_shape_export', 'binary-packed', str(artifact)], cwd=stage,
                           env=environment, stdout=sys.stderr, check=True, timeout=900)
            build = runpy.run_path(str(base / PUBLIC / 'tls_shape_pinning.py'))['build']
            text = build(stage, [descriptor])
            validate_manifest(stage, text)
            # No published file may ever be replaced with different bytes.
            for line in text.splitlines()[1:]:
                expected, path = line.split(' ', 1)
                destination = base / path
                if destination.exists():
                    if digest(destination) != expected:
                        raise ValueError('immutable TLS shape collision')
                else:
                    atomic_write(destination, (stage / path).read_bytes())
            validate_manifest(base, text)
            atomic_write(manifest, text.encode())
            record = {'toolchain': identity, 'wire_bytes': size, 'manifest': digest(manifest)}
            atomic_write(receipt, (json.dumps(record, sort_keys=True) + '\n').encode())
        return manifest


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('wire_bytes', nargs='?', type=int)
    parser.add_argument('--install', type=Path)
    parser.add_argument('--emitter', type=Path)
    args = parser.parse_args()
    if args.install is not None:
        if args.emitter is None or args.wire_bytes is not None:
            parser.error('--install requires --emitter and no wire size')
        install(args.install, args.emitter)
    elif args.wire_bytes is None or args.emitter is not None:
        parser.error('expected wire byte count')
    else:
        prepare(args.wire_bytes)


if __name__ == '__main__':
    main()
