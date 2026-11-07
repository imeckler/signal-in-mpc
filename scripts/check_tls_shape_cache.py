#!/usr/bin/env python3
"""Public compiler/cache + native extension checks; no MPC or TCP execution."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import tempfile
from pin_tls_worker import build

ROOT = Path(__file__).resolve().parents[1]
BACKEND = ROOT / '.deps/sharing-refresh/MP-SPDZ'
PROBE = BACKEND.parent / 'tls-shape-probe'


def main():
    cases = []
    with tempfile.TemporaryDirectory(prefix='tls-shape-checks-') as temporary:
        base = Path(temporary)
        public = base / 'Worker-Public'
        public.mkdir()
        descriptor = 'tls_binary_tls_open_handshake_record_38-sbv:[592x1]-sbv:[168x1]'
        extension = (BACKEND / 'Worker-Public/tls-shape-38.manifest').read_text()
        for line in extension.splitlines()[1:]:
            _, relative = line.split(' ', 1)
            path = base / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(BACKEND / relative, path)
        manifest = public / 'tls-shape-38.manifest'
        manifest.write_text(extension)
        # A trusted local fixture compiler records its only public argument and
        # checks an explicitly inheritable descriptor was closed by spawn.
        with (base / 'private-fd-sentinel').open('w') as sentinel:
            os.set_inheritable(sentinel.fileno(), True)
            helper = public / 'tls-shape-compiler'
            helper.write_text('#!/usr/bin/env python3\nimport os,sys\nfrom pathlib import Path\n'
                'assert sys.argv[1:] == ["38"]\n'
                f'try:\n os.fstat({sentinel.fileno()})\nexcept OSError:\n pass\nelse:\n raise RuntimeError("private descriptor leaked")\n'
                'with Path("calls").open("a") as out: out.write("38\\n")\n')
            helper.chmod(0o755)
            (public / 'tls-shape-toolchain.json').write_text('{}\n')
            boot = build(base, [], ['Worker-Public/tls-shape-compiler', 'Worker-Public/tls-shape-toolchain.json'])
            boot_path = base / 'boot.manifest'
            boot_path.write_text(boot)

            def check(name, accept, mode='accept', size=38):
                run = subprocess.run([str(PROBE), str(boot_path), str(size), mode], cwd=base,
                                     capture_output=True, text=True, pass_fds=(sentinel.fileno(),), timeout=30)
                assert (run.returncode == 0) == accept, (name, run.stdout, run.stderr)
                if accept:
                    assert run.stdout.strip() == '1 agreements', run.stdout
                cases.append({'case': name, 'accepted': accept})

            check('spawn closes private fd; extension installed after agreement; second call reuses', True)
            assert (base / 'calls').read_text() == '38\n'
            check('party disagreement rejects before registration', False, mode='reject')
            for size in (0, 21, 16407, 16646):
                check('invalid public size ' + str(size), False, size=size)
            original = helper.read_bytes()
            helper.write_bytes(original + b'# modification\n')
            check('changed compiler rejected', False)
            helper.write_bytes(original)
            config = public / 'tls-shape-toolchain.json'
            config.write_text('{"changed":true}\n')
            check('changed toolchain rejected', False)
            config.write_text('{}\n')
            lines = extension.splitlines()
            for line in lines[1:]:
                _, path = line.split(' ', 1)
                manifest.write_text('\n'.join(x for x in lines if x != line) + '\n')
                check('missing closure entry ' + path, False)
            manifest.write_text(extension)
            extra = base / 'Programs/Bytecode/unrelated.bc'
            extra.write_bytes(b'unrelated')
            manifest.write_text(extension + hashlib.sha256(extra.read_bytes()).hexdigest() + ' Programs/Bytecode/unrelated.bc\n')
            check('unrelated extension file rejected', False)
            manifest.write_text(extension)
            bytecode = base / lines[1].split(' ', 1)[1]
            bytecode_original = bytecode.read_bytes()
            bytecode.write_bytes(bytecode_original + b'changed')
            check('changed bytecode rejected', False)
            bytecode.write_bytes(bytecode_original)
            # Simulate a local compiler attempting to replace an already
            # boot-pinned dependency, while leaving the new descriptor absent.
            relative = lines[1].split(' ', 1)[1]
            replacement = bytecode_original + b'replacement'
            manifest.write_text(extension.replace(lines[1].split(' ', 1)[0], hashlib.sha256(replacement).hexdigest()))
            helper.write_bytes(original + f'Path({relative!r}).write_bytes({replacement!r})\n'.encode())
            boot_path.write_text(build(base, [], ['Worker-Public/tls-shape-compiler','Worker-Public/tls-shape-toolchain.json']) + lines[1] + '\n')
            check('extension cannot replace boot-pinned bytecode', False)
    # This uses the REAL installed Lean emitter / MP-SPDZ compiler cache, not
    # the subprocess fixture. The existing receipt must be validated unchanged.
    receipt = BACKEND / 'Worker-Public/tls-shape-38.receipt.json'
    before = receipt.read_bytes()
    subprocess.run(['python3', 'Worker-Public/tls-shape-compiler', '38'], cwd=BACKEND, check=True, timeout=30)
    assert receipt.read_bytes() == before
    cases.append({'case': 'real compiler cache reuse validates unchanged receipt', 'accepted': True})
    source_names = ['scripts/prepare_tls_shape.py', 'scripts/check_tls_shape_cache.py',
                    'handshake_backend/ShapeCompiler.h', 'handshake_backend/PinnedPrograms.h',
                    'handshake_backend/shape_compiler_probe.cpp', 'handshake_backend/NativeCollective.h',
                    'handshake_backend/NativeDispatch.h', 'handshake_backend/worker_main.cpp']
    report = {'cases': cases, 'native_mpc_executed': False, 'collective_agreement_executed': False,
              'actual_public_shape_compiled': 38, 'compiler_manifest_sha256': hashlib.sha256(extension.encode()).hexdigest(),
              'source_sha256': {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in source_names}}
    (ROOT/'benchmarks/results/tls-shape-cache-checks.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'passed': len(cases), 'native_mpc_executed': False}))


if __name__ == '__main__':
    main()
