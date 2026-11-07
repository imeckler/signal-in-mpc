#!/usr/bin/env python3
"""Fresh packed TLS shape compilation with exact toolchain provenance.

No native MPC execution. Keep the generated cache for later native probes.
"""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
BACKEND = ROOT/'.deps/sharing-refresh/MP-SPDZ'
CACHE = ROOT/'.deps/sharing-refresh/tls-packed-shape-test'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('sizes', nargs='+', type=int)
    parser.add_argument('--cache', type=Path, default=CACHE)
    args = parser.parse_args()
    cache = args.cache.resolve()
    cache.mkdir(exist_ok=True)
    compiler = cache/'Compiler'
    if not compiler.exists():
        compiler.symlink_to(BACKEND/'Compiler', target_is_directory=True)
    shutil.copy2(BACKEND/'compile.py', cache/'compile.py')
    for folder in ('Source', 'Functions', 'Bytecode', 'Schedules'):
        (cache/'Programs'/folder).mkdir(parents=True, exist_ok=True)
    python = json.loads((BACKEND/'Worker-Public/tls-shape-toolchain.json').read_text())['python']['path']
    if not (cache/'Worker-Public/tls-shape-toolchain.json').exists():
        subprocess.run([python, str(ROOT/'scripts/prepare_tls_shape.py'), '--install', str(cache),
                        '--emitter', str(ROOT/'.lake/build/bin/emit_mpc')], check=True)
    for size in args.sizes:
        start = time.monotonic()
        run = subprocess.run([python, 'Worker-Public/tls-shape-compiler', str(size)],
                             cwd=cache, capture_output=True, text=True, timeout=1900)
        elapsed = time.monotonic()-start
        manifest = cache/f'Worker-Public/tls-shape-{size}.manifest'
        report = {'wire_bytes': size, 'elapsed_seconds': elapsed, 'exit_code': run.returncode,
                  'compiler_output': run.stdout+run.stderr, 'native_mpc_executed': False,
                  'cache': str(cache),
                  'toolchain_sha256': hashlib.sha256((cache/'Worker-Public/tls-shape-toolchain.json').read_bytes()).hexdigest(),
                  'manifest_sha256': hashlib.sha256(manifest.read_bytes()).hexdigest() if manifest.exists() else None}
        (ROOT/f'benchmarks/results/{cache.name}-{size}-checks.json').write_text(json.dumps(report, indent=2)+'\n')
        print(json.dumps({key:value for key,value in report.items() if key!='compiler_output'}), flush=True)
        if run.returncode != 0:
            print(run.stderr, flush=True)
            raise SystemExit(run.returncode)


if __name__ == '__main__':
    main()
