#!/usr/bin/env python3
"""Compile in an independent location; compare bytes, not just circuit costs."""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import tempfile
from pin_tls_worker import build

ROOT = Path(__file__).resolve().parents[1]
BACKEND = ROOT/'.deps/sharing-refresh/MP-SPDZ'


def main():
    config = json.loads((BACKEND/'Worker-Public/tls-shape-toolchain.json').read_text())
    with tempfile.TemporaryDirectory(prefix='tls-shape-reproducibility-') as temporary:
        base = Path(temporary)
        for relative in [*config['files'], 'Worker-Public/tls-shape-compiler', 'Worker-Public/tls-shape-toolchain.json']:
            target = base/relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(BACKEND/relative, target)
        for directory in ('Functions','Bytecode','Schedules'):
            (base/'Programs'/directory).mkdir(exist_ok=True)
        subprocess.run(['python3','Worker-Public/tls-shape-compiler','38'], cwd=base, check=True, timeout=1000)
        original = (BACKEND/'Worker-Public/tls-shape-38.manifest').read_bytes()
        reproduced = (base/'Worker-Public/tls-shape-38.manifest').read_bytes()
        assert reproduced == original, 'compiler artifacts depend on checkout/cache location'
        # The actual native spawn path must accept the real compiler result.
        boot = base/'boot.manifest'
        boot.write_text(build(base, [], ['Worker-Public/tls-shape-compiler','Worker-Public/tls-shape-toolchain.json']))
        run = subprocess.run([str(BACKEND.parent/'tls-shape-probe'),str(boot),'38','accept'], cwd=base,
                             check=True, capture_output=True, text=True, timeout=30)
        assert run.stdout.strip() == '1 agreements', run.stdout
        # Replacing both cached bytecode and its manifest is outside the trusted
        # host filesystem model. Ordinary cache corruption must fail closed.
        manifest = base/'Worker-Public/tls-shape-38.manifest'
        manifest.write_bytes(original+b'bad\n')
        rejected = subprocess.run(['python3','Worker-Public/tls-shape-compiler','38'], cwd=base,
                                  capture_output=True, text=True, timeout=30)
        assert rejected.returncode != 0 and 'receipt mismatch' in rejected.stderr
        manifest.write_bytes(original)
        source = base/'Programs/Source/tls_shape_export.mpc'
        source.write_text(source.read_text()+'\n# tampered compiler input\n')
        rejected = subprocess.run(['python3','Worker-Public/tls-shape-compiler','38'], cwd=base,
                                  capture_output=True, text=True, timeout=30)
        assert rejected.returncode != 0 and 'toolchain changed' in rejected.stderr
    report = {'independent_location_byte_identical': True, 'actual_native_compiler_spawn_passed': True,
              'cache_corruption_rejected': True, 'toolchain_change_rejected': True,
              'wire_bytes': 38, 'manifest_sha256': hashlib.sha256(original).hexdigest(), 'pinned_python': config['python'],
              'native_mpc_executed': False, 'collective_agreement_executed': False}
    (ROOT/'benchmarks/results/tls-shape-reproducibility-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
