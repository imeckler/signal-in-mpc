#!/usr/bin/env python3
"""Compile actual Lean application/parser artifacts to isolated mixed-VM functions.

No live worker pins are changed. No native MPC execution or secret input.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
BACKEND = ROOT/'.deps/sharing-refresh/MP-SPDZ'
CACHE = ROOT/'.deps/sharing-refresh/tls-post-handshake-compile'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    subprocess.run(['lake','build','emit_mpc'],cwd=ROOT,check=True)
    CACHE.mkdir(exist_ok=True)
    if not (CACHE/'Compiler').exists():
        (CACHE/'Compiler').symlink_to(BACKEND/'Compiler', target_is_directory=True)
    shutil.copy2(BACKEND/'compile.py',CACHE/'compile.py')
    for folder in ('Source','Functions','Bytecode','Schedules'):
        (CACHE/'Programs'/folder).mkdir(parents=True,exist_ok=True)
    for module in ('backend_adapter','handshake_backend'):
        shutil.copytree(ROOT/module,CACHE/module,dirs_exist_ok=True)
    source = CACHE/'Programs/Source/tls_posthandshake_export.mpc'
    source.write_text('program.set_security(128)\n'+(ROOT/'programs/tls_export.mpc').read_text())
    python = json.loads((BACKEND/'Worker-Public/tls-shape-toolchain.json').read_text())['python']['path']
    rows = []
    for mode, size in [('tls-route-application',64),('tls-post-handshake',64),('tls-open-application-record',27)]:
        artifact = CACHE/f'{mode}-{size}.json'
        with artifact.open('wb') as out:
            subprocess.run([str(ROOT/'.lake/build/bin/emit_mpc'),mode,str(size)],cwd=ROOT,stdout=out,check=True)
        command = [python,'-B','compile.py','-M','-X','-P',str(2**255-19),
                   'tls_posthandshake_export','binary-packed',artifact.name]
        start = time.monotonic()
        run = subprocess.run(command,cwd=CACHE,capture_output=True,text=True,timeout=900)
        row = {'mode':mode,'size':size,'command':command,'exit_code':run.returncode,
               'elapsed_seconds':time.monotonic()-start,'compiler_output':run.stdout+run.stderr,
               'artifact_sha256':digest(artifact)}
        rows.append(row)
        if run.returncode:
            print(row['compiler_output'])
            raise RuntimeError('MPC compilation failed')
        print(json.dumps({k:v for k,v in row.items() if k!='compiler_output'}),flush=True)
    sources = [ROOT/'TlsMpc/TlsApplicationRoute.lean',ROOT/'TlsMpc/TlsPostHandshake.lean',ROOT/'Main.lean',ROOT/'programs/tls_export.mpc',Path(__file__).resolve(),
               CACHE/'compile.py',source,*sorted((CACHE/'Compiler').rglob('*.py')),
               *sorted((CACHE/'backend_adapter').rglob('*.py')),*sorted((CACHE/'handshake_backend').rglob('*.py'))]
    products = [p for folder in ('Functions','Bytecode','Schedules')
                for p in (CACHE/'Programs'/folder).rglob('*') if p.is_file()]
    report = {'checked_at_utc':datetime.now(timezone.utc).isoformat(),'profiles':rows,
              'native_mpc_executed':False,'security_parameter':128,'modulus':str(2**255-19),
              'python':{'path':python,'sha256':digest(Path(python))},
              'source_sha256':{str(p.relative_to(ROOT)):digest(p) for p in sources},
              'products_sha256':{str(p.relative_to(ROOT)):digest(p) for p in products}}
    (ROOT/'benchmarks/results/tls-post-handshake-compilation.json').write_text(json.dumps(report,indent=2)+'\n')


if __name__ == '__main__':
    main()
