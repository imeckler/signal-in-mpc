#!/usr/bin/env python3
"""Export Lean stages and compile their composition in the isolated MPC tree.

Compilation is not native execution. Does not start parties or open sockets.
"""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
from datetime import datetime, timezone
ROOT=Path(__file__).resolve().parents[1]
MODULUS=str(2**255-19)
STAGES=[('x25519-field',),('tls-handshake-secrets',),('tls-application-secrets',),
        ('tls-traffic-keys',),('tls-finished',),('tls-verify-finished',),
        ('tls-open-handshake-record','58'),('tls-seal-record','22','36','0')]

def main():
    backend=ROOT/'.deps/sharing-refresh/MP-SPDZ'
    if not (backend/'compile.py').is_file():
        raise RuntimeError('pinned isolated MP-SPDZ tree is missing')
    subprocess.run(['lake','build','emit_mpc'],cwd=ROOT,check=True)
    directory=ROOT/'artifacts/lean/handshake';directory.mkdir(parents=True,exist_ok=True)
    for args in STAGES:
        with (directory/('-'.join(args)+'.json')).open('w') as output:
            subprocess.run([str(ROOT/'.lake/build/bin/emit_mpc'),*args],stdout=output,check=True)
    for name in ('handshake_backend','backend_adapter'):
        shutil.copytree(ROOT/name,backend/name,dirs_exist_ok=True)
    shutil.copy(ROOT/'programs/handshake_stages.mpc',backend/'Programs/Source/handshake_stages.mpc')
    command=['python3','compile.py','-X','-P',MODULUS,'handshake_stages',str(directory)]
    output=subprocess.run(command,cwd=backend,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,check=True)
    report={'checked_utc':datetime.now(timezone.utc).isoformat(),'command':command,
            'compiler_output':output.stdout,'native_mpc_executed':False,
            'scope':'one mixed VM; secret register composition; fixed public stage shapes; no live controller binding',
            'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in
                [ROOT/'programs/handshake_stages.mpc',*sorted((ROOT/'handshake_backend').glob('*.py')),
                 *sorted(directory.glob('*.json'))]}}
    path=ROOT/'benchmarks/results/lean-handshake-stages-compile.json'
    path.write_text(json.dumps(report,indent=2)+'\n')
    print(output.stdout)

if __name__=='__main__':main()
