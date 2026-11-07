#!/usr/bin/env python3
"""Build separate TLS functions for the persistent native mixed VM adapter.

Does not open sockets, launch parties, or claim native protocol execution.
"""
from pathlib import Path
import argparse, hashlib, json, shutil, subprocess
from datetime import datetime, timezone
ROOT = Path(__file__).resolve().parents[1]
P = str(2**255-19)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('mode',choices=['begin','agreement','binary'])
    parser.add_argument('artifact',type=Path)
    args=parser.parse_args()
    path=args.artifact.resolve()
    backend=ROOT/'.deps/sharing-refresh/MP-SPDZ'
    for module in ['handshake_backend','backend_adapter']:
        shutil.copytree(ROOT/module,backend/module,dirs_exist_ok=True)
    shutil.copy(ROOT/'programs/tls_export.mpc',backend/'Programs/Source/tls_export.mpc')
    command=['python3','compile.py','-M','-X','-P',P,'tls_export',args.mode,str(path)]
    run=subprocess.run(command,cwd=backend,capture_output=True,text=True,check=True,timeout=900)
    report={'checked_utc':datetime.now(timezone.utc).isoformat(),'command':command,
            'compiler_output':run.stdout+run.stderr,'native_mpc_executed':False,
            'artifact_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'exporter_sha256':hashlib.sha256((ROOT/'programs/tls_export.mpc').read_bytes()).hexdigest()}
    destination=ROOT/'benchmarks/results'/('tls-export-'+args.mode+'-'+path.stem+'.json')
    destination.write_text(json.dumps(report,indent=2)+'\n')
    print(run.stdout)

if __name__=='__main__':main()
