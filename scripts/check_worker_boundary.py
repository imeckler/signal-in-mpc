#!/usr/bin/env python3
"""Build the native boundary and test its public parser and Lean pipe codec.

No native MPC parties are launched. Pipe peers use public echo fixtures only.
"""
from pathlib import Path
import hashlib, json, subprocess, tempfile
from datetime import datetime, timezone
ROOT=Path(__file__).resolve().parents[1]

def run(command, **kwargs):
    result=subprocess.run(command,cwd=ROOT,text=True,capture_output=True,timeout=180,**kwargs)
    if result.returncode:
        raise RuntimeError(f'{command}:\n{result.stdout}\n{result.stderr}')
    return result

def main():
    backend=ROOT/'.deps/sharing-refresh/MP-SPDZ'
    native=subprocess.run(['make','-f',str(ROOT/'handshake_backend/Makefile'),'TLS_ROOT='+str(ROOT/'handshake_backend'),
                           '../tls-worker-build','../tls-worker'],
                          cwd=backend,check=True,text=True,capture_output=True,timeout=180)
    run(['lake','build','worker_pipe_fixture'])
    checks=[]
    with tempfile.TemporaryDirectory(prefix='tls-worker-public-') as tmp:
        directory=Path(tmp)
        for name in ['session_policy_checks','application_policy_checks','public_protocol_checks','transport_checks','pipe_fixture','owned_secrets_checks']:
            run(['c++','-std=c++20','-O2','-pthread','-fsanitize=address,undefined',
                 '-I/opt/homebrew/include','-L/opt/homebrew/lib',
                 str(ROOT/'handshake_backend'/f'{name}.cpp'),'-lsodium','-o',str(directory/name)])
        for name in ['session_policy_checks','application_policy_checks','public_protocol_checks','transport_checks','owned_secrets_checks']:
            result=run([str(directory/name)])
            checks.append({'test':name,'output':result.stdout.strip()})
        for mode in ['valid','truncated','oversized','rejected','concurrent','duplex']:
            result=run([str(ROOT/'.lake/build/bin/worker_pipe_fixture'),str(directory/'pipe_fixture'),mode])
            checks.append({'test':'Lean/C++ pipe '+mode,'output':result.stdout.strip()})
        result=run(['lake','env','lean','--run','WorkerApplicationFixture.lean'])
        checks.append({'test':'Lean application RPC contract','output':result.stdout.strip()})
    sources=[*sorted((ROOT/'handshake_backend').glob('*.h')),
             ROOT/'TlsMpc/TlsWorker.lean',ROOT/'TlsMpc/TlsWorkerPipe.lean',ROOT/'WorkerPipeFixture.lean',
             ROOT/'WorkerApplicationFixture.lean',ROOT/'handshake_backend/application_policy_checks.cpp',
             ROOT/'handshake_backend/owned_secrets_checks.cpp',
             ROOT/'handshake_backend/worker_build.cpp',ROOT/'handshake_backend/session_policy_checks.cpp',
             ROOT/'handshake_backend/worker_main.cpp',ROOT/'handshake_backend/Makefile',
             ROOT/'handshake_backend/public_protocol_checks.cpp',ROOT/'handshake_backend/pipe_fixture.cpp',ROOT/'handshake_backend/transport_checks.cpp',
             Path(__file__).resolve()]
    report={'checked_utc':datetime.now(timezone.utc).isoformat(),'native_adapter_build':True,'native_executable_build':True,
            'checks':checks,'sanitizers':['address','undefined'],
            'native_mpc_executed':False,'collective_network_agreement_executed':False,
            'operational_erasure_implemented':False,
            'scope':'compile/link native dispatch/executable; public parsing/state checks; actual Lean/C++ concurrent and duplex pipe interop',
            'application_execution_enabled':False,
            'products_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in [backend.parent/'tls-worker-build',backend.parent/'tls-worker']},
            'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}}
    path=ROOT/'benchmarks/results/tls-worker-boundary-checks.json'
    path.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'checks':checks,'native_mpc_executed':False,'report':str(path.relative_to(ROOT))}))

if __name__=='__main__':main()
