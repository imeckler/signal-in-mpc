#!/usr/bin/env python3
"""Test native worker rejection paths that occur BEFORE Names/socket creation."""
from pathlib import Path
import tempfile,subprocess,json,hashlib
ROOT=Path(__file__).resolve().parents[1]
WORKER=ROOT/'.deps/sharing-refresh/tls-worker'

def main():
    cases=[]
    with tempfile.TemporaryDirectory(prefix='tls-worker-startup-') as tmp:
        directory=Path(tmp);bad=directory/'bad.manifest';bad.write_text('unsupported manifest\n')
        base=['0','nonexistent-public-hosts','9000',str(bad),'00'*32]
        tests=[('bad manifest',base),('missing manifest',base[:3]+[str(directory/'missing')]+base[4:]),
               ('invalid party',['5']+base[1:]),('invalid port',base[:2]+['0']+base[3:]),
               ('invalid session ID',base[:4]+['AA'*32])]
        for name,args in tests:
            result=subprocess.run([str(WORKER),*args],input=b'',capture_output=True,timeout=10)
            assert result.returncode==1,(name,result.returncode)
            assert result.stdout==bytes([1,0,0,0,0]),(name,result.stdout)
            assert result.stderr==b'TLS MPC worker aborted\n',(name,result.stderr)
            cases.append({'case':name,'passed':True})
        result=subprocess.run([str(WORKER)],capture_output=True,timeout=10)
        assert result.returncode==2 and result.stdout==b''
        cases.append({'case':'usage before startup','passed':True})
    report={'cases':cases,'native_mpc_executed':False,'sockets_opened':False,
            'scope':'startup rejection paths preceding networking; stdout framing isolation',
            'worker_sha256':hashlib.sha256(WORKER.read_bytes()).hexdigest(),
            'source_sha256':hashlib.sha256((ROOT/'handshake_backend/worker_main.cpp').read_bytes()).hexdigest()}
    (ROOT/'benchmarks/results/tls-worker-startup-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'passed':len(cases),'sockets_opened':False}))
if __name__=='__main__':main()
