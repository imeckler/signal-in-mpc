#!/usr/bin/env python3
from pathlib import Path
import tempfile,subprocess,hashlib,json
from pin_tls_worker import build
ROOT=Path(__file__).resolve().parents[1]
PROBE=ROOT/'.deps/sharing-refresh/tls-pinned-probe'

def main():
    cases=[]
    with tempfile.TemporaryDirectory(prefix='tls-pinned-worker-') as tmp:
        base=Path(tmp)
        files={'Programs/Functions/probe':b'test\n1\n- 0\n',
               'Programs/Schedules/test.sch':b'1\n2\ntest-0:0 test-1:0\n1 0\n0\n',
               'Programs/Bytecode/test-0.bc':b'public bytecode fixture0',
               'Programs/Bytecode/test-1.bc':b'public bytecode fixture1'}
        for name,data in files.items():p=base/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
        original=build(base,['probe'])
        manifest=base/'manifest.txt'
        def check(name,text,accept=False):
            manifest.write_text(text)
            r=subprocess.run([str(PROBE),str(manifest),'probe'],cwd=base,capture_output=True,text=True,timeout=10)
            assert (r.returncode==0)==accept,(name,r.stdout,r.stderr)
            cases.append({'case':name,'accepted':accept})
        check('valid complete closure',original,True)
        for name,data in files.items():
            (base/name).write_bytes(data+b'!');check('modified '+name,original);(base/name).write_bytes(data)
            text='\n'.join(line for line in original.splitlines() if not line.endswith(' '+name))+'\n'
            check('unlisted '+name,text)
        check('duplicate file',original+original.splitlines()[1]+'\n')
        check('noncanonical digest',original.replace(original.splitlines()[1][:64],'A'*64,1))
        check('path traversal',original+hashlib.sha256(b'').hexdigest()+' Worker-Public/../secret\n')
        check('unknown format',original.replace('tls-mpc-pinned-files-v1','unknown'))
        (base/'Programs/Functions/probe').write_bytes(b'../escape\n1\n- 0\n')
        # Deliberately pin the malformed descriptor to ensure hash equality is
        # insufficient to authorize a traversal through its schedule name.
        text=original.replace(hashlib.sha256(files['Programs/Functions/probe']).hexdigest(),hashlib.sha256((base/'Programs/Functions/probe').read_bytes()).hexdigest())
        check('pinned malformed descriptor',text)
    report={'cases':cases,'native_mpc_executed':False,'scope':'actual native pinned-file parser and function dependency validation',
            'source_sha256':{name:hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in
              ['handshake_backend/PinnedPrograms.h','handshake_backend/pinned_program_probe.cpp','scripts/pin_tls_worker.py','scripts/check_pinned_worker.py']}}
    (ROOT/'benchmarks/results/tls-pinned-worker-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'passed':len(cases),'native_mpc_executed':False}))
if __name__=='__main__':main()
