"""Bounded honest-execution component smoke plus fail-closed negative control.

Fixture driver knows dummy logical inputs. Party executables receive only one
XOR share and Alice's private output pad; no sender secret is reconstructed in
either party path. Driver reconstructs fixture outputs only for verification.
"""
import hashlib
import json
import os
import pathlib
import random
import subprocess
import tempfile
import time
from convert import convert, write

ROOT=pathlib.Path(__file__).resolve().parents[2]
BASE=ROOT/'.deps/two-party-comparison'

def bits(data):return [bool((b>>i)&1) for b in data for i in range(7,-1,-1)]
def packed(data):return bytes(sum(int(x)<<(7-j) for j,x in enumerate(data[i:i+8])) for i in range(0,len(data),8))
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def run_case(name,path,logical,expected,port,corrupt=False):
    image=json.loads(path.read_text())
    circuit=convert(image)
    work=pathlib.Path(tempfile.mkdtemp(prefix=name+'-',dir=BASE))
    write(circuit,work/'circuit.txt')
    rng=random.Random(190113)
    source=bits(logical)
    bob=[bool(rng.getrandbits(1)) for _ in source]
    alice=[x^y for x,y in zip(source,bob)]
    pads=[bool(rng.getrandbits(1)) for _ in range(circuit['n3'])]
    (work/'alice.bin').write_bytes(bytes(alice+pads))
    (work/'bob.bin').write_bytes(bytes(bob))
    env=dict(os.environ,DYLD_LIBRARY_PATH=str(BASE/'install/lib'))
    children=[]; files=[]; start=time.monotonic()
    try:
        for party,who in [(1,'alice'),(2,'bob')]:
            log=open(work/(who+'.log'),'wb');files.append(log)
            childenv=dict(env)
            if corrupt and party==2:childenv['EMP_TEST_CORRUPT_OUTPUT_KEY']='1'
            children.append(subprocess.Popen([str(BASE/'emp-worker'),str(party),str(port),str(work/'circuit.txt'),
                str(work/(who+'.bin')),str(work/(who+'.output')),str(work/(who+'.json'))],
                env=childenv,stdout=log,stderr=subprocess.STDOUT))
        deadline=start+180
        for child in children:child.wait(timeout=max(1,deadline-time.monotonic()))
    finally:
        for child in children:
            if child.poll() is None:child.kill()
            child.wait()
        for log in files:log.close()
    codes=[c.returncode for c in children]
    if corrupt:
        passed=codes[1]==4 and not (work/'bob.output').exists()
    else:
        actual=(work/'bob.output').read_bytes() if (work/'bob.output').exists() else b''
        passed=codes==[0,0] and packed([bool(x)^y for x,y in zip(actual,pads)])==expected and len(actual)==len(pads)
    metrics=[json.loads((work/(who+'.json')).read_text()) if (work/(who+'.json')).exists() else None for who in ('alice','bob')]
    if not corrupt and passed:
        assert metrics[0]['sent_bytes']==metrics[1]['received_bytes']
        assert metrics[1]['sent_bytes']==metrics[0]['received_bytes']
    result={'name':name,'passed':passed,'corruption_control':corrupt,'exit_codes':codes,
            'controller_wall_seconds':time.monotonic()-start,'directory':str(work),
            'logical_input_bits':len(source),'output_bits':len(pads),
            'source_sha256':digest(path),'bristol_sha256':digest(work/'circuit.txt'),
            'and_gates':sum(g[0]=='AND' for g in circuit['gates']),'parties':metrics}
    if not passed:raise RuntimeError(json.dumps(result))
    return result

if __name__=='__main__':
    aes=ROOT/'.deps/reference-fixslice-cost-v1/reference-1x1.json'
    sha=ROOT/'.deps/sha-backend-profiles/reference-block.json'
    key=bytes(range(32));plain=bytes(range(16))
    ciphertext=subprocess.run(['/opt/homebrew/opt/openssl@3.5/bin/openssl','enc','-aes-256-ecb','-K',key.hex(),'-nopad'],input=plain,stdout=subprocess.PIPE,check=True).stdout
    initial=bytes.fromhex('6a09e667bb67ae853c6ef372a54ff53a510e527f9b05688c1f83d9ab5be0cd19')
    block=b'\x80'+bytes(63)
    results=[run_case('aes256',aes,key+plain,ciphertext,31300),
             run_case('sha256-empty',sha,initial+block,hashlib.sha256(b'').digest(),31310),
             run_case('reject-output-key',aes,key+plain,ciphertext,31320,True)]
    report={'passed':all(r['passed'] for r in results),'scope':'loopback component smoke; not full Signal/TLS throughput',
            'security':'legacy AG2PC nominal40-bit statistical profile; local40-bit comparison-mask correction; full parameter composition unvalidated; failclosed overlay6branches',
            'build':json.loads((BASE/'emp-build.json').read_text()),'results':results}
    target=ROOT/'benchmarks/TwoPartyComparisonWork/emp-smoke-report.json'
    target.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'passed':report['passed'],'report':str(target),'cases':len(results)}))
