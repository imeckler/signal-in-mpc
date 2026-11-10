#!/usr/bin/env python3
"""Check the per-contact state kernels against independent references.

contact-key: SHA-256("CONTACT_STATE_KEY_V1" || ((a + b) mod r) as 32 LE bytes),
with r the Pallas scalar order, on random and boundary share pairs.
contact-seal / contact-open: AES-128-CTR as GCM lays out its counters, the key
check value, round trip, and rejection under a wrong key.
"""
import hashlib,json,random,subprocess,sys
from pathlib import Path
from cryptography.hazmat.primitives.ciphers import Cipher,algorithms,modes
HERE=Path(__file__).resolve().parent
R=0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001
def kernel(*args):
    out=subprocess.run([sys.executable,str(HERE/'circuit_cache.py'),'kernel',*map(str,args)],check=True,capture_output=True).stdout.decode().split()
    lines=Path(out[0]).read_text().split('\n');n,count,width=map(int,lines[1].split())
    if lines[0]!='EMP_HYBRID_BOOL_V1' or n!=int(out[2]) or width!=int(out[3]):raise ValueError('flat header')
    gates=[row.split() for row in lines[2:2+count]];outputs=list(map(int,lines[2+count].split()[1:]))
    fields={};offset={'I':0,'O':0}
    for row in Path(out[4]).read_text().split('\n')[1:]:
        f=row.split()
        if len(f)>=3:fields[(f[0],f[1])]=(offset[f[0]],int(f[2]));offset[f[0]]+=int(f[2])
    def run(**values):
        wires=[0]*n
        for name,data in values.items():
            start,bits=fields[('I',name)]
            if bits!=8*len(data):raise ValueError('input size '+name)
            for i in range(bits):wires[start+i]=(data[i//8]>>(i%8))&1
        for g in gates:wires.append(1-wires[int(g[1])] if g[0]=='N' else (wires[int(g[1])]^wires[int(g[2])] if g[0]=='X' else wires[int(g[1])]&wires[int(g[2])]))
        bits=[wires[o] for o in outputs];result={}
        for (kind,name),(start,size) in fields.items():
            if kind=='O':result[name]=bytes(sum(bits[start+8*i+j]<<j for j in range(8)) for i in range(size//8))
        return result
    return run,sum(g[0]=='A' for g in gates)
def ecb(key,block):
    e=Cipher(algorithms.AES(key),modes.ECB()).encryptor();return e.update(block)+e.finalize()
def nonce(iv,version):return bytes(a^b for a,b in zip(iv,bytes(4)+version))
def ctr(key,iv,version,data):
    n=nonce(iv,version);return bytes(d^ecb(key,n+(2+i//16).to_bytes(4,'big'))[i%16] for i,d in enumerate(data))
rng=random.Random(20261110);report={}
key_kernel,ands=key_kernel_info=kernel('contact-key');report['contact-key']=dict(and_gates=ands)
def expected_traffic(a,b):
    digest=hashlib.sha256(b'CONTACT_STATE_KEY_V1'+((a+b)%R).to_bytes(32,'little')).digest();return bytes(32)+digest[:28]
cases=[(0,0),(R-1,R-1),(R-1,1),(1,R-2),(R-1,0)]+[(rng.randrange(R),rng.randrange(R)) for _ in range(40)]
for a,b in cases:
    if key_kernel(shareA=a.to_bytes(32,'little'),shareB=b.to_bytes(32,'little'))['traffic']!=expected_traffic(a,b):raise AssertionError('contact-key %x %x'%(a,b))
report['contact-key']['cases_checked']=len(cases)
for size in (1,16,97):
    seal,seal_ands=kernel('contact-seal',size);open_,open_ands=kernel('contact-open',size)
    for _ in range(4):
        traffic=expected_traffic(rng.randrange(R),rng.randrange(R));key,iv=traffic[32:48],traffic[48:60]
        version=rng.randrange(2**63).to_bytes(8,'big');content=rng.randbytes(size)
        out=seal(traffic=traffic,version=version,content=content);check=ecb(key,nonce(iv,b'\xff'*8)+(1).to_bytes(4,'big'))
        if out['ciphertext']!=ctr(key,iv,version,content) or out['check']!=check:raise AssertionError('contact-seal')
        back=open_(traffic=traffic,version=version,ciphertext=out['ciphertext'],check=check)
        if back['accepted']!=b'\xff' or back['content']!=content:raise AssertionError('contact-open')
        wrong=bytearray(traffic);wrong[40]^=1
        bad=open_(traffic=bytes(wrong),version=version,ciphertext=out['ciphertext'],check=check)
        if bad['accepted']!=b'\x00' or any(bad['content']):raise AssertionError('contact-open accepted a wrong key')
    report['contact-seal %d'%size]=dict(and_gates=seal_ands);report['contact-open %d'%size]=dict(and_gates=open_ands)
(HERE/'contact-kernels-report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
