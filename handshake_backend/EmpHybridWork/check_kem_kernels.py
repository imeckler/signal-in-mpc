#!/usr/bin/env python3
"""Check the KEM encapsulation kernels (TlsMpc/MlKemFastKernels.lean).

This script is a CHECK only. Run it under the guard:

    python3 scripts/guarded.py 10 1500 python3 handshake_backend/EmpHybridWork/check_kem_kernels.py

It
* contains a plain-Python reference of Kyber-1024 (round 3, libsignal key type 8) and ML-KEM-1024
  (FIPS 203): key generation, encapsulation, decapsulation, written independently of the Lean;
* validates that reference against (a) the pinned libcrux 0.0.10 that libsignal links
  (.deps/signal-libcrux-mlkem-oracle-target, built by scripts/check_lean_signal_mlkem.py; skipped with
  a note if the binary is absent), (b) libsignal's own test key pairs
  (.deps/libsignal-v0.106.1/rust/protocol/src/kem/test-data): the public key inside the private key,
  and decapsulation of our ciphertext under libsignal's private key, (c) the `cryptography` package's
  ML-KEM-1024 if the installed version has it;
* lowers every kernel with the Lean executable `kem_kernel_emitter` (cached by the binary's hash),
  evaluates the gate lists in the order of operations of TlsMpc/MlKemFastKernels.lean and compares
  EVERY output field of every kernel with the reference, for both variants;
* runs the existing Lean specification (`Signal.MlKem.encapsulate`, values) and the value instances
  of the stage functions on the same inputs and compares (skip with --no-lean-values: about 30 s each);
* feeds malformed keys (a coefficient of the encoded key at or above q) and failed statuses, and
  requires status 0 with an all-zero ciphertext and secret;
* tries the sampler on streams with too few, exactly enough and late accepted candidates;
* asserts from the layout files that no kernel opens anything.

Nothing is sent to any network service. Writes kem-kernels-report.json next to this file.
"""
import hashlib,json,os,random,subprocess,sys,time
from array import array
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
EMITTER=ROOT/'.lake/build/bin/kem_kernel_emitter'
ORACLE=ROOT/'.deps/signal-libcrux-mlkem-oracle-target/debug/signal-libcrux-mlkem-oracle'
TESTDATA=ROOT/'.deps/libsignal-v0.106.1/rust/protocol/src/kem/test-data'
Q=3329

# ---- circuit evaluation: all test vectors of a batch at once, one bit of a Python integer each ----
KERNELS={}
def kernel(*args):
    key=' '.join(map(str,args))
    if key in KERNELS:return KERNELS[key]
    if not EMITTER.exists():raise SystemExit('build the emitter first: lake build kem_kernel_emitter (under the guard)')
    cache=ROOT/'.deps/emp-hybrid-word-v1/cache'/('kem-'+hashlib.sha256(EMITTER.read_bytes()).hexdigest()[:16]);cache.mkdir(parents=True,exist_ok=True)
    stem=cache/'-'.join(map(str,args));flat,layout,meta=stem.with_suffix('.flat'),stem.with_suffix('.layout'),stem.with_suffix('.json')
    if not (flat.exists() and layout.exists() and meta.exists()):
        out=subprocess.run([str(EMITTER),str(flat)+'.tmp',str(layout)+'.tmp','kernel',*map(str,args)],check=True,capture_output=True,cwd=ROOT).stdout.split()
        os.replace(str(flat)+'.tmp',flat);os.replace(str(layout)+'.tmp',layout)
        meta.write_text(json.dumps(dict(arguments=list(map(str,args)),input_bits=int(out[0]),output_bits=int(out[1]),and_gates=int(out[2]),gates=int(out[3]),sha256=hashlib.sha256(flat.read_bytes()).hexdigest()))+'\n')
    info=json.loads(meta.read_text())
    with open(flat) as f:
        if f.readline().strip()!='EMP_HYBRID_BOOL_V1':raise ValueError('flat header')
        n,count,width=map(int,f.readline().split())
        if n!=info['input_bits'] or width!=info['output_bits']:raise ValueError('flat header')
        kind=bytearray(count);left=array('I',bytes(4*count));right=array('I',bytes(4*count));ands=0
        for i in range(count):
            row=f.readline().split()
            if row[0]=='A':kind[i]=0;left[i]=int(row[1]);right[i]=int(row[2]);ands+=1
            elif row[0]=='X':kind[i]=1;left[i]=int(row[1]);right[i]=int(row[2])
            elif row[0]=='N':kind[i]=2;left[i]=int(row[1])
            else:raise ValueError('gate')
        outputs=list(map(int,f.readline().split()[1:]))
    if ands!=info['and_gates'] or len(outputs)!=width:raise ValueError('flat counts')
    fields={};offset={'I':0,'O':0};opened={}
    for row in layout.read_text().split('\n')[1:]:
        f=row.split()
        if len(f)>=3:
            fields[(f[0],f[1])]=(offset[f[0]],int(f[2]));offset[f[0]]+=int(f[2])
            if f[0]=='O':opened[f[1]]=f[3]
    names={name for k,name in fields if k=='I'}
    def run(batch):
        """batch: list of {input name: bytes}; returns list of {output name: bytes}"""
        full=(1<<len(batch))-1;wires=[0]*n
        for v,values in enumerate(batch):
            if set(values)!=names:raise ValueError('%s inputs %s'%(key,sorted(names^set(values))))
            for name,data in values.items():
                start,bits=fields[('I',name)]
                if bits!=8*len(data):raise ValueError('%s input size %s'%(key,name))
                number=int.from_bytes(data,'little')
                for i in range(bits):
                    if (number>>i)&1:wires[start+i]|=1<<v
        append=wires.append
        for i in range(count):
            k=kind[i]
            if k==1:append(wires[left[i]]^wires[right[i]])
            elif k==0:append(wires[left[i]]&wires[right[i]])
            else:append(wires[left[i]]^full)
        results=[]
        for v in range(len(batch)):
            result={}
            for (k,name),(start,size) in fields.items():
                if k=='O':result[name]=sum(((wires[outputs[start+i]]>>v)&1)<<i for i in range(size)).to_bytes(size//8,'little')
            results.append(result)
        return results
    KERNELS[key]=(run,ands,opened);return KERNELS[key]

# ---- reference: Kyber-1024 round 3 and ML-KEM-1024, plain integers ------------------------------
def brv(i):return int('{:07b}'.format(i)[::-1],2)
ZETA=[pow(17,brv(i),Q) for i in range(128)]
def ntt(f):
    f=f[:];k=1;l=128
    while l>=2:
        for start in range(0,256,2*l):
            z=ZETA[k];k+=1
            for j in range(start,start+l):
                t=z*f[j+l]%Q;f[j+l]=(f[j]-t)%Q;f[j]=(f[j]+t)%Q
        l//=2
    return f
def intt(f):
    f=f[:];k=127;l=2
    while l<=128:
        for start in range(0,256,2*l):
            z=ZETA[k];k-=1
            for j in range(start,start+l):
                t=f[j];f[j]=(t+f[j+l])%Q;f[j+l]=z*(f[j+l]-t)%Q
        l*=2
    return [x*3303%Q for x in f]
def basemul(a,b):
    r=[0]*256
    for i in range(128):
        g=pow(17,2*brv(i)+1,Q);a0,a1,b0,b1=a[2*i],a[2*i+1],b[2*i],b[2*i+1]
        r[2*i]=(a0*b0+a1*b1*g)%Q;r[2*i+1]=(a0*b1+a1*b0)%Q
    return r
def padd(*ps):return [sum(c)%Q for c in zip(*ps)]
def psub(a,b):return [(x-y)%Q for x,y in zip(a,b)]
def candidates(stream):
    out=[]
    for i in range(0,len(stream)-2,3):
        out.append(stream[i]|((stream[i+1]&15)<<8));out.append((stream[i+1]>>4)|(stream[i+2]<<4))
    return out
def parse(seed,blocks=None):
    """SampleNTT. With `blocks`, the kernels' budget: (coefficients or zeros, accepted)."""
    if blocks is None:
        accepted=[d for d in candidates(hashlib.shake_128(seed).digest(168*12)) if d<Q]
        if len(accepted)<256:raise ValueError('unbounded sampler ran out')
        return accepted[:256]
    accepted=[d for d in candidates(hashlib.shake_128(seed).digest(168*blocks)) if d<Q]
    return (accepted[:256],True) if len(accepted)>=256 else ([0]*256,False)
def cbd2(data):
    bits=int.from_bytes(data,'little')
    return [(((bits>>(4*i))&1)+((bits>>(4*i+1))&1)-((bits>>(4*i+2))&1)-((bits>>(4*i+3))&1))%Q for i in range(256)]
def compress(poly,d):return [(((x<<d)+Q//2)//Q)%(1<<d) for x in poly]
def decompress(poly,d):return [(x*Q+(1<<(d-1)))>>d for x in poly]
def pack(values,d):return sum(v<<(d*i) for i,v in enumerate(values)).to_bytes(len(values)*d//8,'little')
def unpack(data,d):
    n=int.from_bytes(data,'little');return [(n>>(d*i))&((1<<d)-1) for i in range(len(data)*8//d)]
H=lambda x:hashlib.sha3_256(x).digest()
G=lambda x:hashlib.sha3_512(x).digest()
def prf(seed,nonce):return cbd2(hashlib.shake_256(seed+bytes([nonce])).digest(128))
def keygen(seed,kyber):
    d,z=seed[:32],seed[32:];g=G(d if kyber else d+b'\x04');rho,sigma=g[:32],g[32:]
    s=[ntt(prf(sigma,i)) for i in range(4)];e=[ntt(prf(sigma,4+i)) for i in range(4)]
    t=[padd(*[basemul(parse(rho+bytes([j,i])),s[j]) for j in range(4)],e[i]) for i in range(4)]
    pk=b''.join(pack(p,12) for p in t)+rho
    return b''.join(pack(p,12) for p in s)+pk+H(pk)+z,pk
def encrypt(pk,message,coins,detail=None):
    t=[unpack(pk[384*i:384*i+384],12) for i in range(4)];rho=pk[1536:]
    r=[ntt(prf(coins,i)) for i in range(4)];e1=[prf(coins,4+i) for i in range(4)];e2=prf(coins,8)
    rows=[[parse(rho+bytes([i,j])) for j in range(4)] for i in range(4)]
    u=[padd(intt(padd(*[basemul(rows[i][j],r[j]) for j in range(4)])),e1[i]) for i in range(4)]
    v=padd(intt(padd(*[basemul(t[j],r[j]) for j in range(4)])),e2,[((message[i//8]>>(i%8))&1)*1665 for i in range(256)])
    us=[pack(compress(p,11),11) for p in u];vs=pack(compress(v,5),5)
    if detail is not None:detail.update(rhat=b''.join(pack(p,12) for p in r),rows=[b''.join(pack(p,12) for p in row) for row in rows],u=us,v=vs)
    return b''.join(us)+vs
def encapsulate(pk,randomness,kyber,detail=None):
    m=H(randomness) if kyber else randomness;kr=G(m+H(pk));kbar,coins=kr[:32],kr[32:]
    ct=encrypt(pk,m,coins,detail)
    if detail is not None:detail.update(message=m,kbar=kbar,coins=coins)
    return ct,(hashlib.shake_256(kbar+H(ct)).digest(32) if kyber else kbar)
def decapsulate(sk,ct,kyber):
    s=[unpack(sk[384*i:384*i+384],12) for i in range(4)];pk=sk[1536:3104];h=sk[3104:3136];z=sk[3136:3168]
    u=[decompress(unpack(ct[352*i:352*i+352],11),11) for i in range(4)];v=decompress(unpack(ct[1408:],5),5)
    w=psub(v,intt(padd(*[basemul(s[j],ntt(u[j])) for j in range(4)])))
    m=pack(compress(w,1),1);kr=G(m+h);good=encrypt(pk,m,kr[32:])==ct
    if kyber:return hashlib.shake_256((kr[:32] if good else z)+H(ct)).digest(32)
    return kr[:32] if good else hashlib.shake_256(z+ct).digest(32)
def key_valid(pk):return all(x<Q for x in unpack(pk[:1536],12))

def oracle(variant,seed,entropy):
    line=subprocess.run([str(ORACLE)],input='%s|%s|%s\n'%(variant,seed.hex(),entropy.hex()),text=True,capture_output=True,check=True).stdout.strip()
    sk,pk,ct,ss,recovered=map(bytes.fromhex,line.split('|'));return sk,pk,ct,ss

def validate_reference(rng,notes):
    count=0
    if ORACLE.exists():
        for name,kyber in (('kyber1024',True),('mlkem1024',False)):
            for trial in range(3):
                seed=rng.randbytes(64) if trial else bytes(64);entropy=rng.randbytes(32)
                sk,pk,ct,ss=oracle(name,seed,entropy)
                if keygen(seed,kyber)!=(sk,pk):raise AssertionError('reference keygen vs libcrux '+name)
                if encapsulate(pk,entropy,kyber)!=(ct,ss):raise AssertionError('reference encapsulate vs libcrux '+name)
                if decapsulate(sk,ct,kyber)!=ss:raise AssertionError('reference decapsulate vs libcrux '+name)
                count+=1
        notes.append('reference equals pinned libcrux 0.0.10 on %d key pairs (keygen, encapsulate, decapsulate)'%count)
    else:notes.append('libcrux oracle binary absent: reference NOT compared with libcrux')
    keys={}
    if TESTDATA.exists():
        for name,kyber,strip in (('',True,0),('mlkem-',False,1)):
            pk=(TESTDATA/(name+'pk.dat')).read_bytes()[strip:];sk=(TESTDATA/(name+'sk.dat')).read_bytes()[strip:]
            if len(pk)!=1568 or len(sk)!=3168 or sk[1536:3104]!=pk or sk[3104:3136]!=H(pk):raise AssertionError('libsignal test key pair '+name)
            ct,ss=encapsulate(pk,rng.randbytes(32),kyber)
            if decapsulate(sk,ct,kyber)!=ss:raise AssertionError('round trip under libsignal test key '+name)
            keys[kyber]=(pk,sk)
        notes.append('reference round-trips under libsignal\'s two test key pairs')
    else:notes.append('libsignal test key pairs absent')
    try:
        from cryptography.hazmat.primitives.asymmetric import mlkem
        private=mlkem.MLKEM1024PrivateKey.from_seed_bytes(bytes(range(64)));pk=private.public_key().public_bytes_raw()
        if keygen(bytes(range(64)),False)[1]!=pk:raise AssertionError('reference keygen vs cryptography')
        ct,ss=encapsulate(pk,rng.randbytes(32),False)
        if private.decapsulate(ct)!=ss:raise AssertionError('cryptography decapsulation of the reference ciphertext')
        notes.append('reference ML-KEM-1024 agrees with the cryptography package (keygen from seed, decapsulation)');keys['cryptography']=private
    except (ImportError,AttributeError) as error:
        notes.append('cryptography package has no usable ML-KEM-1024 here (%s): not used'%type(error).__name__)
    return keys

def sequence(variant,cases,report):
    """Run the whole kernel sequence on a batch of (key, entropyA, entropyB); compare every field."""
    kyber=variant=='kyber';ands={}
    def run(*args):
        f,count,opened=kernel(*args);ands[' '.join(map(str,args))]=count
        if any(flag!='0' for flag in opened.values()):raise AssertionError('%s opens %s'%(args,opened))
        return f
    expect=[]
    for key,a,b in cases:
        d={};valid=key_valid(key)
        ct,ss=encapsulate(key,bytes(x^y for x,y in zip(a,b)),kyber,d);d.update(valid=valid,ct=ct,ss=ss);expect.append(d)
    hashed=run('kem-hash',variant)([dict(kyberPrekey=k,entropyA=a,entropyB=b) for k,a,b in cases])
    for got,d in zip(hashed,expect):
        if (got['message'],got['kbar'],got['coins'])!=(d['message'],d['kbar'],d['coins']):raise AssertionError('kem-hash')
        if got['keyValid']!=(b'\xff' if d['valid'] else b'\x00'):raise AssertionError('keyValid')
    rhat=run('kem-ntt')([dict(coins=h['coins']) for h in hashed])
    for got,d in zip(rhat,expect):
        if got['rhat']!=d['rhat']:raise AssertionError('kem-ntt')
    us=[];oks=[]
    for i in range(4):
        rows=run('kem-matrix',i)([dict(kyberPrekey=k) for k,_,_ in cases])
        for got,d in zip(rows,expect):
            if got['row%d'%i]!=d['rows'][i] or got['ok%d'%i]!=b'\xff':raise AssertionError('kem-matrix %d'%i)
        u=run('kem-u',i)([{'row%d'%i:r['row%d'%i],'rhat':t['rhat'],'coins':h['coins']} for r,t,h in zip(rows,rhat,hashed)])
        for got,d in zip(u,expect):
            if got['u%d'%i]!=d['u'][i]:raise AssertionError('kem-u %d'%i)
        us.append(u);oks.append(rows)
    v=run('kem-v')([dict(kyberPrekey=k,rhat=t['rhat'],coins=h['coins'],message=h['message']) for (k,_,_),t,h in zip(cases,rhat,hashed)])
    for got,d in zip(v,expect):
        if d['valid'] and got['v']!=d['v']:raise AssertionError('kem-v')
    finish=run('kem-finish',variant)
    inputs=[dict(u0=us[0][n]['u0'],u1=us[1][n]['u1'],u2=us[2][n]['u2'],u3=us[3][n]['u3'],v=v[n]['v'],kbar=hashed[n]['kbar'],
        ok0=oks[0][n]['ok0'],ok1=oks[1][n]['ok1'],ok2=oks[2][n]['ok2'],ok3=oks[3][n]['ok3'],keyValid=hashed[n]['keyValid']) for n in range(len(cases))]
    final=finish(inputs);accepted=rejected=0
    for got,d in zip(final,expect):
        if d['valid']:
            if (got['kemStatus'],got['kemCiphertext'],got['kemSecret'])!=(b'\xff',d['ct'],d['ss']):raise AssertionError('accepted encapsulation differs')
            accepted+=1
        else:
            if (got['kemStatus'],got['kemCiphertext'],got['kemSecret'])!=(b'\x00',bytes(1568),bytes(32)):raise AssertionError('malformed key not rejected cleanly')
            rejected+=1
    # A failed status of any stage, including a byte that is neither 0 nor 255.
    bad=[]
    for name,value in (('ok0',b'\x00'),('ok3',b'\x00'),('ok2',b'\x01'),('ok1',b'\xfe'),('keyValid',b'\x00'),('keyValid',b'\x7f')):
        bad.append(dict(inputs[0],**{name:value}))
    for got in finish(bad):
        if (got['kemStatus'],got['kemCiphertext'],got['kemSecret'])!=(b'\x00',bytes(1568),bytes(32)):raise AssertionError('failed status not rejected cleanly')
    report['and_gates'][variant]=ands;report['sequence_total'][variant]=sum(ands.values())
    return accepted,rejected,final

def malformed(pk,index,value):
    coefficients=unpack(pk[:1536],12);coefficients[index]=value;return pack(coefficients,12)+pk[1536:]

def sampler(rng):
    run,ands,opened=kernel('kem-sample')
    if any(flag!='0' for flag in opened.values()):raise AssertionError('kem-sample opens')
    def stream_of(values):return pack(values,12)
    streams=[]
    streams.append([4095]*448)                                          # nothing accepted
    streams.append([rng.randrange(Q) for _ in range(448)])              # everything accepted
    streams.append([rng.randrange(Q,4096)]*192+[rng.randrange(Q) for _ in range(256)])   # exactly 256, all at the end
    streams.append([rng.randrange(Q,4096)]*193+[rng.randrange(Q) for _ in range(255)])   # 255: one short
    for accepted in (0,1,255,256,257,300):
        values=[rng.randrange(Q) for _ in range(accepted)]+[rng.randrange(Q,4096) for _ in range(448-accepted)];rng.shuffle(values);streams.append(values)
    streams.append([Q-1,Q]*224);streams.append([Q,Q-1]*224)            # the boundary values, alternating
    for _ in range(6):streams.append([rng.randrange(4096) for _ in range(448)])
    for _ in range(4):streams.append([rng.randrange(Q) if rng.random()<0.57 else rng.randrange(Q,4096) for _ in range(448)])   # near the threshold
    results=run([dict(stream=stream_of(s)) for s in streams]);failed=0
    for values,got in zip(streams,results):
        accepted=[x for x in values if x<Q];good=len(accepted)>=256
        want=pack(accepted[:256],12) if good else bytes(384)
        if got['entry']!=want or got['ok']!=(b'\xff' if good else b'\x00'):raise AssertionError('sampler on a %d-accepted stream'%len(accepted))
        failed+=not good
    return len(streams),failed,ands

def lean_values(variant,key,a,b,expected):
    entropy=bytes(x^y for x,y in zip(a,b))
    for command in (['stages',variant,key.hex(),a.hex(),b.hex()],['reference',variant,key.hex(),entropy.hex()]):
        out=subprocess.run([str(EMITTER),*command],check=True,capture_output=True,text=True,cwd=ROOT).stdout.split()
        if out!=[x.hex() for x in expected]:raise AssertionError('Lean %s values differ (%s)'%(command[0],variant))

def main():
    started=time.time();rng=random.Random(20261111);notes=[];report=dict(and_gates={},sequence_total={})
    keys=validate_reference(rng,notes)
    for variant in ('kyber','mlkem'):
        kyber=variant=='kyber';cases=[]
        for trial in range(2):
            pk=keygen(rng.randbytes(64),kyber)[1];cases.append((pk,rng.randbytes(32),rng.randbytes(32)))
        if kyber in keys:cases.append((keys[kyber][0],rng.randbytes(32),rng.randbytes(32)))
        good=len(cases);base=cases[0][0]
        for index,value in ((0,Q),(1023,4095),(511,Q+1),(256,4000)):
            cases.append((malformed(base,index,value),cases[0][1],cases[0][2]))
        accepted,rejected,final=sequence(variant,cases,report)
        if accepted!=good or rejected!=4:raise AssertionError('case counts')
        if kyber in keys:   # libsignal's private key opens what the kernels produced for libsignal's public key
            if decapsulate(keys[kyber][1],final[good-1]['kemCiphertext'],kyber)!=final[good-1]['kemSecret']:raise AssertionError('libsignal key round trip')
        if not kyber and 'cryptography' in keys:
            private=keys['cryptography'];pk=private.public_key().public_bytes_raw()
            _,_,extra=sequence(variant,[(pk,rng.randbytes(32),rng.randbytes(32))],dict(and_gates={},sequence_total={}))
            if private.decapsulate(extra[0]['kemCiphertext'])!=extra[0]['kemSecret']:raise AssertionError('cryptography decapsulation of the kernels\' ciphertext')
            notes.append('the cryptography package decapsulates the kernels\' ML-KEM ciphertext to the kernels\' secret')
        if ORACLE.exists():
            seed=rng.randbytes(64);a=rng.randbytes(32);b=rng.randbytes(32)
            sk,pk,ct,ss=oracle(variant+'1024',seed,bytes(x^y for x,y in zip(a,b)))
            _,_,direct=sequence(variant,[(pk,a,b)],dict(and_gates={},sequence_total={}))
            if (direct[0]['kemCiphertext'],direct[0]['kemSecret'])!=(ct,ss):raise AssertionError('kernels vs libcrux directly')
        if '--no-lean-values' not in sys.argv:
            lean_values(variant,cases[0][0],cases[0][1],cases[0][2],(b'\xff',final[0]['kemCiphertext'],final[0]['kemSecret']))
        print(variant,'accepted',accepted,'rejected',rejected,'AND gates',report['sequence_total'][variant],flush=True)
    streams,failed,sample_ands=sampler(rng)
    print('sampler streams',streams,'of which rejected',failed)
    report.update(checked_at=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),notes=notes,sampler_streams=streams,sampler_rejected=failed,
        sampler_and_gates=sample_ands,lean_values_compared='--no-lean-values' not in sys.argv,libcrux_compared=ORACLE.exists(),
        nothing_opened=True,seconds=round(time.time()-started,1),emitter_sha256=hashlib.sha256(EMITTER.read_bytes()).hexdigest(),all_pass=True)
    (HERE/'kem-kernels-report.json').write_text(json.dumps(report,indent=2)+'\n')
    for note in notes:print('note:',note)
    print('all pass')
if __name__=='__main__':main()
