"""Export the Lean-defined conversion circuits, check and pin them.

The gate lists are produced entirely in Lean (TlsMpc/WordMask.lean compiled by
TlsMpc/BoolDag.lean, printed by EmitWordMask.lean). This script does no
lowering: it parses the printed text exactly as the C++ loader does, evaluates
it against Python integers on boundary and random inputs, and writes the files
and their SHA-256 pins. Input word v, bit i (2^i) is wire 255*v+i; output k is
the k-th expression of the Lean circuit.
"""
import hashlib,json,pathlib,random,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent;OUT=ROOT/'.deps/emp-hybrid-word-v1';OUT.mkdir(exist_ok=True)
P=2**255-19;W=255
def parse(text,expected_inputs=2*W):
    lines=text.split('\n')
    if lines[0]!='EMP_HYBRID_BOOL_V1' or lines[-1]!='':raise ValueError('format')
    inputs,count,width=map(int,lines[1].split())
    if inputs!=expected_inputs or len(lines)!=count+4:raise ValueError('shape')
    gates=[]
    for i,row in enumerate(lines[2:2+count]):
        f=row.split();op=f[0];args=list(map(int,f[1:]))
        if op not in 'AXN' or len(args)!=(1 if op=='N' else 2) or any(a>=inputs+i for a in args):raise ValueError('gate')
        gates.append((op,*args))
    tail=lines[2+count].split()
    if tail[0]!='O' or len(tail)!=width+1:raise ValueError('outputs')
    return gates,list(map(int,tail[1:]))
def evaluate(gates,outputs,x,y):
    wires=[(x>>i)&1 for i in range(W)]+[(y>>i)&1 for i in range(W)]
    for g in gates:wires.append(1-wires[g[1]] if g[0]=='N' else (wires[g[1]]^wires[g[2]] if g[0]=='X' else wires[g[1]]&wires[g[2]]))
    return sum(wires[w]<<k for k,w in enumerate(outputs))
SPEC={'modadd':lambda x,y:(x+y)%P if x<P and y<P else None,
      'finalize-mask':lambda x,y:(((x+y)%P)|(1<<255)) if x<P and y<P else None,
      'finalize-bits':lambda x,y:(x^y)|((x<P and y<P and x>=32 and y>=32)<<255),
      'into-field':lambda x,y:(x%P+y)%P if y<P else None,
      'status':lambda x,y:(x==y)|((x!=0)<<1)}
# For rejected inputs only the flag bit is specified.
FLAG={'finalize-mask':lambda x,y:x<P and y<P}
EDGE=[0,1,18,19,31,32,33,P-1,P,P+1,P+18,2**255-1,2**254,2**254-1]
rng=random.Random(20261110);report={};pins=[]
subprocess.run(['lake','build','word_mask_emitter'],cwd=ROOT,check=True,capture_output=True)
for name in SPEC:
    text=subprocess.run(['lake','exe','word_mask_emitter',name],cwd=ROOT,check=True,capture_output=True).stdout.decode()
    gates,outputs=parse(text)
    cases=[(x,y) for x in EDGE for y in EDGE]+[(rng.randrange(2**255),rng.randrange(2**255)) for _ in range(200)]+[(rng.randrange(P),rng.randrange(P)) for _ in range(200)]
    for x,y in cases:
        got=evaluate(gates,outputs,x,y);want=SPEC[name](x,y)
        if want is not None:
            if got!=want:raise AssertionError((name,x,y))
        elif name in FLAG and (got>>255)!=FLAG[name](x,y):raise AssertionError((name,'flag',x,y))
    path=OUT/(name+'.flat');path.write_text(text);digest=hashlib.sha256(text.encode()).hexdigest()
    pins.append('inline constexpr const char* WORD_%s_SHA="%s";'%(name.replace('-','_').upper(),digest))
    report[name]=dict(flat_sha256=digest,and_gates=sum(g[0]=='A' for g in gates),xor_gates=sum(g[0]=='X' for g in gates),not_gates=sum(g[0]=='N' for g in gates),outputs=len(outputs),cases_checked=len(cases))
# Single-bit XOR, used in parallel copies.
text=subprocess.run(['lake','exe','word_mask_emitter','xor-bit'],cwd=ROOT,check=True,capture_output=True).stdout.decode()
gates,outputs=parse(text,2)
for a in (0,1):
    for b in (0,1):
        wires=[a,b]
        for g in gates:wires.append(1-wires[g[1]] if g[0]=='N' else (wires[g[1]]^wires[g[2]] if g[0]=='X' else wires[g[1]]&wires[g[2]]))
        if [wires[w] for w in outputs]!=[a^b]:raise AssertionError('xor-bit')
(OUT/'xor-bit.flat').write_text(text);pins.append('inline constexpr const char* WORD_XOR_BIT_SHA="%s";'%hashlib.sha256(text.encode()).hexdigest())
report['xor-bit']=dict(flat_sha256=hashlib.sha256(text.encode()).hexdigest(),and_gates=sum(g[0]=='A' for g in gates),outputs=1,cases_checked=4)
# Field-side programs (TlsMpc/FieldBits.lean), same flat format as the X25519 program.
def field_eval(text,inputs):
    lines=text.split('\n');n,count,output=map(int,lines[1].split())
    if lines[0]!='EMP_HYBRID_FIELD_DAG_V1' or int(lines[2])!=P or len(inputs)!=n or len(lines)!=count+4 or lines[-1]!='':raise ValueError('field format')
    values=[]
    for row in lines[3:3+count]:
        f=row.split()
        if f[0]=='C':values.append(int(f[1])%P)
        elif f[0]=='I':values.append(inputs[int(f[1])])
        else:
            a,b=values[int(f[1])],values[int(f[2])];values.append((a+b if f[0]=='A' else a-b if f[0]=='S' else a*b)%P)
    return values[output],sum(r[0]=='M' for r in lines[3:3+count])
FIELD={'field-bit-check':(1,lambda v:v[0]*(v[0]-1)%P),'field-bit-xor':(2,lambda v:(v[0]+v[1]-2*v[0]*v[1])%P),'field-recompose':(256,lambda v:(sum(v[i]<<i for i in range(255))-v[255])%P)}
for name,(n,spec) in FIELD.items():
    text=subprocess.run(['lake','exe','word_mask_emitter',name],cwd=ROOT,check=True,capture_output=True).stdout.decode()
    for _ in range(50):
        v=[rng.randrange(P) for _ in range(n)] if _%2 else [rng.randrange(2) for _ in range(n)]
        got,muls=field_eval(text,v)
        if got!=spec(v):raise AssertionError(name)
    (OUT/(name+'.flat')).write_text(text);digest=hashlib.sha256(text.encode()).hexdigest()
    pins.append('inline constexpr const char* %s_SHA="%s";'%(name.replace('-','_').upper(),digest))
    report[name]=dict(flat_sha256=digest,multiplication_nodes=muls,inputs=n,cases_checked=50)
# Multi-output field programs (V2): the leaner X25519 ladder and the mask pair.
def field_eval_all(text,inputs):
    lines=text.split('\n');n,count,width=map(int,lines[1].split())
    if lines[0]!='EMP_HYBRID_FIELD_DAG_V2' or int(lines[2])!=P or len(inputs)!=n or len(lines)!=count+5 or lines[-1]!='':raise ValueError('field format')
    values=[];secret=[];products=0
    for row in lines[3:3+count]:
        f=row.split()
        if f[0]=='C':values.append(int(f[1])%P);secret.append(False)
        elif f[0]=='I':values.append(inputs[int(f[1])]);secret.append(True)
        else:
            i,j=int(f[1]),int(f[2]);a,b=values[i],values[j]
            if f[0]=='D' and b==0:raise ZeroDivisionError('field program division by zero')
            values.append((a+b if f[0]=='A' else a-b if f[0]=='S' else a*pow(b,P-2,P) if f[0]=='D' else a*b)%P)
            secret.append(secret[i] or secret[j]);products+=2 if f[0]=='D' else (f[0]=='M' and secret[i] and secret[j])
    tail=lines[3+count].split()
    if tail[0]!='O' or len(tail)!=width+1:raise ValueError('field outputs')
    return [values[int(w)] for w in tail[1:]],products
def clamp(bits):return [0,0,0]+bits[3:254]+[1,0]
def swap_bits(bits):
    c=clamp(bits);return {t:(0 if t+1==255 else c[t+1])^c[t] for t in range(255)}
from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey,X25519PublicKey
from cryptography.hazmat.primitives import serialization as ser
text=subprocess.run(['lake','exe','word_mask_emitter','x25519-fast'],cwd=ROOT,check=True,capture_output=True).stdout.decode()
for _ in range(20):
    scalar=rng.randbytes(32);point=X25519PrivateKey.from_private_bytes(rng.randbytes(32)).public_key().public_bytes(ser.Encoding.Raw,ser.PublicFormat.Raw)
    want=int.from_bytes(X25519PrivateKey.from_private_bytes(scalar).exchange(X25519PublicKey.from_public_bytes(point)),'little')
    bits=[(scalar[i//8]>>(i%8))&1 for i in range(256)];w=swap_bits(bits);u=int.from_bytes(point,'little')%(1<<255)%P
    (x,z),products=field_eval_all(text,[w[t] if 2<=t<=253 else 0 for t in range(256)]+[u])
    if x*pow(z,P-2,P)%P!=want:raise AssertionError('x25519-fast')
(OUT/'x25519-fast.flat').write_text(text);digest=hashlib.sha256(text.encode()).hexdigest();pins.append('inline constexpr const char* X25519_FAST_SHA="%s";'%digest)
report['x25519-fast']=dict(flat_sha256=digest,secret_products=products,inputs=257,outputs=2,cases_checked=20,reference='cryptography X25519')
text=subprocess.run(['lake','exe','word_mask_emitter','field-mask-pair'],cwd=ROOT,check=True,capture_output=True).stdout.decode()
for _ in range(20):
    v=[rng.randrange(P) for _ in range(3)];got,products=field_eval_all(text,v)
    if got!=[v[0]*v[2]%P,v[1]*v[2]%P]:raise AssertionError('mask pair')
(OUT/'field-mask-pair.flat').write_text(text);digest=hashlib.sha256(text.encode()).hexdigest();pins.append('inline constexpr const char* FIELD_MASK_PAIR_SHA="%s";'%digest)
report['field-mask-pair']=dict(flat_sha256=digest,secret_products=products,inputs=3,outputs=2,cases_checked=20)
# Additive-share agreement programs (TlsMpc/EdwardsShare.lean), checked against an
# independent Montgomery ladder: u(kA*S + kB*S) must equal ladder(kA+kB, u(S)).
D=(-121665*pow(121666,P-2,P))%P
def ed_add(p,q):
    (x1,y1),(x2,y2)=p,q;t=D*x1*x2*y1*y2%P
    return ((x1*y2+y1*x2)*pow(1+t,P-2,P)%P,(y1*y2+x1*x2)*pow(1-t,P-2,P)%P)
def ed_mul(k,p):
    r=(0,1)
    while k:
        if k&1:r=ed_add(r,p)
        p=ed_add(p,p);k>>=1
    return r
def ladder(k,u):
    x2,z2,x3,z3,swap=1,0,u,1,0
    for t in reversed(range(255)):
        b=(k>>t)&1;swap^=b
        if swap:x2,x3,z2,z3=x3,x2,z3,z2
        swap=b
        a=(x2+z2)%P;aa=a*a%P;b2=(x2-z2)%P;bb=b2*b2%P;e=(aa-bb)%P;c=(x3+z3)%P;d=(x3-z3)%P;da=d*a%P;cb=c*b2%P
        x3=(da+cb)**2%P;z3=u*(da-cb)**2%P;x2=aa*bb%P;z2=e*(aa+121665*e)%P
    if swap:x2,x3,z2,z3=x3,x2,z3,z2
    return x2*pow(z2,P-2,P)%P
def lift(u):
    y=(u-1)*pow(u+1,P-2,P)%P;xx=(y*y-1)*pow(D*y*y+1,P-2,P)%P;x=pow(xx,(P+3)//8,P)
    if x*x%P!=xx:x=x*pow(2,(P-1)//4,P)%P
    if x*x%P!=xx:return None
    return (x if x%2==0 else P-x,y)
curve_text=subprocess.run(['lake','exe','word_mask_emitter','edwards-on-curve'],cwd=ROOT,check=True,capture_output=True).stdout.decode()
add_text=subprocess.run(['lake','exe','word_mask_emitter','edwards-add-u'],cwd=ROOT,check=True,capture_output=True).stdout.decode()
checked=0
while checked<20:
    server=lift(ladder(8*rng.randrange(1,2**250),9))
    if server is None:continue
    ka,kb=8*rng.randrange(1,2**250),8*rng.randrange(1,2**250);ta,tb=ed_mul(ka,server),ed_mul(kb,server)
    for point in (ta,tb):
        if field_eval(curve_text,list(point))[0]!=0 or field_eval(curve_text,[point[0],(point[1]+1)%P])[0]==0:raise AssertionError('edwards-on-curve')
    (x,z),add_products=field_eval_all(add_text,[*ta,*tb])
    if z==0 or x*pow(z,P-2,P)%P!=ladder(ka+kb,(1+server[1])*pow(1-server[1],P-2,P)%P):raise AssertionError('edwards-add-u')
    checked+=1
for name,text,key,extra in (('edwards-on-curve',curve_text,'EDWARDS_ON_CURVE_SHA',dict(multiplication_nodes=field_eval(curve_text,[0,1])[1],inputs=2)),('edwards-add-u',add_text,'EDWARDS_ADD_U_SHA',dict(secret_products=add_products,inputs=4,outputs=2))):
    (OUT/(name+'.flat')).write_text(text);digest=hashlib.sha256(text.encode()).hexdigest();pins.append('inline constexpr const char* %s="%s";'%(key,digest))
    report[name]=dict(flat_sha256=digest,cases_checked=20,reference='independent Montgomery ladder on the summed scalar',**extra)
# Affine Edwards programs (TlsMpc/EdwardsAffine.lean), checked against the same reference.
SQRT_M1=pow(2,(P-1)//4,P)
def field_sqrt(a):
    x=pow(a,(P+3)//8,P)
    if x*x%P!=a%P:x=x*SQRT_M1%P
    return x if x*x%P==a%P else None
texts={name:subprocess.run(['lake','exe','word_mask_emitter',name],cwd=ROOT,check=True,capture_output=True).stdout.decode() for name in ('edwards-prepare','edwards-offset-sum')}
WINDOWS,DIGITS,BITS=63,15,252;CHECKS=1+2*BITS
def montgomery_u(point):return (1+point[1])*pow(1-point[1],P-2,P)%P
edwards_products={}
for case in range(4):
    base=None
    while base is None:
        u=ladder(8*rng.randrange(1,2**250),9);base=lift(u)
    ka,kb=rng.randrange(2**BITS),rng.randrange(2**BITS)
    bits=[(ka>>i)&1 for i in range(BITS)]+[(kb>>i)&1 for i in range(BITS)]
    out,edwards_products['edwards-prepare']=field_eval_all(texts['edwards-prepare'],[u,rng.randrange(1,P),*bits])
    if len(out)!=CHECKS+2+2*WINDOWS*DIGITS or any(out[:CHECKS]):raise AssertionError('edwards-prepare checks')
    initial=tuple(out[CHECKS:CHECKS+2]);table=[tuple(out[CHECKS+2+2*i:CHECKS+4+2*i]) for i in range(WINDOWS*DIGITS)]
    root=table[0]   # either of the two points with this u
    if root[1]!=base[1] or root[0] not in (base[0],P-base[0]) or field_eval(curve_text,list(root))[0]!=0:raise AssertionError('edwards-prepare recipient')
    if initial!=ed_mul(ka+kb,root):raise AssertionError('edwards-prepare initial point')
    for w in ((0,1,2,31,62) if case else range(WINDOWS)):
        for j in range(1,DIGITS+1):
            if table[DIGITS*w+j-1]!=ed_mul(j*16**w,root):raise AssertionError('edwards-prepare table')
    # A flipped scalar bit input that is not a bit must fail its check; a twist u must fail the curve check.
    bad=list(bits);bad[5]=2
    if field_eval_all(texts['edwards-prepare'],[u,1,*bad])[0][1+5]==0:raise AssertionError('edwards-prepare bit check')
    for _ in range(3):
        offset=rng.randrange(2**BITS);chosen=[]
        for w in range(WINDOWS):
            digit=(offset>>(4*w))&15;chosen+=list(table[DIGITS*w+digit-1]) if digit else [0,1]
        (got,),edwards_products['edwards-offset-sum']=field_eval_all(texts['edwards-offset-sum'],[*initial,*chosen])
        if got!=montgomery_u(ed_mul(ka+kb+offset,root)) or got!=ladder(ka+kb+offset,u):raise AssertionError('edwards-offset-sum')
twists=0
while twists<3:
    u=rng.randrange(2,P)
    if pow((u*u*u+486662*u*u+u)%P,(P-1)//2,P)==1:continue
    twists+=1
    try:
        if field_eval_all(texts['edwards-prepare'],[u,1,*([0]*(2*BITS))])[0][0]==0:raise AssertionError('edwards-prepare accepted a twist point')
    except ZeroDivisionError:pass
for name,text in texts.items():
    (OUT/(name+'.flat')).write_text(text);digest=hashlib.sha256(text.encode()).hexdigest();pins.append('inline constexpr const char* %s_SHA="%s";'%(name.replace('-','_').upper(),digest))
    report[name]=dict(flat_sha256=digest,products=edwards_products[name],divisions=sum(row.startswith('D') for row in text.split('\n')[3:]),cases_checked=4,reference='independent Edwards arithmetic and Montgomery ladder')
# Swap-bit derivation from scalar bits (no AND gates).
text=subprocess.run(['lake','exe','word_mask_emitter','swap-bits'],cwd=ROOT,check=True,capture_output=True).stdout.decode()
gates,outputs=parse(text,256)
for _ in range(50):
    bits=[rng.randrange(2) for _ in range(256)];wires=list(bits)
    for g in gates:wires.append(1-wires[g[1]] if g[0]=='N' else (wires[g[1]]^wires[g[2]] if g[0]=='X' else wires[g[1]]&wires[g[2]]))
    w=swap_bits(bits)
    if [wires[o] for o in outputs]!=[w[t] for t in range(2,254)]:raise AssertionError('swap-bits')
(OUT/'swap-bits.flat').write_text(text);digest=hashlib.sha256(text.encode()).hexdigest();pins.append('inline constexpr const char* SWAP_BITS_SHA="%s";'%digest)
report['swap-bits']=dict(flat_sha256=digest,and_gates=sum(g[0]=='A' for g in gates),outputs=len(outputs),cases_checked=50)
(OUT/'word_circuit_pins.h').write_text('#pragma once\nnamespace emp_hybrid {\n'+'\n'.join(pins)+'\n}\n')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
out=dict(passed=True,circuits=report,lean_sources={f:sha(ROOT/f) for f in ('TlsMpc/BoolDag.lean','TlsMpc/WordMask.lean','TlsMpc/FieldBits.lean','TlsMpc/FieldDag.lean','TlsMpc/FieldDagMulti.lean','TlsMpc/X25519.lean','TlsMpc/X25519Fast.lean','TlsMpc/X25519SwapBits.lean','handshake_backend/EmpHybridWork/EmitWordMask.lean')},scope='Conversion circuits defined and proved in Lean (TlsMpc/WordMask.lean), compiled by the validated gate-level compiler (TlsMpc/BoolDag.lean) and printed from Lean. Checked here against integer arithmetic on boundary and random inputs. The printer, this parser and the C++ loader are outside the Lean theorems.')
(HERE/'word-circuits-report.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v.get('and_gates',v.get('secret_products',v.get('multiplication_nodes'))) for k,v in report.items()}))
