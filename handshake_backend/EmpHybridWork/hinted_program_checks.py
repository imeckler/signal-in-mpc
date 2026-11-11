"""Export, check and pin the constant-depth curve programs of TlsMpc/EdwardsHinted.lean.

Called by lower_word_circuits.py (which writes the pins header and the report). Every
program is printed from Lean, evaluated here on Python integers exactly as the C++ loader
reads it, and compared with independent arithmetic: textbook affine Edwards addition, a
Montgomery ladder, and `cryptography`'s X25519. The masks, hints and public square roots
that the runtime supplies (hinted_points.h) are modelled here the same way.
Run alone, it checks and writes the .flat files and prints the summary; it does not touch
the pins header.
"""
import hashlib,json,pathlib,random,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[2];OUT=ROOT/'.deps/emp-hybrid-word-v1'
P=2**255-19;D=(-121665*pow(121666,P-2,P))%P;ELL=2**252+27742317777372353535851937790883648493
SQRT_M1=pow(2,(P-1)//4,P)
NAMES=('lift-open','lift-point','edwards-prepare-hinted','edwards-offset-sum-fast','edwards-bit-table','edwards-bit-sum','edwards-affine-bit-sum','edwards-signature-sum','edwards-torsion-hinted')
def inv(a):return pow(a,P-2,P)
def field_sqrt(a):
    x=pow(a,(P+3)//8,P)
    if x*x%P!=a%P:x=x*SQRT_M1%P
    return x if x*x%P==a%P else None
def ed_add(p,q):
    (x1,y1),(x2,y2)=p,q;t=D*x1*x2*y1*y2%P
    return ((x1*y2+y1*x2)*inv(1+t)%P,(y1*y2+x1*x2)*inv(1-t)%P)
def ed_neg(p):return ((P-p[0])%P,p[1])
def ed_mul(k,p):
    r=(0,1)
    while k:
        if k&1:r=ed_add(r,p)
        p=ed_add(p,p);k>>=1
    return r
def on_curve(p):return (-p[0]*p[0]+p[1]*p[1]-1-D*p[0]*p[0]*p[1]*p[1])%P==0
def ladder(k,u):
    x2,z2,x3,z3,swap=1,0,u,1,0
    for t in reversed(range(255)):
        b=(k>>t)&1;swap^=b
        if swap:x2,x3,z2,z3=x3,x2,z3,z2
        swap=b
        a=(x2+z2)%P;aa=a*a%P;b2=(x2-z2)%P;bb=b2*b2%P;e=(aa-bb)%P;c=(x3+z3)%P;d=(x3-z3)%P;da=d*a%P;cb=c*b2%P
        x3=(da+cb)**2%P;z3=u*(da-cb)**2%P;x2=aa*bb%P;z2=e*(aa+121665*e)%P
    if swap:x2,x3,z2,z3=x3,x2,z3,z2
    return x2*inv(z2)%P
def lift(u):
    y=(u-1)*inv(u+1)%P;xx=(y*y-1)*inv(D*y*y+1)%P;x=field_sqrt(xx)
    return None if x is None else (x,y)
def montgomery_u(point):return (1+point[1])*inv(1-point[1])%P
def evaluate(text,inputs):
    """Outputs, and what the C++ loader counts: products that use a triple, multiplication
    levels, and levels that also have an opening (a division)."""
    lines=text.split('\n');n,count,width=map(int,lines[1].split())
    if lines[0]!='EMP_HYBRID_FIELD_DAG_V2' or int(lines[2])!=P or len(inputs)!=n or len(lines)!=count+5 or lines[-1]!='':raise ValueError('field format')
    values=[];small=[];depth=[];products=0;division_levels=set()
    for row in lines[3:3+count]:
        f=row.split()
        if f[0]=='C':values.append(int(f[1])%P);small.append(len(f[1])<=18);depth.append(0)
        elif f[0]=='I':values.append(inputs[int(f[1])]%P);small.append(False);depth.append(0)
        else:
            i,j=int(f[1]),int(f[2]);a,b=values[i],values[j]
            if f[0]=='D' and b==0:raise ZeroDivisionError('field program division by zero')
            values.append((a+b if f[0]=='A' else a-b if f[0]=='S' else a*inv(b) if f[0]=='D' else a*b)%P);small.append(False)
            secret=f[0]=='D' or (f[0]=='M' and not small[i] and not small[j])
            depth.append(max(depth[i],depth[j])+secret);products+=2 if f[0]=='D' else int(secret)
            if f[0]=='D':division_levels.add(depth[-1])
    tail=lines[3+count].split()
    if tail[0]!='O' or len(tail)!=width+1:raise ValueError('field outputs')
    return [values[int(w)] for w in tail[1:]],dict(products=products,levels=max(depth),opening_levels=len(division_levels))
def check(emit,rng):
    """`emit(name)`: the program's text from Lean. Returns (pins, report)."""
    texts={name:emit(name) for name in NAMES};cost={}
    def run(name,inputs):
        out,cost[name]=evaluate(texts[name],inputs);return out
    C_MAP=field_sqrt(-486664%P);BASE=lift(9);BASE=BASE if BASE[0]%2==0 else ed_neg(BASE)
    if BASE[1]!=4*inv(5)%P:raise AssertionError('base point')
    torsion8=None
    while torsion8 is None:
        candidate=lift(rng.randrange(2,P))
        if candidate is not None and ed_mul(4,ed_mul(ELL,candidate))!=(0,1):torsion8=ed_mul(ELL,candidate)
    def mask_point():   # uniform over the whole group, as the runtime samples it
        return ed_add(ed_mul(rng.randrange(1,ELL),BASE),ed_mul(rng.randrange(8),torsion8))
    def curve_u():return ladder(8*rng.randrange(1,2**250),9)
    def twist_u():
        while True:
            u=rng.randrange(2,P)
            if pow(u*(u*u+486662*u+1)%P,(P-1)//2,P)==P-1:return u
    def lift_run(u,ma,mb,ba=None,bb=None):
        """The runtime's lift: checks opened first, then w, then the public root, then Z."""
        r=rng.randrange(1,P);ba=rng.randrange(2) if ba is None else ba;bb=rng.randrange(2) if bb is None else bb
        w,ca,cb,cma,cmb,b=run('lift-open',[u,r,ba,bb,*ma,*mb])
        if (ca,cb,cma,cmb)!=(0,0,0,0):return None
        if b!=ba^bb:raise AssertionError('lift bit')
        if w==0:cs,sel,b=0,0,0
        else:
            sel=int(pow(w,(P-1)//2,P)==1);s=field_sqrt(w if sel else w*inv(2)%P);cs=C_MAP*inv(s)%P
        valid,x,y,zx,zy=run('lift-point',[cs,sel,u,r,b,*ma,*mb])
        return dict(w=w,valid=valid,point=(x,y),z=(zx,zy),sel=sel)
    def hints(z,ma,mb):   # A: 16^w (Z - M_A); B: 16^w M_B
        a,b=ed_add(z,ed_neg(ma)),mb;out=[]
        for w in range(1,64):
            a,b=ed_mul(16,a),ed_mul(16,b);out+=[*a,*b]
        return out
    # ---- lift: curve points, twist points, the two special coordinates, both values of the hidden bit.
    symbols=set();lifted=[]
    for case in range(8):
        u=curve_u() if case<4 else twist_u();ma,mb=mask_point(),mask_point()
        for ba,bb in ((0,0),(1,0)) if case%4==0 else ((None,None),):
            got=lift_run(u,ma,mb,ba,bb);want=lift(u)
            symbols.add((case<4,got['sel']))
            if got['valid']!=int(want is not None):raise AssertionError('lift validity')
            point=want if want is not None else BASE
            if got['point'] not in (point,ed_neg(point)) or (want is None and got['point']!=BASE):raise AssertionError('lift point')
            if got['z']!=ed_add(ed_add(ma,mb),got['point']) or not on_curve(got['z']):raise AssertionError('lift masked point')
            if case<4:lifted.append((u,got['point'],got['z'],ma,mb))
    if len(symbols)!=4:raise AssertionError('lift: the opened value must be a square and a non-square for curve and twist alike')
    for u in (0,P-1,1):   # u = 0 opens w = 0 and is treated as invalid; u = -1 must not divide by zero; u = 1 is a curve point of order 4
        ma,mb=mask_point(),mask_point();got=lift_run(u,ma,mb)
        if (got['w']==0)!=(u==0) or got['valid']!=int(u==1) or got['z']!=ed_add(ed_add(ma,mb),got['point']):raise AssertionError('lift special coordinate')
    ma,mb=mask_point(),mask_point()
    if lift_run(curve_u(),(ma[0],(ma[1]+1)%P),mb) is not None or lift_run(curve_u(),ma,mb,ba=2) is not None:raise AssertionError('lift checks')
    # ---- prepare, offset sum, bit table, agreements.
    from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey,X25519PublicKey
    WINDOWS,DIGITS,BITS=64,8,252;CHECKS=2*BITS+2*(WINDOWS-1)
    for case,(u,root,z,ma,mb) in enumerate(lifted[:3]):
        h=hints(z,ma,mb);masks=[rng.randrange(1,P) for _ in range(126)]
        ka,kb=rng.randrange(2**BITS),rng.randrange(2**BITS);bits=[(ka>>i)&1 for i in range(BITS)]+[(kb>>i)&1 for i in range(BITS)]
        out=run('edwards-prepare-hinted',[*root,*h,*masks,*bits])
        if len(out)!=CHECKS+2+2*WINDOWS*DIGITS or any(out[:CHECKS]):raise AssertionError('prepare-hinted checks')
        initial=tuple(out[CHECKS:CHECKS+2]);table=[tuple(out[CHECKS+2+2*i:CHECKS+4+2*i]) for i in range(WINDOWS*DIGITS)]
        if initial!=ed_mul(ka+kb,root):raise AssertionError('prepare-hinted initial point')
        for w in (range(WINDOWS) if case==0 else (0,1,2,31,63)):
            for j in range(1,DIGITS+1):
                if table[DIGITS*w+j-1]!=ed_mul(j*16**w,root):raise AssertionError('prepare-hinted table')
        # A wrong hint (a coordinate, or a different curve point) and a non-bit must each fail a check.
        for at in (0,1,2,3,4*17,4*62+3):
            bad=list(h);bad[at]=(bad[at]+1)%P
            try:
                if not any(run('edwards-prepare-hinted',[*root,*bad,*masks,*bits])[2*BITS:CHECKS]):raise AssertionError('prepare-hinted accepted a wrong hint')
            except ZeroDivisionError:pass
        bad=list(h);bad[4*9:4*9+2]=ed_add((bad[4*9],bad[4*9+1]),BASE)
        if not any(run('edwards-prepare-hinted',[*root,*bad,*masks,*bits])[2*BITS:CHECKS]):raise AssertionError('prepare-hinted accepted a shifted hint')
        bad=list(bits);bad[5]=2
        if run('edwards-prepare-hinted',[*root,*h,*masks,*bad])[5]==0:raise AssertionError('prepare-hinted bit check')
        for trial in range(3):
            offset=(2**BITS-1,rng.randrange(2**BITS),rng.randrange(2**BITS))[trial];chosen=[];carry=0
            for w in range(WINDOWS):
                digit=((offset>>(4*w))&15)+carry;carry=int(digit>8);digit-=16*carry
                chosen+=[*table[DIGITS*w+abs(digit)-1],1 if digit>0 else P-1] if digit else [0,1,1]
            numerator,denominator=run('edwards-offset-sum-fast',[*initial,*chosen])
            if numerator*inv(denominator)%P!=ladder(ka+kb+offset,u):raise AssertionError('offset-sum-fast')
        out=run('edwards-bit-table',[*root,*h,*masks])
        if len(out)!=126+1024 or any(out[:126]):raise AssertionError('bit-table links')
        ext=[out[126+4*i:130+4*i] for i in range(256)];power=root
        for i in range(256):
            x,y,zz,t=ext[i]
            if (x*inv(zz)%P,y*inv(zz)%P)!=power or t*zz%P!=x*y%P:raise AssertionError('bit-table entry')
            power=ed_add(power,power)
        bad=list(h);bad[4*30+1]=(bad[4*30+1]+1)%P
        try:
            if not any(run('edwards-bit-table',[*root,*bad,*masks])[:126]):raise AssertionError('bit-table accepted a wrong hint')
        except ZeroDivisionError:pass
        for trial in range(2):
            scalar=rng.randbytes(32);k=int.from_bytes(scalar,'little');kbits=[(k>>i)&1 for i in range(3,254)];rho=rng.randrange(1,P)
            want=int.from_bytes(X25519PrivateKey.from_private_bytes(scalar).exchange(X25519PublicKey.from_public_bytes(u.to_bytes(32,'little'))),'little')
            points=[c for i in range(3,255) for c in ext[i]]
            numerator,denominator=run('edwards-bit-sum',[1,rho,*points,*kbits])
            if numerator*inv(denominator)%P!=want:raise AssertionError('bit-sum')
            if run('edwards-bit-sum',[0,rho,*points,*kbits])[0]!=rho:raise AssertionError('bit-sum: an invalid point must give the mask')
            affine=[c for i in range(3,255) for c in table[DIGITS*(i//4)+2**(i%4)-1]]
            numerator,denominator=run('edwards-affine-bit-sum',[1,rho,*affine,*kbits])
            if numerator*inv(denominator)%P!=want:raise AssertionError('affine-bit-sum')
        # The signature point [s]B - [h]A, with the key's table in both forms the runtime uses.
        public=[];power=root
        for i in range(256):public+=[power[0],power[1],1,power[0]*power[1]%P];power=ed_add(power,power)
        base=[];power=BASE
        for i in range(253):base+=[power[0],power[1],1,power[0]*power[1]%P];power=ed_add(power,power)
        for key in (public,[c for e in ext for c in e]):
            flip,hh,s=rng.randrange(2),rng.randrange(2**256),rng.randrange(2**253)
            a=((P-root[0])%P if flip else root[0],root[1]);want=ed_add(ed_mul(hh,ed_neg(a)),ed_mul(s,BASE))
            got=run('edwards-signature-sum',[flip,*key,*[(hh>>i)&1 for i in range(256)],*base,*[(s>>i)&1 for i in range(253)]])
            if tuple(got)!=want:raise AssertionError('signature-sum')
    # ---- torsion: zero exactly for points of the prime-order subgroup; a hint off the curve is caught.
    eighth=pow(8,ELL-2,ELL)
    for u,root,z,ma,mb in lifted:
        for point,free in ((root,True),(ed_neg(root),True),(ed_add(root,torsion8),False),(ed_add(root,ed_mul(2,torsion8)),False),(ed_add(root,ed_mul(4,torsion8)),False)):
            zz=ed_add(ed_add(ma,mb),point);ha,hb=ed_mul(eighth,ed_add(zz,ed_neg(ma))),ed_mul(eighth,mb);mask=rng.randrange(1,P)
            got=run('edwards-torsion-hinted',[*point,*ha,*hb,mask])
            if (got==[0,0])!=free or (ed_mul(ELL,point)==(0,1))!=free:raise AssertionError('torsion-hinted')
            try:
                if run('edwards-torsion-hinted',[*point,ha[0],(ha[1]+1)%P,*hb,mask])==[0,0]:raise AssertionError('torsion-hinted accepted a wrong hint')
            except ZeroDivisionError:pass
    pins,report=[],{}
    for name,text in texts.items():
        (OUT/(name+'.flat')).write_text(text);digest=hashlib.sha256(text.encode()).hexdigest()
        pins.append('inline constexpr const char* %s_SHA="%s";'%(name.replace('-','_').upper(),digest))
        report[name]=dict(flat_sha256=digest,cases_checked=len(lifted),reference='independent Edwards arithmetic, Montgomery ladder, cryptography X25519',**cost[name])
    return pins,report
if __name__=='__main__':
    subprocess.run(['lake','build','word_mask_emitter'],cwd=ROOT,check=True,capture_output=True)
    emit=lambda name:subprocess.run(['lake','exe','word_mask_emitter',name],cwd=ROOT,check=True,capture_output=True).stdout.decode()
    pins,report=check(emit,random.Random(20261111))
    print(json.dumps({k:{c:v[c] for c in ('products','levels','opening_levels')} for k,v in report.items()},indent=1))
