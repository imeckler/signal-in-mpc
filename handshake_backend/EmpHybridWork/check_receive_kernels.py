#!/usr/bin/env python3
"""Check the first-message receive kernels (TlsMpc/ReceiveKernels.lean).

This script is a CHECK only. A real libsignal v0.106.1 SENDER
(signal_backend/Oracle/src/bin/signal-first-receive-oracle.rs) establishes a
session from a test recipient's prekey bundle and produces genuine
sealed-sender v1 envelopes carrying PreKeySignalMessages. The script then

* computes everything the recipient must compute with a reference written here
  independently of the Lean (hashlib/hmac, the `cryptography` library, a
  generic protobuf reader, plain integer arithmetic for Curve25519);
* lowers each kernel with circuit_cache.py, evaluates the flat gate list in the
  order of operations the runtime would follow (playing the field engine; the
  KEM decapsulation is done by libsignal in the oracle process), and compares
  every output field with the reference;
* builds, from the conversation record the kernels produced, a reply
  SignalMessage with a Python reference of the existing send path, and has the
  libsignal sender decrypt it;
* tampers with envelopes, MACs, certificates and agreements and requires every
  such run to be rejected with nothing released.

`--reference` runs only the Python reference against the oracle (no kernels).
`--build-oracle` builds the oracle offline first.
Nothing is sent to any network service.
"""
import base64,hashlib,hmac,json,os,random,subprocess,sys
from pathlib import Path
from cryptography.hazmat.primitives.ciphers import Cipher,algorithms,modes
from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey,X25519PublicKey
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
TARGET=ROOT/'.deps/signal-established-send-oracle-target'
ORACLE=TARGET/'debug/signal-first-receive-oracle'
P=2**255-19;ELL=2**252+27742317777372353535851937790883648493
D=-121665*pow(121666,-1,P)%P;SQRT_M1=pow(2,(P-1)//4,P);BASE_Y=4*pow(5,-1,P)%P

def build_oracle():
    environment=dict(os.environ,CARGO_TARGET_DIR=str(TARGET),CARGO_HOME=str(ROOT/'.deps/libsignal-cargo-home'))
    run=subprocess.run(['cargo','+nightly-2025-09-24','build','--offline','--locked','--ignore-rust-version','--bin','signal-first-receive-oracle'],
        cwd=ROOT/'signal_backend/Oracle',env=environment,capture_output=True,text=True)
    if run.returncode:
        at=run.stderr.find('error');print(run.stderr[at:at+6000]);raise SystemExit(1)

class Oracle:
    def __init__(self):self.process=subprocess.Popen([str(ORACLE)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True)
    def ask(self,**command):
        self.process.stdin.write(json.dumps(command)+'\n');self.process.stdin.flush();line=self.process.stdout.readline()
        if not line:raise RuntimeError('oracle exited')
        return json.loads(line)
    def close(self):self.process.stdin.close();self.process.wait()

# ---- circuit evaluation (as in check_establish_kernels.py) -----------------
KERNELS={}
def kernel(*args):
    key=' '.join(map(str,args))
    if key in KERNELS:return KERNELS[key][0]
    out=subprocess.run([sys.executable,str(HERE/'circuit_cache.py'),'kernel',*map(str,args)],check=True,capture_output=True).stdout.decode().split()
    lines=Path(out[0]).read_text().split('\n');n,count,width=map(int,lines[1].split())
    if lines[0]!='EMP_HYBRID_BOOL_V1' or n!=int(out[2]) or width!=int(out[3]):raise ValueError('flat header')
    gates=[(row[0],*map(int,row.split()[1:])) for row in lines[2:2+count]];outputs=list(map(int,lines[2+count].split()[1:]))
    fields={};offset={'I':0,'O':0};opened={}
    for row in Path(out[4]).read_text().split('\n')[1:]:
        f=row.split()
        if len(f)>=3:
            fields[(f[0],f[1])]=(offset[f[0]],int(f[2]));offset[f[0]]+=int(f[2])
            if f[0]=='O' and len(f)>=4:opened[f[1]]=f[3]
    names={name for kind,name in fields if kind=='I'}
    def run(**values):
        if set(values)!=names:raise ValueError('%s inputs %s'%(key,sorted(names^set(values))))
        wires=[0]*n
        for name,data in values.items():
            start,bits=fields[('I',name)]
            if isinstance(data,bytes):
                if bits!=8*len(data):raise ValueError('%s input size %s: %d bits, got %d bytes'%(key,name,bits,len(data)))
                data=int.from_bytes(data,'little')
            if data>>bits:raise ValueError('input range '+name)
            for i in range(bits):wires[start+i]=(data>>i)&1
        for g in gates:
            if g[0]=='N':wires.append(1-wires[g[1]])
            elif g[0]=='X':wires.append(wires[g[1]]^wires[g[2]])
            else:wires.append(wires[g[1]]&wires[g[2]])
        bits=[wires[o] for o in outputs];result={}
        for (kind,name),(start,size) in fields.items():
            if kind=='O':
                value=sum(bits[start+i]<<i for i in range(size))
                result[name]=value.to_bytes(size//8,'little') if size%8==0 else value
        return result
    KERNELS[key]=(run,sum(g[0]=='A' for g in gates),opened);return run

# ---- references ------------------------------------------------------------
def mac(key,data):return hmac.digest(key,data,'sha256')
def hkdf(salt,ikm,info,n):
    prk=mac(salt,ikm);out=b'';prior=b''
    for i in range(1,(n+31)//32+1):prior=mac(prk,prior+info+bytes([i]));out+=prior
    return out[:n]
def x25519(private,public):return X25519PrivateKey.from_private_bytes(private).exchange(X25519PublicKey.from_public_bytes(public))
def public(private):return X25519PrivateKey.from_private_bytes(private).public_key().public_bytes_raw()
def word(data):return int.from_bytes(data,'little')%2**255
def le32(value):return value.to_bytes(32,'little')
def varint(n):
    out=b''
    while n>=128:out+=bytes([n%128+128]);n//=128
    return out+bytes([n])
def field(tag,data):return bytes([tag])+varint(len(data))+data
def aes_ctr(key,data):
    e=Cipher(algorithms.AES(key),modes.CTR(bytes(16))).encryptor();return e.update(data)+e.finalize()
def cbc_decrypt(key,iv,data):
    d=Cipher(algorithms.AES(key),modes.CBC(iv)).decryptor();return d.update(data)+d.finalize()
def cbc_encrypt(key,iv,plain):
    pad=16-len(plain)%16;e=Cipher(algorithms.AES(key),modes.CBC(iv)).encryptor();return e.update(plain+bytes([pad])*pad)+e.finalize()

def read_varint(data,at):
    value=0;shift=0
    while True:
        byte=data[at];at+=1;value|=(byte&127)<<shift;shift+=7
        if byte<128:return value,at
def protobuf(data):
    """[(field number, wire type, value, offset of value, width of the varint or length prefix)]"""
    out=[];at=0
    while at<len(data):
        key,at=read_varint(data,at);number,kind=key>>3,key&7
        if kind==0:value,end=read_varint(data,at);out.append((number,kind,value,at,end-at));at=end
        elif kind==1:out.append((number,kind,data[at:at+8],at,0));at+=8
        elif kind==2:size,start=read_varint(data,at);out.append((number,kind,data[start:start+size],start,start-at));at=start+size
        else:raise ValueError('wire type')
    if at!=len(data):raise ValueError('protobuf length')
    return out
def one(fields,number):
    found=[f for f in fields if f[0]==number]
    if len(found)!=1:raise ValueError('field %d'%number)
    return found[0]
def has(fields,number):return any(f[0]==number for f in fields)

# Edwards25519, affine, for the field engine's part.
def ed_add(p,q):
    (x1,y1),(x2,y2)=p,q;t=D*x1*x2*y1*y2%P
    return ((x1*y2+x2*y1)*pow(1+t,-1,P)%P,(y1*y2+x1*x2)*pow(1-t,-1,P)%P)
def ed_mul(k,p):
    acc=(0,1)
    while k:
        if k&1:acc=ed_add(acc,p)
        p=ed_add(p,p);k>>=1
    return acc
def ed_x(y):
    xx=(y*y-1)*pow(D*y*y+1,-1,P)%P;x=pow(xx,(P+3)//8,P)
    if (x*x-xx)%P:x=x*SQRT_M1%P
    return x,(x*x-xx)%P==0
BASE=(ed_x(BASE_Y)[0] if ed_x(BASE_Y)[0]%2==0 else P-ed_x(BASE_Y)[0],BASE_Y)
def recover(u):
    """`xeddsa-recover`: valid, x (root as computed, sign not chosen), y"""
    if (u+1)%P==0:return 0,0,0
    y=(u-1)*pow(u+1,-1,P)%P
    if (D*y*y+1)%P==0:return 0,0,y
    x,ok=ed_x(y);return int(ok),x,y
def xeddsa_check(x,y,flip,h,s):
    """`xeddsa-check`: [s]B - [h]A with A = (±x, y)"""
    a=((P-x)%P if flip else x,y);negative=((P-a[0])%P,a[1])
    return ed_add(ed_mul(h,negative),ed_mul(s,BASE))
def torsion(x,y):
    """`receive-torsion` up to projective scaling: zero outputs exactly for a torsion-free point"""
    t=ed_mul(ELL,(x,y));return t[0],(t[1]-1)%P
def xeddsa_verify(key,message,signature):
    """libsignal's verify_signature for a Montgomery public key, in the clear"""
    valid,x,y=recover(word(key))
    if not valid:return False
    sign=(signature[63]>>7)&(1 if x else 0);a=(y|(sign<<255)).to_bytes(32,'little')
    h=int.from_bytes(hashlib.sha512(signature[:32]+a+message).digest(),'little')%ELL
    s=int.from_bytes(signature[32:],'little')&(2**255-1)   # the top bit carries the sign of A
    if s>>253:return False
    rx,ry=xeddsa_check(x,y,(x&1)^sign,h,s&(2**253-1))
    return (ry|((rx&1)<<255)).to_bytes(32,'little')==signature[:32]

LABEL=b'WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024'
def content_plaintext(body,timestamp=1900000000123,profile=bytes(range(32))):
    """A Signal Content with a data message (body, profile key, timestamp), padded as the clients pad"""
    data=field(10,body)+field(50,profile)+b'\x38'+varint(timestamp);content=field(10,data)
    return (content+b'\x80').ljust((len(content)+1+79)//80*80-1,b'\0')

def reference(fx,envelope,now,trust_root_checked_server,jump_allowed=16):
    """Everything the recipient computes, in the clear. Raises on any failed check."""
    r={};bob=bytes.fromhex(fx['bob_identity_private']);bob_public=bytes.fromhex(fx['bob_identity'])[1:]
    if envelope[0]!=0x11:raise ValueError('version')
    outer=protobuf(envelope[1:]);ephemeral=one(outer,1)[2];static=one(outer,2)[2];message=one(outer,3)[2]
    if ephemeral[0]!=5 or len(ephemeral)!=33:raise ValueError('ephemeral')
    r['ephemeral']=ephemeral[1:];r['agreement1']=x25519(bob,ephemeral[1:])
    first=hkdf(b'UnidentifiedDelivery'+b'\x05'+bob_public+ephemeral,r['agreement1'],b'',96)
    if mac(first[64:],static[:-10])[:10]!=static[-10:]:raise ValueError('static mac')
    key=aes_ctr(first[32:64],static[:-10])
    if key[0]!=5 or len(key)!=33:raise ValueError('static key')
    r['sender_identity']=key[1:];r['chain']=first[:32];r['agreement2']=x25519(bob,key[1:])
    second=hkdf(first[:32]+static,r['agreement2'],b'',96)
    if mac(second[64:],message[:-10])[:10]!=message[-10:]:raise ValueError('message mac')
    usmc=aes_ctr(second[32:64],message[:-10]);r['content']=usmc;fields=protobuf(usmc)
    r['type']=one(fields,1)[2];certificate=one(fields,2)[2];inner=one(fields,3)[2];r['hint']=has(fields,4)
    r['certificate']=certificate;r['message']=inner
    # certificate
    signed=protobuf(certificate);body=one(signed,1)[2];signature=one(signed,2)[2];c=protobuf(body)
    r['e164']=one(c,1)[2] if has(c,1) else None;r['device']=one(c,2)[2];expires=int.from_bytes(one(c,3)[2],'little')
    if one(c,4)[2]!=key:raise ValueError('certificate identity')
    if now>expires:raise ValueError('expired')
    if has(c,5):
        if one(c,5)[2]!=trust_root_checked_server['certificate']:raise ValueError('server certificate')
        r['signer']=one(c,5)[2]
    else:
        if one(c,8)[2]!=trust_root_checked_server['id']:raise ValueError('server id')
        r['signer']=varint(one(c,8)[2])
    r['uuid']=bytes.fromhex(one(c,6)[2].decode().replace('-','')) if has(c,6) else one(c,7)[2]
    if not xeddsa_verify(trust_root_checked_server['key'],body,signature):raise ValueError('certificate signature')
    r['certificate_body']=body;r['certificate_signature']=signature
    # PreKeySignalMessage
    if r['type']!=1 or inner[0]>>4!=4:raise ValueError('type')
    pre=protobuf(inner[1:]);r['one_time_id']=one(pre,1)[2] if has(pre,1) else None
    base=one(pre,2)[2];identity=one(pre,3)[2];signal=one(pre,4)[2]
    r['registration']=one(pre,5)[2];r['signed_id']=one(pre,6)[2];r['kyber_id']=one(pre,7)[2];ciphertext=one(pre,8)[2]
    if identity!=key or base[0]!=5 or ciphertext[0]!=8 or len(ciphertext)!=1569:raise ValueError('prekey fields')
    r['base']=base[1:];r['kyber_ciphertext']=ciphertext[1:];r['signal']=signal
    r['widths']=[one(pre,1)[4] if has(pre,1) else 0,one(pre,5)[4],one(pre,6)[4],one(pre,7)[4]]
    if int.from_bytes(base[1:],'little')>=P:raise ValueError('base range')
    valid,bx,by=recover(word(base[1:]))
    if not valid or torsion(bx,by)!=(0,0):raise ValueError('base torsion')
    # SignalMessage
    if signal[0]>>4!=4:raise ValueError('signal version')
    sm=protobuf(signal[1:-8]);ratchet=one(sm,1)[2];r['counter']=one(sm,2)[2];r['previous']=one(sm,3)[2]
    body_ct=one(sm,4)[2];pq=one(sm,5)[2];r['ratchet']=ratchet[1:];r['addresses']=has(sm,6)
    r['signal_widths']=[one(sm,2)[4],one(sm,3)[4]];r['ciphertext']=body_ct
    if pq[0]!=1 or pq[1]!=1 or pq[2]>=128:raise ValueError('post-quantum message')
    r['pq_index']=pq[2];r['pq_message']=pq
    if r['addresses']:
        expected=b'\0'+r['uuid']+bytes([r['device']])+b'\0'+bytes.fromhex(fx['bob_uuid'].replace('-',''))+b'\x01'
        if one(sm,6)[2]!=expected:raise ValueError('addresses')
    return r

def reference_session(fx,r,kem_secret,ratchet_private,ours):
    """Keys, plaintext and records from the parsed message (reference for `receive-session`)"""
    bob=bytes.fromhex(fx['bob_identity_private']);spk=bytes.fromhex(fx['signed_prekey_private']);otp=bytes.fromhex(fx['one_time_prekey_private'])
    bob_public=bytes.fromhex(fx['bob_identity'])[1:]
    a=dict(dh1=x25519(spk,r['sender_identity']),dh2=x25519(bob,r['base']),dh3=x25519(spk,r['base']),
        receive=x25519(spk,r['ratchet']),send=x25519(ratchet_private,r['ratchet']),ratchet_public=public(ratchet_private))
    if r['one_time_id'] is not None:a['dh4']=x25519(otp,r['base'])
    secret=b'\xff'*32+a['dh1']+a['dh2']+a['dh3']+a.get('dh4',b'')+kem_secret
    hs=hkdf(bytes(32),secret,LABEL,96);r1=hkdf(hs[:32],a['receive'],b'WhisperRatchet',64);r2=hkdf(r1[:32],a['send'],b'WhisperRatchet',64)
    pqc=hkdf(bytes(32),hs[64:],b'Signal PQ Ratchet V1 Chain  Start',96)
    chain=r1[32:]
    for _ in range(r['counter']):chain=mac(chain,b'\x02')
    pq_key=pqc[32:64]
    for i in range(1,r['pq_index']+1):
        out=hkdf(bytes(32),pq_key,i.to_bytes(4,'big')+b'Signal PQ Ratchet V1 Chain Next',64);pq_key,pq_message_key=out[:32],out[32:]
    keys=hkdf(pq_message_key,mac(chain,b'\x01'),b'WhisperMessageKeys',80);signal=r['signal']
    if mac(keys[32:64],b'\x05'+r['sender_identity']+b'\x05'+bob_public+signal[:-8])[:8]!=signal[-8:]:raise ValueError('message MAC')
    padded=cbc_decrypt(keys[:32],keys[64:],r['ciphertext']);pad=padded[-1]
    if not 1<=pad<=16 or padded[-pad:]!=bytes([pad])*pad:raise ValueError('padding')
    plain=padded[:-pad]
    session=bytes([4])+bytes(8)+a['ratchet_public']+r2[32:]+pqc[64:]+bytes(4)+bytes(7)+b'\x01'+b'\x00'+bob_public+r['sender_identity']+bytes(80)
    metadata=r['uuid']+ours['access']+bytes(8)+ours['request']+bytes([r['device']])+r['registration'].to_bytes(4,'big')+bytes(4)
    receiver=r2[:32]+mac(chain,b'\x02')+r['ratchet']+(r['counter']+1).to_bytes(4,'big')+pqc[:32]+pq_key+r['pq_index'].to_bytes(4,'big')+r['base']
    return dict(a=a,plain=plain,conversation=ours['certificate']+session+metadata,receiver=receiver,
        plaintext=len(plain).to_bytes(8,'big')+plain.ljust(len(r['ciphertext']),b'\0'),receiver_chain_next=mac(chain,b'\x02'))

def reference_text(plain):
    stripped=plain.rstrip(b'\0')
    if stripped[-1]!=0x80:raise ValueError('content padding')
    return one(protobuf(one(protobuf(stripped[:-1]),1)[2]),1)[2]

def reference_reply(conversation,cert,plain):
    """A SignalMessage built from a conversation record as the established send path builds it
    (TlsMpc/HybridKernels.lean, signalSealFixed: no addresses, chunk-less post-quantum message)."""
    session=conversation[cert:cert+262]
    counter,previous=int.from_bytes(session[1:5],'big'),int.from_bytes(session[5:9],'big')
    ratchet,chain,pq_chain=session[9:41],session[41:73],session[73:105];pq_counter=int.from_bytes(session[105:109],'big');epoch=int.from_bytes(session[109:117],'big')
    sender,receiver=session[118:150],session[150:182]
    pq=hkdf(bytes(32),pq_chain,(pq_counter+1).to_bytes(4,'big')+b'Signal PQ Ratchet V1 Chain Next',64)
    keys=hkdf(pq[32:],mac(chain,b'\x01'),b'WhisperMessageKeys',80)
    pq_message=b'\x01'+varint(epoch)+varint(pq_counter+1)+b'\x00'
    content=bytes([session[0]<<4|session[0]])+field(10,b'\x05'+ratchet)+b'\x10'+varint(counter)+b'\x18'+varint(previous)+field(34,cbc_encrypt(keys[:32],keys[64:80],plain))+field(42,pq_message)
    return content+mac(keys[32:64],b'\x05'+sender+b'\x05'+receiver+content)[:8]

# ---- one scenario ----------------------------------------------------------
def flags(data):
    if any(b not in (0,255) for b in data):raise AssertionError('flag bytes')
    return [b==255 for b in data]
def width(group):
    if sum(group)!=1:raise AssertionError('width flags %s'%group)
    return group.index(True)+1
def flip(data,at):return data[:at]+bytes([data[at]^1])+data[at+1:]
def zero(*values):return not any(any(v) if isinstance(v,bytes) else v for v in values)

def scenario(name,report,use_kernels,rng,seed,style,one_time,e164,hint,body,jump=0,count=1,ids=(77,17,23),registration=1234):
    now=1900000000000;plain=content_plaintext(body);oracle=Oracle()
    fx=oracle.ask(mode='init',seed=seed,one_time=one_time,style=style,e164=e164,hint=hint,count=count,plaintext=plain.hex(),
        one_time_id=ids[0],signed_id=ids[1],kyber_id=ids[2],alice_registration=registration,alice_device=1,expires=2000000000000,now=now,server_id=3)
    raw=lambda k:bytes.fromhex(fx[k]);envelope=bytes.fromhex(fx['envelopes'][count-1])
    # The server certificate is validated once in the clear against the trust root (libsignal: ServerCertificate::validate).
    server=dict(key=raw('server_public')[1:],certificate=raw('server_certificate'),id=fx['server_id'])
    if server['certificate']:
        sc=protobuf(server['certificate']);inner=protobuf(one(sc,1)[2])
        if one(inner,2)[2]!=raw('server_public') or not xeddsa_verify(raw('trust_root')[1:],one(sc,1)[2],one(sc,2)[2]):raise AssertionError('server certificate')
    r=reference(fx,envelope,now,server)
    kem_secret=bytes.fromhex(oracle.ask(mode='decapsulate',ciphertext='08'+r['kyber_ciphertext'].hex())['secret'])
    ratchet_private=rng.randbytes(32);CERT=40
    ours=dict(certificate=rng.randbytes(CERT),access=rng.randbytes(16),request=rng.randbytes(8))
    s=reference_session(fx,r,kem_secret,ratchet_private,ours)
    if s['plain']!=plain or reference_text(s['plain'])!=body:raise AssertionError('reference plaintext')
    if r['counter']!=count-1 or r['pq_index']!=count:raise AssertionError('counters %d %d'%(r['counter'],r['pq_index']))
    lib=fx['libsignal_recipient']
    if count==1 and (bytes.fromhex(lib['receiver_chain_key'])!=s['receiver_chain_next'] or lib['receiver_chain_index']!=1 or
            bytes.fromhex(lib['receiver_ratchet_key'])[1:]!=r['ratchet'] or lib['remote_registration']!=r['registration'] or
            lib['previous_counter']!=0 or lib['sender_chain_index']!=0 or bytes.fromhex(lib['plaintext'])!=plain):
        raise AssertionError('reference disagrees with the libsignal recipient')
    row=dict(style=style,one_time_prekey=one_time,phone_number=e164,content_hint=hint,envelope_bytes=len(envelope),body_bytes=len(body),
        counter=r['counter'],reference_matches_libsignal_recipient=count==1,addresses=r['addresses'],post_quantum_payload_bytes=len(r['pq_message'])-3)
    conversation=s['conversation']
    if use_kernels:conversation=kernels(fx,envelope,now,server,r,s,kem_secret,ratchet_private,ours,row,jump,body,CERT)
    # The libsignal sender decrypts a reply built from the conversation record.
    reply_plain=b'reply from the new session'+bytes([0x80])+bytes(13)
    answer=oracle.ask(mode='reply',wire=reference_reply(conversation,CERT,reply_plain).hex())
    if not answer.get('accepted') or bytes.fromhex(answer['plaintext'])!=reply_plain:raise AssertionError('libsignal sender rejected the reply: %s'%answer)
    second=oracle.ask(mode='reply',wire=reference_reply(conversation[:CERT+1]+(1).to_bytes(4,'big')+conversation[CERT+5:CERT+41]+mac(conversation[CERT+41:CERT+73],b'\x02')+
        hkdf(bytes(32),conversation[CERT+73:CERT+105],(1).to_bytes(4,'big')+b'Signal PQ Ratchet V1 Chain Next',64)[:32]+(1).to_bytes(4,'big')+conversation[CERT+109:],CERT,reply_plain).hex())
    if not second.get('accepted'):raise AssertionError('second reply rejected: %s'%second)
    row['replies_decrypted_by_libsignal_sender']=2;oracle.close();report[name]=row

def kernels(fx,envelope,now,server,r,s,kem_secret,ratchet_private,ours,row,jump,body,CERT):
    raw=lambda k:bytes.fromhex(fx[k]);bob=raw('bob_identity_private');bob_public=raw('bob_identity')[1:];SIZE=len(envelope);rejected=0
    # 1-3
    got=kernel('receive-envelope-point',SIZE)(envelope=envelope)
    if got['ephemeralPoint']!=word(r['ephemeral']):raise AssertionError('ephemeral point')
    static=kernel('receive-unseal-static',SIZE)
    st=static(envelope=envelope,ourIdentity=bob_public,agreement=word(r['agreement1']))
    if st['staticValid']!=b'\xff' or st['senderIdentity']!=r['sender_identity'] or st['senderPoint']!=word(r['sender_identity']) or st['chain']!=r['chain']:raise AssertionError('unseal static')
    for bad in (static(envelope=flip(envelope,50),ourIdentity=bob_public,agreement=word(r['agreement1'])),
            static(envelope=flip(envelope,0),ourIdentity=bob_public,agreement=word(r['agreement1'])),
            static(envelope=flip(envelope,10),ourIdentity=bob_public,agreement=word(r['agreement1'])),
            static(envelope=envelope,ourIdentity=bob_public,agreement=word(flip(r['agreement1'],3))),
            static(envelope=envelope,ourIdentity=flip(bob_public,0),agreement=word(r['agreement1'])),
            static(envelope=envelope,ourIdentity=bob_public,agreement=0)):
        if not zero(*bad.values()):raise AssertionError('unseal static released something after a failed check')
        rejected+=1
    # 4-5
    unseal=kernel('receive-unseal-message',SIZE)
    um=unseal(envelope=envelope,staticValid=st['staticValid'],chain=st['chain'],agreement=word(r['agreement2']))
    if um['valid']!=b'\xff' or um['content']!=r['content']:raise AssertionError('unseal message')
    for bad in (unseal(envelope=flip(envelope,SIZE-1),staticValid=st['staticValid'],chain=st['chain'],agreement=word(r['agreement2'])),
            unseal(envelope=flip(envelope,200),staticValid=st['staticValid'],chain=st['chain'],agreement=word(r['agreement2'])),
            unseal(envelope=envelope,staticValid=b'\0',chain=st['chain'],agreement=word(r['agreement2'])),
            unseal(envelope=envelope,staticValid=st['staticValid'],chain=flip(st['chain'],0),agreement=word(r['agreement2'])),
            unseal(envelope=envelope,staticValid=st['staticValid'],chain=st['chain'],agreement=0)):
        if not zero(*bad.values()):raise AssertionError('unseal message released something after a failed check')
        rejected+=1
    C0,C1=um['certificateLength'];U=len(um['content'])
    if (C0&127)+128*C1!=len(r['certificate']):raise AssertionError('certificate length')
    # 6-7
    shape=kernel('receive-content-shape',U,C0,C1)(content=um['content'],valid=um['valid'])['shape']
    plain_flag,hinted=flags(shape[:2]);present=shape[2];length=shape[3]
    if plain_flag==hinted or hinted!=r['hint'] or (present==255)!=(r['e164'] is not None) or length!=(len(r['e164']) if r['e164'] else 0):raise AssertionError('content shape %s'%shape.hex())
    if not zero(kernel('receive-content-shape',U,C0,C1)(content=um['content'],valid=b'\0')['shape']):raise AssertionError('content shape opened without validity')
    HINT=int(hinted);split=kernel('receive-content',U,C0,C1,HINT)
    parts=split(content=um['content'],valid=um['valid'])
    if parts['valid']!=b'\xff' or parts['messageType']!=bytes([r['type']]) or parts['certificate']!=r['certificate'] or parts['message']!=r['message']:raise AssertionError('content split')
    if not zero(*kernel('receive-content',U,C0,C1,1-HINT)(content=um['content'],valid=um['valid']).values()):raise AssertionError('content split accepted the wrong layout')
    if not zero(*split(content=um['content'],valid=b'\0').values()) or not zero(*split(content=flip(um['content'],0),valid=um['valid']).values()):raise AssertionError('content split')
    rejected+=3
    # 8-10
    cert=kernel('receive-certificate',C0,C1,present,length);verify=kernel('receive-certificate-verified')
    server_valid,sx,sy=recover(word(server['key']))
    def certificate(certificate=parts['certificate'],valid=parts['valid'],identity=st['senderIdentity'],signer=r['signer'],now=now,rx=None):
        c=cert(certificate=certificate,valid=valid,senderIdentity=identity,signer=signer,now=now.to_bytes(8,'big'),serverX=sx,serverY=sy)
        point=xeddsa_check(sx,sy,c['flip'],int.from_bytes(c['challenge'],'little'),c['scalar'])
        v=verify(certificateValid=c['certificateValid'],signature=c['signature'],serverValid=server_valid,rx=point[0] if rx is None else point[0]^rx,ry=point[1])   # R is ry with the parity of rx: a tampered rx must change the parity
        return c,v['verified']
    c,verified=certificate()
    if c['certificateValid']!=b'\xff' or verified!=b'\xff' or c['uuid']!=r['uuid'] or c['deviceId']!=bytes([r['device']]) or c['signature']!=r['certificate_signature']:raise AssertionError('certificate')
    at=parts['certificate'].index(r['sender_identity'])
    for why,bad in (('expired',certificate(now=2000000000001)),('other signer',certificate(signer=flip(r['signer'],len(r['signer'])-1))),
            ('identity',certificate(identity=flip(st['senderIdentity'],5))),('signature',certificate(certificate=flip(parts['certificate'],len(parts['certificate'])-1))),
            ('signed body',certificate(certificate=flip(parts['certificate'],at-8))),('invalid content',certificate(valid=b'\0')),('point',certificate(rx=1))):
        if bad[1]!=b'\0':raise AssertionError('certificate accepted: '+why)
        rejected+=1
    if certificate(now=2000000000000)[1]!=b'\xff':raise AssertionError('certificate rejected at its expiry time')
    if not zero(certificate(valid=b'\0')[0]['uuid'],certificate(valid=b'\0')[0]['deviceId']):raise AssertionError('certificate released identity without validity')
    # 11-12
    N=len(parts['message']);sh=flags(kernel('receive-prekey-shape',N)(message=parts['message'],valid=parts['valid'])['shape'])
    Pw=width(sh[1:6]) if sh[0] else 0;R,S,K=width(sh[6:11]),width(sh[11:16]),width(sh[16:21])
    if [Pw,R,S,K]!=r['widths']:raise AssertionError('prekey shape %s %s'%([Pw,R,S,K],r['widths']))
    opener=kernel('receive-prekey-open',N,Pw,R,S,K)
    po=opener(message=parts['message'],valid=parts['valid'],messageType=parts['messageType'],senderIdentity=st['senderIdentity'])
    if (po['prekeyValid']!=b'\xff' or po['basePoint']!=word(r['base']) or po['ratchetPoint']!=word(r['ratchet']) or
            po['oneTimePrekeyId']!=(r['one_time_id'] or 0).to_bytes(4,'big') or po['signedPrekeyId']!=r['signed_id'].to_bytes(4,'big') or
            po['kyberPrekeyId']!=r['kyber_id'].to_bytes(4,'big') or po['kyberCiphertext']!=r['kyber_ciphertext']):raise AssertionError('prekey open')
    for bad in (opener(message=parts['message'],valid=b'\0',messageType=parts['messageType'],senderIdentity=st['senderIdentity']),
            opener(message=parts['message'],valid=parts['valid'],messageType=b'\x02',senderIdentity=st['senderIdentity']),
            opener(message=parts['message'],valid=parts['valid'],messageType=parts['messageType'],senderIdentity=flip(st['senderIdentity'],0)),
            opener(message=flip(parts['message'],N-1569),valid=parts['valid'],messageType=parts['messageType'],senderIdentity=st['senderIdentity'])):
        if not zero(*bad.values()):raise AssertionError('prekey open released something after a failed check')
        rejected+=1
    # 13-15
    base_valid,bx,by=recover(po['basePoint']);tx,ty=torsion(bx,by)
    ss=kernel('receive-signal-shape',N,Pw,R,S,K)(message=parts['message'],valid=po['prekeyValid'])['shape'];sf=flags(ss[:10])
    CW,PW=width(sf[:5]),width(sf[5:10]);L0,L1=ss[10],ss[11];ADDR=int(flags(ss[12:13])[0])
    if [CW,PW]!=r['signal_widths'] or (L0 if L1==0 else (L0&127)+128*L1)!=len(r['ciphertext']) or bool(ADDR)!=r['addresses']:raise AssertionError('signal shape')
    # 16
    name=('receive-session',CERT,N,Pw,R,S,K,CW,PW,L0,L1,ADDR,jump);session=kernel(*name);a=s['a']
    def run(**change):
        values=dict(message=parts['message'],prekeyValid=po['prekeyValid'],verified=verified,senderIdentity=st['senderIdentity'],ourIdentity=bob_public,
            localAddress=bytes.fromhex(fx['bob_uuid'].replace('-',''))+b'\x01',uuid=c['uuid'],deviceId=c['deviceId'],dh1=word(a['dh1']),dh2=word(a['dh2']),dh3=word(a['dh3']),
            kemSecret=kem_secret,receiveAgreement=word(a['receive']),sendAgreement=word(a['send']),ratchetPublic=word(a['ratchet_public']),
            baseValid=base_valid,torsionX=tx,torsionY=ty,certificate=ours['certificate'],accessKey=ours['access'],requestId=ours['request'])
        if Pw:values['dh4']=word(a['dh4'])
        values.update(change);return session(**values)
    out=run()
    if out['status']!=b'\xff' or out['conversation']!=s['conversation'] or out['receiver']!=s['receiver'] or out['plaintext']!=s['plaintext']:
        raise AssertionError('session: status %s conversation %s receiver %s plaintext %s'%(out['status'].hex(),out['conversation']==s['conversation'],out['receiver']==s['receiver'],out['plaintext']==s['plaintext']))
    signal_at=parts['message'].index(r['signal'])
    tampered=[dict(message=flip(parts['message'],signal_at+len(r['signal'])-1)),dict(message=flip(parts['message'],signal_at+len(r['signal'])-20)),
        dict(message=flip(parts['message'],signal_at+60)),dict(prekeyValid=b'\0'),dict(verified=b'\0'),dict(verified=b'\x01'),dict(dh1=word(flip(a['dh1'],0))),dict(dh2=0),
        dict(kemSecret=flip(kem_secret,31)),dict(receiveAgreement=word(flip(a['receive'],9))),dict(sendAgreement=0),dict(baseValid=0),dict(torsionX=5),dict(torsionY=1),
        dict(senderIdentity=flip(st['senderIdentity'],1)),dict(ourIdentity=flip(bob_public,1))]
    if ADDR:tampered+=[dict(uuid=flip(c['uuid'],0)),dict(deviceId=b'\x02'),dict(localAddress=bytes(16)+b'\x01')]
    for change in tampered:
        bad=run(**change)
        if not zero(*bad.values()):raise AssertionError('session released something after a failed check: %s'%list(change))
        rejected+=1
    if jump:
        short=kernel('receive-session',CERT,N,Pw,R,S,K,CW,PW,L0,L1,ADDR,jump-1)
        values=dict(message=parts['message'],prekeyValid=po['prekeyValid'],verified=verified,senderIdentity=st['senderIdentity'],ourIdentity=bob_public,
            localAddress=bytes.fromhex(fx['bob_uuid'].replace('-',''))+b'\x01',uuid=c['uuid'],deviceId=c['deviceId'],dh1=word(a['dh1']),dh2=word(a['dh2']),dh3=word(a['dh3']),
            kemSecret=kem_secret,receiveAgreement=word(a['receive']),sendAgreement=word(a['send']),ratchetPublic=word(a['ratchet_public']),
            baseValid=base_valid,torsionX=tx,torsionY=ty,certificate=ours['certificate'],accessKey=ours['access'],requestId=ours['request'])
        if Pw:values['dh4']=word(a['dh4'])
        if not zero(*short(**values).values()):raise AssertionError('a counter beyond the jump budget was accepted')
        rejected+=1
    # 17
    CLEN=len(r['ciphertext']);CAP=CLEN-6;text=kernel('receive-text',CLEN,CAP);t=text(plaintext=out['plaintext'])
    if t['status']!=b'\xff' or int.from_bytes(t['length'],'big')!=len(body) or t['text']!=body.ljust(CAP,b'\0'):raise AssertionError('text %s'%t)
    if not zero(*text(plaintext=bytes(8+CLEN)).values()):raise AssertionError('text released from a rejected session')
    row.update(kernel_outputs_match_reference=True,tampered_or_invalid_rejected_and_nothing_released=rejected,session_kernel=' '.join(map(str,name)))
    return out['conversation']

def field_program(rng):
    """The field program `receive-torsion` as defined in Lean (TlsMpc/ReceiveField.lean, evaluated on field values by
    EvalReceiveField.lean) against the reference: both outputs zero exactly for torsion-free points, and otherwise the
    same projective point."""
    valid,x,y=recover(word(public(rng.randbytes(32))))
    if not valid:raise AssertionError('fixture point')
    cases=[((x,y),True),(((P-x)%P,(P-y)%P),False),(ed_add((x,y),(SQRT_M1,0)),False),(BASE,True),((0,P-1),False)]
    for (px,py),free in cases:
        out=subprocess.run(['lake','env','lean','--run',str(HERE/'EvalReceiveField.lean'),str(px),str(py)],cwd=ROOT,check=True,capture_output=True,text=True).stdout.split()
        big_x,rest=int(out[0]),int(out[1]);tx,ty=torsion(px,py)
        if ((big_x,rest)==(0,0))!=free or ((tx,ty)==(0,0))!=free or (rest*tx-big_x*ty)%P or (big_x==0)!=(tx==0):raise AssertionError('receive-torsion')
    return dict(points=len(cases),zero_exactly_when_torsion_free=True)

def main():
    if '--build-oracle' in sys.argv:build_oracle()
    use=not '--reference' in sys.argv;rng=random.Random(20261111);report={}
    token=lambda n:base64.b64encode(json.dumps(dict(id=str(rng.getrandbits(128)),sig=rng.randbytes(n).hex())).encode())
    scenario('libsignal certificate, one-time prekey, content hint',report,use,rng,4101,'libsignal',True,False,True,token(64))
    scenario('server certificate with phone number, no one-time prekey',report,use,rng,4102,'server',False,True,False,token(8),ids=(1,300,70000),registration=77)
    scenario('certificate by reference, second message of the chain (first lost)',report,use,rng,4103,'reference',True,False,True,b'short token',jump=1,count=2,ids=(16777215,2,5))
    if use:report['field program receive-torsion']=field_program(rng)
    if use:report['kernels']={key:dict(and_gates=value[1],opened=sorted(n for n,k in value[2].items() if k=='1')) for key,value in sorted(KERNELS.items())}
    (HERE/('receive-kernels-report.json' if use else 'receive-reference-report.json')).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=1))
if __name__=='__main__':main()
