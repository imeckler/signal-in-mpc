#!/usr/bin/env python3
"""Check the session-establishment kernels (TlsMpc/EstablishKernels.lean).

This script is a CHECK only: it lowers each kernel with circuit_cache.py,
evaluates the flat gate list, and compares against references written here
independently of the Lean (hashlib/hmac, the `cryptography` library, and plain
integer arithmetic for Curve25519 and Kyber-1024). It plays the runtime's part
for the values the field engine supplies (X25519 agreements, the XEdDSA point
recovery and double-scalar multiplication) and for the KEM.

The final judge is an unmodified libsignal v0.106.1 RECIPIENT
(signal_backend/Oracle/src/bin/signal-bootstrap-peer-oracle.rs): it holds the
bundle's private keys, receives the PreKeySignalMessage taken out of the
kernel's sealed-sender envelope, and must decrypt it to the expected plaintext.
Nothing is sent to any network service.
"""
import hashlib,hmac,json,random,subprocess,sys
from pathlib import Path
from cryptography.hazmat.primitives.ciphers import Cipher,algorithms,modes
from cryptography.hazmat.primitives.asymmetric.x25519 import X25519PrivateKey,X25519PublicKey
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
ORACLE=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-bootstrap-peer-oracle'
P=2**255-19;ELL=2**252+27742317777372353535851937790883648493
D=-121665*pow(121666,-1,P)%P;SQRT_M1=pow(2,(P-1)//4,P)
BASE_Y=4*pow(5,-1,P)%P

# ---- circuit evaluation -------------------------------------------------
def kernel(*args):
    out=subprocess.run([sys.executable,str(HERE/'circuit_cache.py'),'kernel',*map(str,args)],check=True,capture_output=True).stdout.decode().split()
    lines=Path(out[0]).read_text().split('\n');n,count,width=map(int,lines[1].split())
    if lines[0]!='EMP_HYBRID_BOOL_V1' or n!=int(out[2]) or width!=int(out[3]):raise ValueError('flat header')
    gates=[(row[0],*map(int,row.split()[1:])) for row in lines[2:2+count]];outputs=list(map(int,lines[2+count].split()[1:]))
    fields={};offset={'I':0,'O':0}
    for row in Path(out[4]).read_text().split('\n')[1:]:
        f=row.split()
        if len(f)>=3:fields[(f[0],f[1])]=(offset[f[0]],int(f[2]));offset[f[0]]+=int(f[2])
    names={name for kind,name in fields if kind=='I'}
    def run(**values):
        if set(values)!=names:raise ValueError('inputs %s'%sorted(names^set(values)))
        wires=[0]*n
        for name,data in values.items():
            start,bits=fields[('I',name)]
            if isinstance(data,bytes):
                if bits!=8*len(data):raise ValueError('input size '+name)
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
    return run,sum(g[0]=='A' for g in gates)

# ---- references ---------------------------------------------------------
def mac(key,data):return hmac.digest(key,data,'sha256')
def hkdf(salt,ikm,info,n):
    prk=mac(salt,ikm);out=b'';prior=b''
    for i in range(1,(n+31)//32+1):prior=mac(prk,prior+info+bytes([i]));out+=prior
    return out[:n]
def x25519(private,public):return X25519PrivateKey.from_private_bytes(private).exchange(X25519PublicKey.from_public_bytes(public))
def public(private):return X25519PrivateKey.from_private_bytes(private).public_key().public_bytes_raw()
def word(data):return int.from_bytes(data,'little')%2**255
def varint(n):
    out=b''
    while n>=128:out+=bytes([n%128+128]);n//=128
    return out+bytes([n])
def varint5(n):return bytes(((n>>(7*i))&127)|(128 if i<4 else 0) for i in range(5))
def field(tag,data):return bytes([tag])+varint(len(data))+data

# Edwards25519, affine, for the field engine's part of XEdDSA.
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
BASE=(ed_x(BASE_Y)[0] if ed_x(BASE_Y)[0]%2==0 else P-ed_x(BASE_Y)[0],BASE_Y)   # the base point has even x
def recover(u):
    """valid, x (root as computed, sign not chosen), y"""
    if (u+1)%P==0:return 0,0,0
    y=(u-1)*pow(u+1,-1,P)%P
    if (D*y*y+1)%P==0:return 0,0,y
    x,ok=ed_x(y);return int(ok),x,y
def xeddsa_check(x,y,flip,h,s):
    a=((P-x)%P if flip else x,y);negative=((P-a[0])%P,a[1])
    return ed_add(ed_mul(h,negative),ed_mul(s,BASE))

# Kyber-1024 (round 3, as libsignal's key type 8) encapsulation.
Q=3329
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
def parse(seed):
    stream=hashlib.shake_128(seed).digest(840);out=[];i=0
    while len(out)<256:
        d1=stream[i]|((stream[i+1]&15)<<8);d2=(stream[i+1]>>4)|(stream[i+2]<<4);i+=3
        if d1<Q:out.append(d1)
        if d2<Q and len(out)<256:out.append(d2)
    return out
def cbd2(data):
    bits=int.from_bytes(data,'little')
    return [(((bits>>(4*i))&1)+((bits>>(4*i+1))&1)-((bits>>(4*i+2))&1)-((bits>>(4*i+3))&1))%Q for i in range(256)]
def compress(poly,d):return [(((x<<d)+Q//2)//Q)%(1<<d) for x in poly]
def pack(values,d):return sum(v<<(d*i) for i,v in enumerate(values)).to_bytes(len(values)*d//8,'little')
def unpack12(data):
    n=int.from_bytes(data,'little');return [(n>>(12*i))&4095 for i in range(256)]
def kyber_encapsulate(pk,randomness):
    h=lambda x:hashlib.sha3_256(x).digest()
    m=h(randomness);kr=hashlib.sha3_512(m+h(pk)).digest();kbar,coins=kr[:32],kr[32:]
    t=[unpack12(pk[384*i:384*i+384]) for i in range(4)];rho=pk[1536:]
    prf=lambda nonce:cbd2(hashlib.shake_256(coins+bytes([nonce])).digest(128))
    r=[ntt(prf(i)) for i in range(4)];e1=[prf(4+i) for i in range(4)];e2=prf(8)
    u=[padd(intt(padd(*[basemul(parse(rho+bytes([i,j])),r[j]) for j in range(4)])),e1[i]) for i in range(4)]
    message=[((m[i//8]>>(i%8))&1)*1665 for i in range(256)]
    v=padd(intt(padd(*[basemul(t[j],r[j]) for j in range(4)])),e2,message)
    ct=b''.join(pack(compress(p,11),11) for p in u)+pack(compress(v,5),5)
    return ct,hashlib.shake_256(kbar+h(ct)).digest(32)

def aes_cbc(key,iv,plain):
    pad=16-len(plain)%16;e=Cipher(algorithms.AES(key),modes.CBC(iv)).encryptor();return e.update(plain+bytes([pad])*pad)+e.finalize()
def aes_ctr(key,data):
    e=Cipher(algorithms.AES(key),modes.CTR(bytes(16))).encryptor();return e.update(data)+e.finalize()

LABEL=b'WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024'
def expected_session(c):
    secret=b'\xff'*32+c['dh1']+c['dh2']+c['dh3']+(c['dh4'] if c['one_time'] else b'')+c['kem_secret']
    handshake=hkdf(bytes(32),secret,LABEL,96);ratchet=hkdf(handshake[:32],c['dh5'],b'WhisperRatchet',64)
    chain=hkdf(bytes(32),handshake[64:],b'Signal PQ Ratchet V1 Chain  Start',96)
    session=bytes([4])+bytes(8)+c['ratchet_public']+ratchet[32:]+chain[32:64]+bytes(4)+bytes(7)+b'\x01'+b'\x00'+c['sender']+c['identity']+bytes(80)
    metadata=c['uuid']+c['access']+bytes(8)+c['request']+bytes([c['device']])+c['registration'].to_bytes(4,'big')+bytes(4)
    pending=c['local_registration'].to_bytes(4,'big')+(c['one_time_id'] if c['one_time'] else 0).to_bytes(4,'big')+c['signed_id'].to_bytes(4,'big')+c['kyber_id'].to_bytes(4,'big')+c['base_public']+c['ciphertext']
    receiver=ratchet[:32]+handshake[32:64]+c['signed_prekey']+handshake[64:]+chain[:32]+chain[64:]
    return c['certificate']+session+metadata,pending,receiver
def text_input(text,timestamp):return b'\xff'+len(text).to_bytes(2,'big')+text.ljust(48,b'\0')+timestamp.to_bytes(8,'big')
def text_plaintext(text,timestamp):
    content=field(10,field(10,text)+b'\x38'+varint(timestamp));return (content+b'\x80').ljust(80,b'\0')
def expected_seal(c,conversation,pending,text,timestamp,ephemeral_private):
    """next conversation, PreKeySignalMessage, envelope"""
    n=len(c['certificate']);session=conversation[n:n+262];metadata=conversation[n+262:]
    counter,previous=int.from_bytes(session[1:5],'big'),int.from_bytes(session[5:9],'big')
    ratchet,chain,pq_chain=session[9:41],session[41:73],session[73:105];pq_counter=int.from_bytes(session[105:109],'big');epoch=int.from_bytes(session[109:117],'big')
    sender,receiver=session[118:150],session[150:182];plain=text_plaintext(text,timestamp)
    pq=hkdf(bytes(32),pq_chain,(pq_counter+1).to_bytes(4,'big')+b'Signal PQ Ratchet V1 Chain Next',64)
    keys=hkdf(pq[32:],mac(chain,b'\x01'),b'WhisperMessageKeys',80)
    addresses=b'\0'+c['local_uuid']+bytes([c['local_device']])+b'\0'+metadata[:16]+metadata[48:49]
    pq_message=b'\x01'+varint(epoch)+varint(pq_counter+1)+b'\x00'
    content=b'\x44'+field(10,b'\x05'+ratchet)+b'\x10'+varint(counter)+b'\x18'+varint(previous)+field(34,aes_cbc(keys[:32],keys[64:80],plain))+field(42,pq_message)+field(50,addresses)
    signal=content+mac(keys[32:64],b'\x05'+sender+b'\x05'+receiver+content)[:8]
    ids=[int.from_bytes(pending[4*i:4*i+4],'big') for i in range(4)]
    prekey=b'\x44'+(b'\x08'+varint5(ids[1]) if c['one_time'] else b'')+field(18,b'\x05'+pending[16:48])+field(26,b'\x05'+sender)+field(34,signal)+b'\x28'+varint5(ids[0])+b'\x30'+varint5(ids[2])+b'\x38'+varint5(ids[3])+field(66,b'\x08'+pending[48:])
    ephemeral=public(ephemeral_private)
    first=hkdf(b'UnidentifiedDelivery'+b'\x05'+receiver+b'\x05'+ephemeral,x25519(ephemeral_private,receiver),b'',96)
    static=aes_ctr(first[32:64],b'\x05'+sender);static+=mac(first[64:],static)[:10]
    second=hkdf(first[:32]+static,x25519(c['identity_private'],receiver),b'',96)
    usmc=b'\x08\x01'+field(18,c['certificate'])+field(26,prekey)
    message=aes_ctr(second[32:64],usmc);message+=mac(second[64:],message)[:10]
    envelope=b'\x11'+field(10,b'\x05'+ephemeral)+field(18,static)+field(26,message)
    session=session[:1]+(counter+1).to_bytes(4,'big')+session[5:41]+mac(chain,b'\x02')+pq[:32]+(pq_counter+1).to_bytes(4,'big')+session[109:117]+b'\x00'+session[118:182]+plain
    return c['certificate']+session+metadata,prekey,envelope

def oracle(commands):
    run=subprocess.run([str(ORACLE)],input=''.join(json.dumps(x)+'\n' for x in commands),capture_output=True,text=True,check=True)
    return [json.loads(line) for line in run.stdout.splitlines()]

def main():
    rng=random.Random(20261110);report={'kernels':{}}
    def load(*args):
        run,ands=kernel(*args);report['kernels'][' '.join(map(str,args))]=dict(and_gates=ands);return run
    challenges=load('establish-challenges');verify=load('establish-verified')
    CERT=40
    for seed,one_time in ((3027,True),(3031,False)):
        fx=oracle([dict(mode='init',seed=seed)])[0];raw=lambda k:bytes.fromhex(fx[k])
        identity,spk,otp,kyber=raw('bob_identity')[1:],raw('signed_prekey')[1:],raw('one_time_prekey')[1:],raw('kyber_prekey')[1:]
        if raw('kyber_prekey')[0]!=8 or len(kyber)!=1568:raise AssertionError('fixture Kyber key')
        ec_sig,pq_sig=raw('signed_signature'),raw('kyber_signature')
        # 1. points
        points=load('establish-points',int(one_time))
        got=points(identityKey=identity,signedPrekey=spk,**(dict(oneTimePrekey=otp) if one_time else {}))
        if got['identityPoint']!=word(identity) or got['signedPrekeyPoint']!=word(spk) or (one_time and got['oneTimePrekeyPoint']!=word(otp)):raise AssertionError('points')
        # 2-5. both signatures; then a tampered copy of each must fail
        valid,x,y=recover(word(identity))
        if not valid:raise AssertionError('identity key did not decode')
        def verification(ec,pq,valid=valid):
            c=challenges(identityX=x,identityY=y,signedPrekey=spk,signedPrekeySignature=ec,kyberPrekey=kyber,kyberPrekeySignature=pq)
            points={}
            for tag,sig,message in (('ec',ec,b'\x05'+spk),('pq',pq,b'\x08'+kyber)):
                sign=(sig[63]>>7)&(1 if x else 0);compressed=(y|(sign<<255)).to_bytes(32,'little')
                h=int.from_bytes(hashlib.sha512(sig[:32]+compressed+message).digest(),'little')%ELL
                if c[tag+'Flip']!=(x&1)^sign or c[tag+'Challenge']!=h.to_bytes(32,'little') or c[tag+'Scalar']!=int.from_bytes(sig[32:],'little')%2**253:raise AssertionError('challenge '+tag)
                points[tag]=xeddsa_check(x,y,c[tag+'Flip'],h,c[tag+'Scalar'])
            return verify(identityValid=valid,ecRx=points['ec'][0],ecRy=points['ec'][1],pqRx=points['pq'][0],pqRy=points['pq'][1],signedPrekeySignature=ec,kyberPrekeySignature=pq)['verified']
        verified=verification(ec_sig,pq_sig)
        if verified!=b'\xff':raise AssertionError('genuine bundle rejected')
        flip=lambda data,at:data[:at]+bytes([data[at]^1])+data[at+1:]
        for ec,pq,why in ((flip(ec_sig,40),pq_sig,'signed prekey s'),(ec_sig,flip(pq_sig,3),'Kyber prekey R'),(flip(ec_sig,63),pq_sig,'signed prekey high bit')):
            if verification(ec,pq)!=b'\x00':raise AssertionError('tampered signature accepted: '+why)
        if verification(ec_sig,pq_sig,valid=0)!=b'\x00':raise AssertionError('undecodable identity accepted')
        # 6-7. the field engine's agreements and the KEM (references)
        alice=raw('alice_private');base,ratchet,ephemeral=(rng.randbytes(32) for _ in range(3))
        ciphertext,kem_secret=kyber_encapsulate(kyber,rng.randbytes(32))
        c=dict(one_time=one_time,dh1=x25519(alice,spk),dh2=x25519(base,identity),dh3=x25519(base,spk),dh4=x25519(base,otp),dh5=x25519(ratchet,spk),
            kem_secret=kem_secret,ciphertext=ciphertext,base_public=public(base),ratchet_public=public(ratchet),sender=public(alice),identity=identity,signed_prekey=spk,
            certificate=rng.randbytes(CERT),uuid=bytes.fromhex('b2000000000040008000000000000002'),access=rng.randbytes(16),request=rng.randbytes(8),device=fx['device_id'],
            registration=fx['registration_id'],local_registration=rng.randrange(1,16381),one_time_id=fx['one_time_id'],signed_id=fx['signed_id'],kyber_id=fx['kyber_id'],
            local_uuid=bytes.fromhex('a2000000000040008000000000000001'),local_device=1,identity_private=alice)
        if c['sender']!=raw('alice_identity')[1:]:raise AssertionError('fixture identity')
        # 8. session
        session=load('establish-session',CERT,int(one_time))
        def establish(verified=verified,kem_status=b'\xff',dh2=c['dh2']):
            values=dict(verified=verified,kemStatus=kem_status,dh1=word(c['dh1']),dh2=word(dh2),dh3=word(c['dh3']),ratchetAgreement=word(c['dh5']),kemSecret=kem_secret,kemCiphertext=ciphertext,
                basePublic=word(c['base_public']),ratchetPublic=word(c['ratchet_public']),senderPublic=word(c['sender']),identityKey=identity,signedPrekey=spk,certificate=c['certificate'],
                uuid=c['uuid'],accessKey=c['access'],requestId=c['request'],deviceId=bytes([c['device']]),registrationId=c['registration'].to_bytes(4,'big'),
                localRegistrationId=c['local_registration'].to_bytes(4,'big'),signedPrekeyId=c['signed_id'].to_bytes(4,'big'),kyberPrekeyId=c['kyber_id'].to_bytes(4,'big'))
            if one_time:values.update(dh4=word(c['dh4']),oneTimePrekeyId=c['one_time_id'].to_bytes(4,'big'))
            return session(**values)
        out=establish();conversation,pending,receiver=expected_session(c)
        if out['status']!=b'\xff' or out['conversation']!=conversation or out['pending']!=pending or out['receiver']!=receiver:raise AssertionError('establish-session')
        for bad in (establish(verified=b'\x00'),establish(verified=b'\x01'),establish(kem_status=b'\x00'),establish(dh2=bytes(32))):
            if bad['status']!=b'\x00' or any(bad['conversation']) or any(bad['pending']) or any(bad['receiver']):raise AssertionError('establish-session released state after a failed check')
        # 9-10. two messages, each judged by the libsignal recipient
        seal=load('establish-seal',CERT,int(one_time),1,1,1,1)
        def send(record,text,timestamp,pending=pending):
            return seal(conversation=record,pending=pending,localAddress=c['local_uuid']+bytes([c['local_device']]),text=text_input(text,timestamp),
                ephemeralPublic=word(public(ephemeral)),senderPublic=word(c['sender']),ephemeralAgreement=word(x25519(ephemeral,identity)),staticAgreement=word(x25519(alice,identity)))
        commands=[dict(mode='init',seed=seed)];plaintexts=[];record=conversation;lengths=[]
        for index,text in enumerate((b'first message to a new contact',b'second, still unacknowledged')):
            timestamp=1900000000000+index;got=send(record,text,timestamp);record,prekey,envelope=expected_seal(c,record,pending,text,timestamp,ephemeral)
            if got['status']!=b'\xff' or got['conversation']!=record or got['envelope']!=envelope or got['timestamp']!=timestamp.to_bytes(8,'big'):raise AssertionError('establish-seal %d'%index)
            commands.append(dict(mode='check',wire=prekey.hex()));plaintexts.append(text_plaintext(text,timestamp).hex());lengths.append(len(envelope))
        replies=oracle(commands)[1:]
        for index,reply in enumerate(replies):
            if not reply.get('accepted') or reply['plaintext']!=plaintexts[index] or not reply['sender_identity_matches']:raise AssertionError('libsignal recipient rejected message %d: %s'%(index,{k:v for k,v in reply.items() if k!='session_record'}))
        if replies[0]['one_time_consumed']!=one_time:raise AssertionError('one-time prekey use')
        # A different contact's ids must not change the envelope length (five-byte varints).
        other=(2**32-1).to_bytes(4,'big')+bytes(4)+(5).to_bytes(4,'big')+(2**21).to_bytes(4,'big')+pending[16:]
        if len(send(conversation,b'x',1,pending=other)['envelope'])!=len(send(conversation,b'x',1)['envelope']):raise AssertionError('envelope length depends on ids')
        # A zero (failed) record sends nothing.
        dead=send(bytes(len(conversation)),b'x',1)
        if dead['status']!=b'\x00' or any(dead['envelope']):raise AssertionError('zero record produced an envelope')
        report['seed %d'%seed]=dict(one_time_prekey=one_time,bundle_signatures_verified=True,tampered_or_invalid_rejected=4,session_records_match_reference=True,
            failed_checks_release_nothing=4,messages_decrypted_by_libsignal_recipient=len(replies),envelope_bytes=lengths)
    (HERE/'establish-kernels-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
if __name__=='__main__':main()
