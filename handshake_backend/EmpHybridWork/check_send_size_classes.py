#!/usr/bin/env python3
"""Check the notify send path's size classes: `signal-seal-built CERT CLASS W1 W2 W3 W4`
(TlsMpc/HybridKernels.lean) and `PrivateTextNotification.buildPublic` (the controllers' part).

    check_send_size_classes.py texts        Lean's built messages against the reference (no kernel)
    check_send_size_classes.py reference    the method itself, on the reference's own messages (no kernel)
    check_send_size_classes.py CLASS        one size class of the kernel, 1..4

Run each through scripts/guarded.py, ONE AT A TIME: a class lowers a kernel of 2-3 million AND
gates (several GB) and evaluates it here.

This script is a CHECK only. Everything it compares against is written here, independently of
the Lean (hashlib/hmac, the `cryptography` library, a protobuf reader), or reused from the
establishment check's references (check_establish_kernels.py), which were themselves judged by
libsignal. What is checked for a class:

  * the controllers' message (Lean, run by `lake env lean --run BuildPublicText.lean`) is the
    Content a Signal client serializes for that text and timestamp, then 0x80, then zeros up to
    the next multiple of 80 bytes, and its class is that multiple;
  * the kernel, on that message and a session record, opens exactly the sealed-sender envelope
    the reference computes, keeps exactly the reference's next record, and its envelope has one
    length per class whatever the text;
  * the final judge is an unmodified libsignal v0.106.1 RECIPIENT
    (signal_backend/Oracle/src/bin/signal-bootstrap-peer-oracle.rs): it holds the bundle's
    private keys, receives the SignalMessage taken out of the kernel's envelope (inside the
    session's PreKeySignalMessage wrapper, as an unacknowledged session sends it) and must
    decrypt it to exactly the padded content, from which the text and timestamp are read back
    the way a client does (strip the padding, parse Content);
  * a message marked invalid, and a zero record, open nothing and leave the record unchanged.

Nothing is sent to any network service.
"""
import json,random,subprocess,sys
from array import array
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
sys.path.insert(0,str(HERE))
import check_establish_kernels as est   # references and the oracle runner only; no kernel is loaded by importing it
from check_establish_kernels import hkdf,mac,x25519,public,word,varint,varint5,field,aes_cbc,aes_ctr
CERT=244;SEED=3027;REPORT=HERE/'send-size-classes-report.json'

# ---- the kernel, evaluated from its flat gate list ----------------------
def kernel(*args):
    out=subprocess.run([sys.executable,str(HERE/'circuit_cache.py'),'kernel',*map(str,args)],check=True,capture_output=True).stdout.decode().split()
    with open(out[0]) as f:
        head=f.readline().strip();n,count,width=map(int,f.readline().split())
        if head!='EMP_HYBRID_BOOL_V1' or n!=int(out[2]) or width!=int(out[3]):raise ValueError('flat header')
        ops=bytearray(count);left=array('I',bytes(4*count));right=array('I',bytes(4*count))
        for i in range(count):
            row=f.readline().split();ops[i]=ord(row[0]);left[i]=int(row[1])
            if len(row)>2:right[i]=int(row[2])
        outputs=list(map(int,f.readline().split()[1:]))
    if len(outputs)!=width or set(ops)-set(b'ANX'):raise ValueError('flat body')
    fields={};offset={'I':0,'O':0}
    for row in Path(out[4]).read_text().split('\n')[1:]:
        f=row.split()
        if len(f)>=3:fields[(f[0],f[1])]=(offset[f[0]],int(f[2]));offset[f[0]]+=int(f[2])
    names={name for kind,name in fields if kind=='I'}
    def run(**values):
        if set(values)!=names:raise ValueError('inputs %s'%sorted(names^set(values)))
        wires=bytearray(n+count)
        for name,data in values.items():
            start,bits=fields[('I',name)]
            if isinstance(data,bytes):
                if bits!=8*len(data):raise ValueError('input size %s: %d bits for %d'%(name,8*len(data),bits))
                data=int.from_bytes(data,'little')
            if data>>bits:raise ValueError('input range '+name)
            for i in range(bits):wires[start+i]=(data>>i)&1
        at=n
        for op,a,b in zip(ops,left,right):
            if op==65:wires[at]=wires[a]&wires[b]
            elif op==88:wires[at]=wires[a]^wires[b]
            else:wires[at]=1-wires[a]
            at+=1
        bits=[wires[o] for o in outputs];result={}
        for (kind,name),(start,size) in fields.items():
            if kind=='O':result[name]=sum(bits[start+i]<<i for i in range(size)).to_bytes(size//8,'little')
        return result
    return run,ops.count(65),{name:bits for (kind,name),(_,bits) in fields.items()}

# ---- what a Signal client does with a text -------------------------------
def content_bytes(text,timestamp):
    """Content { dataMessage { body, timestamp } }"""
    return field(10,field(10,text)+b'\x38'+varint(timestamp))
def padded(text,timestamp):
    """(size class, padded plaintext): 0x80 after the content, zeros to a multiple of 80."""
    body=content_bytes(text,timestamp)+b'\x80';classes=-(-len(body)//80);return classes,body.ljust(80*classes,b'\0')
def built(text,timestamp):
    classes,plain=padded(text,timestamp);return classes,b'\xff\x00'+plain+timestamp.to_bytes(8,'big')
def read_varint(data,at):
    value=shift=0
    while True:
        if at>=len(data):raise ValueError('varint runs past the end')
        byte=data[at];at+=1;value|=(byte&127)<<shift;shift+=7
        if byte<128:return value,at
def parse(data):
    """A protobuf message's fields by key byte: varints and length-delimited only."""
    out={};at=0
    while at<len(data):
        key=data[at];at+=1
        if key in out:raise ValueError('repeated field')
        if key&7==0:out[key],at=read_varint(data,at)
        elif key&7==2:
            size,at=read_varint(data,at)
            if at+size>len(data):raise ValueError('field runs past the end')
            out[key]=data[at:at+size];at+=size
        else:raise ValueError('wire type')
    return out
def client_reads(plain):
    """(text, timestamp) from a decrypted plaintext: strip the padding, parse Content."""
    body=plain.rstrip(b'\0')
    if not body or body[-1]!=0x80:raise ValueError('padding')
    content=parse(body[:-1])
    if set(content)!={10}:raise ValueError('Content fields')
    message=parse(content[10])
    if set(message)!={10,0x38}:raise ValueError('DataMessage fields')
    return message[10],message[0x38]

def lean_built(cases):
    """[(class, built bytes) or None] from the Lean definition the controllers run."""
    args=['%s:%d'%(text.hex(),timestamp) for text,timestamp in cases]
    run=subprocess.run(['lake','env','lean','--run',str(HERE/'BuildPublicText.lean'),*args],cwd=ROOT,capture_output=True,text=True)
    if run.returncode!=0:raise RuntimeError('BuildPublicText: '+run.stderr[-800:])
    rows=run.stdout.split('\n')[:len(cases)]
    return [None if row=='none' else (int(row.split()[0]),bytes.fromhex(row.split()[1])) for row in rows]

def sample(rng,size):
    """`size` bytes of valid UTF-8 mixing one- to four-byte characters."""
    out=b''
    while len(out)<size:
        piece=rng.choice(['a','Z','7',' ','é','ß','世','界','☕','😀']).encode()
        if len(out)+len(piece)<=size:out+=piece
    return out

# ---- the session and the reference sender -------------------------------
def fixture(rng):
    """A fresh session with the libsignal recipient of seed SEED, by the establishment references."""
    fx=est.oracle([dict(mode='init',seed=SEED)])[0];raw=lambda k:bytes.fromhex(fx[k])
    identity,spk,otp,kyber=raw('bob_identity')[1:],raw('signed_prekey')[1:],raw('one_time_prekey')[1:],raw('kyber_prekey')[1:]
    alice=raw('alice_private');base,ratchet,ephemeral=(rng.randbytes(32) for _ in range(3))
    ciphertext,kem_secret=est.kyber_encapsulate(kyber,rng.randbytes(32))
    c=dict(one_time=True,dh1=x25519(alice,spk),dh2=x25519(base,identity),dh3=x25519(base,spk),dh4=x25519(base,otp),dh5=x25519(ratchet,spk),
        kem_secret=kem_secret,ciphertext=ciphertext,base_public=public(base),ratchet_public=public(ratchet),sender=public(alice),identity=identity,signed_prekey=spk,
        certificate=rng.randbytes(CERT),uuid=bytes.fromhex('b2000000000040008000000000000002'),access=rng.randbytes(16),request=rng.randbytes(8),device=fx['device_id'],
        registration=fx['registration_id'],local_registration=rng.randrange(1,16381),one_time_id=fx['one_time_id'],signed_id=fx['signed_id'],kyber_id=fx['kyber_id'],
        identity_private=alice,ephemeral=ephemeral)
    conversation,pending,_=est.expected_session(c)
    if len(conversation)!=CERT+262+57:raise AssertionError('record size')
    return c,conversation,pending
def reference_seal(c,conversation,plain):
    """next record, SignalMessage, sealed-sender envelope for an established session's MESSAGE."""
    session=conversation[CERT:CERT+262];metadata=conversation[CERT+262:]
    counter,previous=int.from_bytes(session[1:5],'big'),int.from_bytes(session[5:9],'big')
    ratchet,chain,pq_chain=session[9:41],session[41:73],session[73:105];pq_counter=int.from_bytes(session[105:109],'big');epoch=int.from_bytes(session[109:117],'big')
    sender,receiver=session[118:150],session[150:182]
    pq=hkdf(bytes(32),pq_chain,(pq_counter+1).to_bytes(4,'big')+b'Signal PQ Ratchet V1 Chain Next',64)
    keys=hkdf(pq[32:],mac(chain,b'\x01'),b'WhisperMessageKeys',80)
    pq_message=b'\x01'+varint(epoch)+varint(pq_counter+1)+b'\x00'
    content=b'\x44'+field(10,b'\x05'+ratchet)+b'\x10'+varint(counter)+b'\x18'+varint(previous)+field(34,aes_cbc(keys[:32],keys[64:80],plain))+field(42,pq_message)
    signal=content+mac(keys[32:64],b'\x05'+sender+b'\x05'+receiver+content)[:8]
    ephemeral=public(c['ephemeral'])
    first=hkdf(b'UnidentifiedDelivery'+b'\x05'+receiver+b'\x05'+ephemeral,x25519(c['ephemeral'],receiver),b'',96)
    static=aes_ctr(first[32:64],b'\x05'+sender);static+=mac(first[64:],static)[:10]
    second=hkdf(first[:32]+static,x25519(c['identity_private'],receiver),b'',96)
    message=aes_ctr(second[32:64],b'\x08\x02'+field(18,c['certificate'])+field(26,signal));message+=mac(second[64:],message)[:10]
    envelope=b'\x11'+field(10,b'\x05'+ephemeral)+field(18,static)+field(26,message)
    session=session[:1]+(counter+1).to_bytes(4,'big')+session[5:41]+mac(chain,b'\x02')+pq[:32]+(pq_counter+1).to_bytes(4,'big')+session[109:117]+b'\x00'+session[118:182]+plain[:80]
    return c['certificate']+session+metadata,signal,envelope
def unseal(c,conversation,envelope):
    """The SignalMessage inside an envelope, opened field by field with both MACs verified."""
    receiver=conversation[CERT+150:CERT+182]
    if envelope[:1]!=b'\x11':raise ValueError('envelope version')
    outer=parse(envelope[1:])
    if set(outer)!={10,18,26} or outer[10][:1]!=b'\x05':raise ValueError('envelope fields')
    first=hkdf(b'UnidentifiedDelivery'+b'\x05'+receiver+outer[10],x25519(c['ephemeral'],receiver),b'',96)
    static,tag=outer[18][:-10],outer[18][-10:]
    if mac(first[64:],static)[:10]!=tag or aes_ctr(first[32:64],static)!=b'\x05'+c['sender']:raise ValueError('sender key')
    second=hkdf(first[:32]+outer[18],x25519(c['identity_private'],receiver),b'',96)
    body,tag=outer[26][:-10],outer[26][-10:]
    if mac(second[64:],body)[:10]!=tag:raise ValueError('message MAC')
    inner=parse(aes_ctr(second[32:64],body))
    if set(inner)!={8,18,26} or inner[8]!=2 or inner[18]!=c['certificate']:raise ValueError('sealed content')
    return inner[26]
def wrapped(c,pending,signal):
    """The session is unacknowledged, so the recipient gets the SignalMessage in the session's PreKeySignalMessage."""
    ids=[int.from_bytes(pending[4*i:4*i+4],'big') for i in range(4)]
    return b'\x44'+b'\x08'+varint5(ids[1])+field(18,b'\x05'+pending[16:48])+field(26,b'\x05'+c['sender'])+field(34,signal)+b'\x28'+varint5(ids[0])+b'\x30'+varint5(ids[2])+b'\x38'+varint5(ids[3])+field(66,b'\x08'+pending[48:])
def judged(wires,plains):
    """The libsignal recipient decrypts each wire, in order, to exactly the given plaintext."""
    replies=est.oracle([dict(mode='init',seed=SEED)]+[dict(mode='check',wire=w.hex()) for w in wires])[1:]
    for index,(reply,plain) in enumerate(zip(replies,plains)):
        if not reply.get('accepted') or reply['plaintext']!=plain.hex() or not reply['sender_identity_matches']:
            raise AssertionError('libsignal recipient rejected message %d: %s'%(index,{k:v for k,v in reply.items() if k!='session_record'}))
    if len(replies)!=len(wires):raise AssertionError('oracle replies')
    return len(replies)

# ---- the checks -----------------------------------------------------------
TEXTS={1:(1,48,68),2:(69,146),3:(147,200,226),4:(227,256)}   # text bytes per class: its bounds (six-byte timestamps), and 48, 200
def save(key,value):
    report=json.loads(REPORT.read_text()) if REPORT.exists() else {}
    report[key]=value;REPORT.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n');print(json.dumps({key:value}))

def check_texts():
    rng=random.Random(20261111);now=1900000000000;cases=[]
    for size in (1,2,47,48,49,67,68,69,100,117,118,127,128,145,146,147,200,225,226,227,255,256):
        cases.append((sample(rng,size),now+size))
    cases+=[(sample(rng,size),stamp) for size in (48,60,68,140,226,250) for stamp in (1,127,128,2**35,2**62,2**64-1)]
    got=lean_built(cases);classes={}
    for (text,stamp),result in zip(cases,got):
        if result!=built(text,stamp):raise AssertionError('built message for %d bytes at %d'%(len(text),stamp))
        if client_reads(result[1][2:-8])!=(text,stamp):raise AssertionError('reading back')
        if stamp>2**40 and stamp<2**42:classes.setdefault(result[0],[]).append(len(text))
    bounds={k:[min(v),max(v)] for k,v in sorted(classes.items())}
    if bounds!={1:[1,68],2:[69,146],3:[147,226],4:[227,256]}:raise AssertionError('class bounds %s'%bounds)
    rejected=[(b'\xff\xfe',now),(b'abc\x80',now),(b'\xe4\xb8',now),(b'\xed\xa0\x80',now),(sample(rng,257),now),(sample(rng,300),now)]
    if any(r is not None for r in lean_built(rejected)):raise AssertionError('accepted an invalid or oversized text')
    save('texts',dict(built_messages_equal_reference=len(cases),text_bytes_per_class_with_current_timestamps=bounds,rejected_invalid_utf8_or_over_256_bytes=len(rejected)))

def messages(rng,classes):
    out=[]
    for index,size in enumerate(TEXTS[classes]):
        text=sample(rng,size);stamp=1900000000000+1000*classes+index
        if padded(text,stamp)[0]!=classes:raise AssertionError('class of %d bytes'%size)
        out.append((text,stamp))
    return out

def check_reference():
    """No kernel: the reference sender's own messages, for every class, through the recipient."""
    rng=random.Random(20261111);c,record,pending=fixture(rng);wires=[];plains=[];sizes={}
    for classes in (1,2,3,4):
        for text,stamp in messages(rng,classes):
            plain=padded(text,stamp)[1];record,signal,envelope=reference_seal(c,record,plain)
            if unseal(c,record,envelope)!=signal:raise AssertionError('unseal')
            wires.append(wrapped(c,pending,signal));plains.append(plain);sizes.setdefault(classes,set()).add(len(envelope))
    count=judged(wires,plains)
    if any(len(v)!=1 for v in sizes.values()):raise AssertionError('reference envelope sizes')
    save('reference',dict(reference_messages_decrypted_by_libsignal_recipient=count,envelope_bytes_per_class={k:min(v) for k,v in sizes.items()}))

def check_class(classes):
    rng=random.Random(20261111+classes);c,record,pending=fixture(rng)
    seal,ands,layout=kernel('signal-seal-built',CERT,classes,1,1,1,1)
    if layout['text']!=8*(10+80*classes) or layout['conversation']!=8*(CERT+262+57):raise AssertionError('kernel layout')
    cases=messages(rng,classes);texts=lean_built(cases)
    def send(record,text):
        return seal(conversation=record,text=text,ephemeralPublic=word(public(c['ephemeral'])),senderPublic=word(c['sender']),
            ephemeralAgreement=word(x25519(c['ephemeral'],c['identity'])),staticAgreement=word(x25519(c['identity_private'],c['identity'])))
    wires=[];plains=[];sizes=set()
    for index,((text,stamp),lean) in enumerate(zip(cases,texts)):
        if lean!=built(text,stamp) or lean[0]!=classes:raise AssertionError('built message %d'%index)
        plain=lean[1][2:-8];got=send(record,lean[1]);before=record;record,signal,envelope=reference_seal(c,record,plain)
        if got['status']!=b'\xff' or got['timestamp']!=stamp.to_bytes(8,'big'):raise AssertionError('status of message %d'%index)
        if got['conversation']!=record:raise AssertionError('next record of message %d'%index)
        if got['envelope']!=envelope:raise AssertionError('envelope of message %d'%index)
        inner=unseal(c,before,got['envelope'])
        if inner!=signal:raise AssertionError('SignalMessage of message %d'%index)
        wires.append(wrapped(c,pending,inner));plains.append(plain);sizes.add(len(got['envelope']))
        if index==0:
            # The same message marked invalid, and a zero record: nothing opened, record unchanged.
            bad=send(before,b'\x00'+lean[1][1:])
            if bad['status']!=b'\x00' or any(bad['envelope']) or bad['conversation']!=before[:CERT+117]+b'\x00'+before[CERT+118:CERT+182]+plain[:80]+before[CERT+262:]:
                raise AssertionError('invalid message')
            dead=send(bytes(len(before)),lean[1])
            if dead['status']!=b'\x00' or any(dead['envelope']):raise AssertionError('zero record')
    count=judged(wires,plains)
    for (text,stamp),plain in zip(cases,plains):
        if client_reads(plain)!=(text,stamp) or len(plain)!=80*classes:raise AssertionError('reading back')
    if len(sizes)!=1:raise AssertionError('envelope size varies inside a class: %s'%sorted(sizes))
    save('class %d'%classes,dict(kernel='signal-seal-built %d %d 1 1 1 1'%(CERT,classes),and_gates=ands,padded_content_bytes=80*classes,
        text_bytes_sent=[len(t) for t,_ in cases],envelope_bytes=min(sizes),envelopes_and_records_equal_reference=len(cases),
        messages_decrypted_by_libsignal_recipient=count,text_and_timestamp_read_back=len(cases),invalid_or_zero_record_open_nothing=2))

if __name__=='__main__':
    mode=sys.argv[1] if len(sys.argv)==2 else ''
    if mode=='texts':check_texts()
    elif mode=='reference':check_reference()
    elif mode in ('1','2','3','4'):check_class(int(mode))
    else:sys.exit(__doc__)
