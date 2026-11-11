#!/usr/bin/env python3
"""Check the two-step record opening (TlsMpc/TypedOpenKernels.lean) against the existing kernel.

This script is a CHECK only. It builds real TLS 1.3 AES-128-GCM records with the `cryptography`
package (application data, alerts, KeyUpdate, NewSessionTicket, a handshake message split
across two records, padding) and tampered variants of them, lowers the kernels with
circuit_cache.py and evaluates the flat gate lists as the worker would sequence them:

  gcm-check                       -> the private mask `accepted`
  tls-open-application-class CAP  -> the existing result (event, parser, length, content)
  tls-open-typed CAP              -> the bit `handshake`; when 0 its own four fields
  tls-frame CAP (bit 255 only)    -> the four fields

and requires, for every case: the four fields of the new path equal the existing kernel's; the
bit is 255 exactly when the record authenticates and its inner type (decrypted here,
independently) is 22; the event is the one the case expects; and for every tampered record the
bit is 0 and the event is [0, 0]. It also runs both new kernels on forced inputs the worker
cannot produce (accepted = 255 with a wrong header, random parser states) and compares them
with the existing kernel there too.

Usage: check_typed_open.py [--large]   (--large adds 2.7 KB records; slower)
Prints AND gates of each kernel and writes typed-open-report.json. Nothing touches a network.
"""
import json,os,random,subprocess,sys
from pathlib import Path
from cryptography.hazmat.primitives.ciphers import Cipher,algorithms,modes
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
HERE=Path(__file__).resolve().parent
RNG=random.Random(20261111)

KERNELS={}
def kernel(*args):
    """The kernel as a function from named input bytes to named output bytes (as check_receive_kernels.py)."""
    key=' '.join(map(str,args))
    if key in KERNELS:return KERNELS[key][0]
    out=subprocess.run([sys.executable,str(HERE/'circuit_cache.py'),'kernel',*map(str,args)],check=True,capture_output=True).stdout.decode().split()
    with open(out[0]) as f:
        if f.readline().strip()!='EMP_HYBRID_BOOL_V1':raise ValueError('flat header')
        n,count,width=map(int,f.readline().split())
        if n!=int(out[2]) or width!=int(out[3]):raise ValueError('flat shape')
        kinds=bytearray(count);left=[0]*count;right=[0]*count
        for i in range(count):
            row=f.readline().split();kinds[i]=ord(row[0]);left[i]=int(row[1])
            if len(row)>2:right[i]=int(row[2])
        outputs=list(map(int,f.readline().split()[1:]))
    fields={};offset={'I':0,'O':0};opened={}
    for row in Path(out[4]).read_text().split('\n')[1:]:
        f=row.split()
        if len(f)>=3:
            fields[(f[0],f[1])]=(offset[f[0]],int(f[2]));offset[f[0]]+=int(f[2])
            if f[0]=='O':opened[f[1]]=int(f[3])
    names={name for kind,name in fields if kind=='I'}
    def run(**values):
        if set(values)!=names:raise ValueError('%s inputs %s'%(key,sorted(names^set(values))))
        wires=[0]*(n+count)
        for name,data in values.items():
            start,bits=fields[('I',name)]
            if bits!=8*len(data):raise ValueError('%s input size %s: %d bits, got %d bytes'%(key,name,bits,len(data)))
            value=int.from_bytes(data,'little')
            for i in range(bits):wires[start+i]=(value>>i)&1
        at=n
        for i in range(count):
            k=kinds[i]
            if k==78:wires[at]=1-wires[left[i]]
            elif k==88:wires[at]=wires[left[i]]^wires[right[i]]
            else:wires[at]=wires[left[i]]&wires[right[i]]
            at+=1
        bits=[wires[o] for o in outputs];result={}
        for (kind,name),(start,size) in fields.items():
            if kind=='O':result[name]=sum(bits[start+i]<<i for i in range(size)).to_bytes(size//8,'little')
        return result
    KERNELS[key]=(run,sum(1 for k in kinds if k==65),opened);return run

def capacity(n):
    if n<=32:return 32
    step=1
    while 8*step<n:step*=2
    return (n+step-1)//step*step

# ---- TLS 1.3 records, independently of the Lean ----------------------------
def nonce(iv,sequence):return bytes(a^b for a,b in zip(iv,bytes(4)+sequence.to_bytes(8,'big')))
def seal(key,iv,sequence,content,kind,padding=0):
    inner=content+bytes([kind])+bytes(padding);header=b'\x17\x03\x03'+(len(inner)+16).to_bytes(2,'big')
    return header+AESGCM(key).encrypt(nonce(iv,sequence),inner,header)
def ctr(key,iv,sequence,data):
    e=Cipher(algorithms.AES(key),modes.CTR(nonce(iv,sequence)+b'\x00\x00\x00\x02')).encryptor();return e.update(data)+e.finalize()
def block(key,data):
    e=Cipher(algorithms.AES(key),modes.ECB()).encryptor();return e.update(data)+e.finalize()
def xor(a,b):return bytes(x^y for x,y in zip(a,b))

class Connection:
    def __init__(self):
        self.secret=RNG.randbytes(32);self.key=RNG.randbytes(16);self.iv=RNG.randbytes(12)
        self.traffic=self.secret+self.key+self.iv
    def check(self,sequence,wire):
        """`accepted` from the gcm-check kernel. The parties' halves of the tag polynomial are supplied as
        (GHASH of the received header and ciphertext, 0): GHASH = correct tag xor pad."""
        header,ciphertext,tag=wire[:5],wire[5:-16],wire[-16:]
        plain=ctr(self.key,self.iv,sequence,ciphertext)
        correct=AESGCM(self.key).encrypt(nonce(self.iv,sequence),plain,header)
        if correct[:-16]!=ciphertext:raise ValueError('reference CTR')
        pad=block(self.key,nonce(self.iv,sequence)+b'\x00\x00\x00\x01')
        out=kernel('gcm-check')(traffic=self.traffic,sequence=sequence.to_bytes(8,'big'),halfA=xor(correct[-16:],pad),halfB=bytes(16),tag=tag)
        accepted=out['accepted']
        if accepted!=(b'\xff' if correct[-16:]==tag else b'\x00'):raise ValueError('gcm-check disagrees with the reference')
        return accepted,plain

FAILURES=[];CASES=[]
def require(condition,label,what):
    if not condition:FAILURES.append('%s: %s'%(label,what))

def open_both(connection,parser,sequence,wire,accepted=None,label=''):
    """Run the existing kernel and the new pair on the same inputs; compare; return (existing fields, bit)."""
    if accepted is None:accepted,_=connection.check(sequence,wire)
    cap=capacity(len(wire));padded=wire+bytes(cap-len(wire))
    inputs=dict(parser=parser,serverApplication=connection.traffic,sequence=sequence.to_bytes(8,'big'),record=padded,size=wire[3:5],accepted=accepted)
    old=kernel('tls-open-application-class',cap)(**inputs)
    first=kernel('tls-open-typed',cap)(**inputs);bit=first['handshake']
    require(bit in (b'\x00',b'\xff'),label,'bit %r'%bit)
    if bit==b'\xff':
        new=kernel('tls-frame',cap)(parser=parser,parsed=first['parsed'])
        require(first['event']==b'\x00\x00',label,'first kernel event not zero with the bit set')
    else:new=first
    for name in ('event','parser','length','content'):
        require(new[name]==old[name],label,'field %s differs from the existing kernel'%name)
    return old,bit

def case(label,connection,parser,sequence,wire,event,tampered=False,kind=None,request=0):
    accepted,plain=connection.check(sequence,wire)
    old,bit=open_both(connection,parser,sequence,wire,accepted,label)
    stripped=plain.rstrip(b'\x00');inner=stripped[-1] if stripped else 0
    expected_bit=b'\xff' if accepted==b'\xff' and inner==22 and len(stripped)>1 else b'\x00'
    require(bit==expected_bit,label,'bit %r, expected %r'%(bit,expected_bit))
    require(old['event']==bytes([event,request]),label,'event %r, expected %d %d'%(old['event'],event,request))
    if kind is not None and accepted==b'\xff':require(inner==kind,label,'inner type')
    if tampered:
        require(accepted==b'\x00',label,'tampered record accepted')
        require(bit==b'\x00',label,'bit opened as 1 for a tampered record')
        require(old['event']==b'\x00\x00',label,'event for a tampered record')
    if event==1:
        length=int.from_bytes(old['length'],'big')
        require(old['content'][:length]==stripped[:-1] and not any(old['content'][length:]),label,'content')
    CASES.append(dict(case=label,size=len(wire),capacity=capacity(len(wire)),accepted=accepted[0],bit=bit[0],event=list(old['event'])))
    return old['parser']

def tamper_cases(label,connection,parser,sequence,wire):
    flipped=bytearray(wire);flipped[5+RNG.randrange(len(wire)-21)]^=1<<RNG.randrange(8)
    case(label+' / ciphertext bit flipped',connection,parser,sequence,bytes(flipped),0,tampered=True)
    retyped=bytearray(wire);retyped[len(wire)-17]^=23^22   # the unpadded type byte: application data <-> handshake
    case(label+' / type byte flipped to the other type',connection,parser,sequence,bytes(retyped),0,tampered=True)
    tag=bytearray(wire);tag[len(wire)-1-RNG.randrange(16)]^=1<<RNG.randrange(8)
    case(label+' / tag bit flipped',connection,parser,sequence,bytes(tag),0,tampered=True)
    if len(wire)>=22+8:
        cut=wire[:5]+wire[5:-16-7]+wire[-16:];cut=cut[:3]+(len(cut)-5).to_bytes(2,'big')+cut[5:]
        case(label+' / truncated',connection,parser,sequence,cut,0,tampered=True)
    case(label+' / wrong sequence number',connection,parser,sequence+1,wire,0,tampered=True)

def main():
    large='--large' in sys.argv
    start=kernel('tls-parser-initial')(unused=b'\x00')['parser']
    c=Connection();sequence=0
    # Application data of several sizes, with and without record padding.
    sizes=[0,1,10,100,129,300]+([2680] if large else [])
    for size in sizes:
        for padding in ([0,7] if size<2000 else [0]):
            wire=seal(c.key,c.iv,sequence,RNG.randbytes(size),23,padding);label='application data %d bytes, padding %d'%(size,padding)
            after=case(label,c,start,sequence,wire,1,kind=23)
            require(after==start,label,'parser state changed by application data')
            if size in (10,129,2680) and padding==0:tamper_cases(label,c,start,sequence,wire)
            sequence+=1
    # Alerts: close_notify (close), user_canceled (ignored), another description, a malformed one.
    for description,event in ((0,4),(90,2),(40,0),(10,0)):
        for level in (1,2):
            wire=seal(c.key,c.iv,sequence,bytes([level,description]),21);label='alert level %d description %d'%(level,description)
            case(label,c,start,sequence,wire,event,kind=21)
            if description in (0,90) and level==1:tamper_cases(label,c,start,sequence,wire)
            sequence+=1
    case('alert of three bytes',c,start,sequence,seal(c.key,c.iv,sequence,b'\x01\x00\x00',21),0,kind=21);sequence+=1
    case('empty alert',c,start,sequence,seal(c.key,c.iv,sequence,b'',21),0);sequence+=1
    case('unknown inner type 24',c,start,sequence,seal(c.key,c.iv,sequence,b'abc',24),0);sequence+=1
    case('all-zero inner plaintext',c,start,sequence,seal(c.key,c.iv,sequence,bytes(9),0),0);sequence+=1
    # KeyUpdate (requested and not), with padding too.
    for request in (0,1):
        for padding in (0,5):
            wire=seal(c.key,c.iv,sequence,bytes([24,0,0,1,request]),22,padding);label='key update request %d, padding %d'%(request,padding)
            case(label,c,start,sequence,wire,3,kind=22,request=request)
            if padding==0:tamper_cases(label,c,start,sequence,wire)
            sequence+=1
    case('key update with a bad body',c,start,sequence,seal(c.key,c.iv,sequence,bytes([24,0,0,1,2]),22),0,kind=22);sequence+=1
    case('key update followed by more',c,start,sequence,seal(c.key,c.iv,sequence,bytes([24,0,0,1,0,4,0,0,0]),22),0,kind=22);sequence+=1
    case('empty handshake record',c,start,sequence,seal(c.key,c.iv,sequence,b'',22),0);sequence+=1
    case('handshake message of another type',c,start,sequence,seal(c.key,c.iv,sequence,bytes([13,0,0,1,0]),22),0,kind=22);sequence+=1
    # NewSessionTicket: whole, two in one record, and split across two records (with other records between refused).
    def ticket(n):return bytes([4])+n.to_bytes(3,'big')+RNG.randbytes(n)
    for size in (40,220)+((2600,) if large else ()):
        wire=seal(c.key,c.iv,sequence,ticket(size),22);label='session ticket %d bytes'%size
        after=case(label,c,start,sequence,wire,2,kind=22)
        require(after[0]==0 and after[10]==0,label,'parser not at a message boundary after a whole ticket')
        if size==220:tamper_cases(label,c,start,sequence,wire)
        sequence+=1
    case('two tickets in one record',c,start,sequence,seal(c.key,c.iv,sequence,ticket(30)+ticket(51),22),2,kind=22);sequence+=1
    case('ticket then key update in one record',c,start,sequence,seal(c.key,c.iv,sequence,ticket(30)+bytes([24,0,0,1,1]),22),3,kind=22,request=1);sequence+=1
    for cut in (2,4,60,150):
        whole=ticket(200);label='ticket split at %d'%cut
        middle=case(label+' / first part',c,start,sequence,seal(c.key,c.iv,sequence,whole[:cut],22),2,kind=22)
        require(middle!=start,label,'parser state after a fragment')
        # In the middle of a message: application data and alerts are refused; the rest of the message completes it.
        case(label+' / application data inside the message',c,middle,sequence+1,seal(c.key,c.iv,sequence+1,b'data',23),0,kind=23)
        case(label+' / close_notify inside the message',c,middle,sequence+1,seal(c.key,c.iv,sequence+1,b'\x01\x00',21),0,kind=21)
        tamper_cases(label+' / second part',c,middle,sequence+1,seal(c.key,c.iv,sequence+1,whole[cut:],22))
        end=case(label+' / second part',c,middle,sequence+1,seal(c.key,c.iv,sequence+1,whole[cut:],22,3),2,kind=22)
        require(end[0]==0 and end[10]==0,label,'parser not at a message boundary after the whole message')
        after=case(label+' / application data after it',c,end,sequence+2,seal(c.key,c.iv,sequence+2,b'more data',23),1,kind=23)
        sequence+=3
    # An error is sticky: after a refused record, genuine records of every type are refused.
    wire=seal(c.key,c.iv,sequence,b'\x02\x28',21);failed=case('fatal alert',c,start,sequence,wire,0,kind=21);sequence+=1
    require(failed!=start,'fatal alert','parser state not marked')
    for content,kind,name in ((b'data',23,'application data'),(bytes([24,0,0,1,0]),22,'key update'),(b'\x01\x00',21,'close_notify')):
        case('after an error: '+name,c,failed,sequence,seal(c.key,c.iv,sequence,content,kind),0,kind=kind);sequence+=1
    # Inputs the worker cannot produce: the kernels must still agree with the existing one.
    forced=0
    for trial in range(12):
        content,kind=RNG.choice(((RNG.randbytes(RNG.randrange(1,90)),23),(bytes([24,0,0,1,trial%2]),22),(ticket(RNG.randrange(1,90)),22),(b'\x01\x00',21)))
        wire=bytearray(seal(c.key,c.iv,sequence,content,kind,RNG.randrange(4)))
        if trial%3==0:wire[0]=22
        if trial%3==1:wire[5+RNG.randrange(len(wire)-21)]^=RNG.randrange(1,256)
        parser=start if trial%2 else RNG.randbytes(11)
        for accepted in (b'\xff',b'\x00',bytes([RNG.randrange(1,255)])):
            old,bit=open_both(c,parser,sequence,bytes(wire),accepted,'forced inputs %d accepted %d'%(trial,accepted[0]));forced+=1
            if accepted==b'\x00':require(bit==b'\x00' and old['event']==b'\x00\x00','forced inputs %d'%trial,'accepted = 0 opened something')
        sequence+=1
    # Layout: what may be opened.
    cap=capacity(160);kernel('tls-open-typed',cap);kernel('tls-frame',cap)
    require(KERNELS['tls-open-typed %d'%cap][2]==dict(handshake=1,event=1,parser=0,length=0,content=0,parsed=0),'layout','tls-open-typed opened fields')
    require(KERNELS['tls-frame %d'%cap][2]==dict(event=1,parser=0,length=0,content=0),'layout','tls-frame opened fields')
    gates={}
    for size in [150]+([2700] if large else []):
        cap=capacity(size);kernel('tls-open-application-class',cap);kernel('tls-open-typed',cap);kernel('tls-frame',cap)
        row={name:KERNELS['%s %d'%(name,cap)][1] for name in ('tls-open-application-class','tls-open-typed','tls-frame')}
        row.update(capacity=cap,existing_per_byte=round(row['tls-open-application-class']/size,1),typed_per_byte=round(row['tls-open-typed']/size,1),
            handshake_record_per_byte=round((row['tls-open-typed']+row['tls-frame'])/size,1));gates[str(size)]=row
    report=dict(passed=not FAILURES,cases=len(CASES),tampered=sum(1 for row in CASES if not row['accepted']),bit_set=sum(1 for row in CASES if row['bit']),
        forced_input_runs=forced,and_gates=gates,failures=FAILURES[:40],rows=CASES)
    (HERE/'typed-open-report.json').write_text(json.dumps(report,indent=1)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='rows'},indent=1))
    sys.exit(0 if report['passed'] else 1)

if __name__=='__main__':main()
