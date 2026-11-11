#!/usr/bin/env python3
"""Check the bundle kernels (TlsMpc/BundleKernels.lean) for contacts with several devices.

This script is a CHECK only. It lowers each kernel, evaluates the flat gate list, and compares
against references written here independently of the Lean: the prekey-bundle response is built
with `json` and `base64` in the shape Signal-Server's `entities/PreKeyResponse.java` serializes
(field order of the Java classes, no whitespace, unpadded base64 for signatures), parsed back
with `json.loads`, and the two request kernels are compared with AES-GCM from the
`cryptography` library applied to the real WebSocket frame.

    check_bundle_kernels.py [--emitter PATH]

Without `--emitter` the kernels come from `circuit_cache.py kernel ...`, which needs
`BundleKernel.find` registered in EmitFlatKernel.lean. With `--emitter` they come from an
executable with the same command line as `flat_kernel_emitter` (and, if it has one, a
`layout MASK_FILE` command that runs the Lean `BundleResponse.layout?` on the opened flags).

Not covered here: `bundle-seal` (3.5 million AND gates, the same body as `establish-seal`, which
check_establish_kernels.py judges with a libsignal recipient) and anything on a network.
Run it under scripts/guarded.py.
"""
import base64,json,random,shutil,subprocess,sys,tempfile
from pathlib import Path
from cryptography.hazmat.primitives.ciphers import Cipher,algorithms,modes
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
EMITTER=sys.argv[sys.argv.index('--emitter')+1] if '--emitter' in sys.argv else None
SCRATCH=Path(tempfile.mkdtemp(prefix='bundle-kernels-',dir=ROOT/'.deps'))

# ---- circuit evaluation -------------------------------------------------
def kernel(*args):
    args=list(map(str,args))
    if EMITTER:
        stem=SCRATCH/'-'.join(args);flat,layout=Path(str(stem)+'.flat'),Path(str(stem)+'.layout')
        subprocess.run([EMITTER,str(flat),str(layout),'kernel',*args],check=True,capture_output=True)
    else:
        out=subprocess.run([sys.executable,str(HERE/'circuit_cache.py'),'kernel',*args],check=True,capture_output=True).stdout.decode().split()
        flat,layout=Path(out[0]),Path(out[4])
    lines=flat.read_text().split('\n');n,count,_=map(int,lines[1].split())
    if lines[0]!='EMP_HYBRID_BOOL_V1':raise ValueError('flat header')
    gates=[(row[0],*map(int,row.split()[1:])) for row in lines[2:2+count]];outputs=list(map(int,lines[2+count].split()[1:]))
    fields={};offset={'I':0,'O':0};opened=set()
    for row in layout.read_text().split('\n')[1:]:
        f=row.split()
        if len(f)>=3:
            fields[(f[0],f[1])]=(offset[f[0]],int(f[2]));offset[f[0]]+=int(f[2])
            if f[0]=='O' and f[3]!='0':opened.add(f[1])
    names={name for kind,name in fields if kind=='I'}
    def run(**values):
        if set(values)!=names:raise ValueError('inputs %s'%sorted(names^set(values)))
        wires=[0]*n
        for name,data in values.items():
            start,bits=fields[('I',name)]
            if bits!=8*len(data):raise ValueError('input size '+name)
            data=int.from_bytes(data,'little')
            for i in range(bits):wires[start+i]=(data>>i)&1
        for g in gates:
            if g[0]=='N':wires.append(1-wires[g[1]])
            elif g[0]=='X':wires.append(wires[g[1]]^wires[g[2]])
            else:wires.append(wires[g[1]]&wires[g[2]])
        bits=[wires[o] for o in outputs]
        return {name:sum(bits[start+i]<<i for i in range(size)).to_bytes(size//8,'little') for (kind,name),(start,size) in fields.items() if kind=='O'}
    return run,sum(g[0]=='A' for g in gates),opened

# ---- the response, as the server writes it -------------------------------
def b64(data,padding=True):
    text=base64.b64encode(data).decode();return text if padding else text.rstrip('=')
def make_device(rng,device,registration,signed_id,kyber_id,one_time_id):
    """The values of one device; `one_time_id` None when the device has no one-time prekeys left."""
    return dict(device=device,registration=registration,signed_id=signed_id,signed_key=rng.randbytes(32),signed_signature=rng.randbytes(64),
        one_time_id=one_time_id,one_time_key=rng.randbytes(32),kyber_id=kyber_id,kyber_key=rng.randbytes(1568),kyber_signature=rng.randbytes(64))
def item(d):
    """PreKeyResponseItem: deviceId, registrationId, signedPreKey, preKey, pqPreKey (ECSignedPreKey, ECPreKey, KEMSignedPreKey)."""
    return {'deviceId':d['device'],'registrationId':d['registration'],
        'signedPreKey':{'keyId':d['signed_id'],'publicKey':b64(b'\x05'+d['signed_key']),'signature':b64(d['signed_signature'],False)},
        'preKey':None if d['one_time_id'] is None else {'keyId':d['one_time_id'],'publicKey':b64(b'\x05'+d['one_time_key'])},
        'pqPreKey':{'keyId':d['kyber_id'],'publicKey':b64(b'\x08'+d['kyber_key']),'signature':b64(d['kyber_signature'],False)}}
def response(identity,devices):
    """PreKeyResponse: identityKey, devices."""
    return json.dumps({'identityKey':b64(b'\x05'+identity),'devices':[item(d) for d in devices]},separators=(',',':')).encode()

# ---- references ----------------------------------------------------------
PUNCTUATION=b'",:[]{}'
def flags(body):return bytes(255 if c in PUNCTUATION else 0 for c in body)
def unb64(text):return base64.b64decode(text+'='*(-len(text)%4),validate=True)
def expected_device(body,index):
    """What bundle-device must output for device `index`, from a JSON parse of the body."""
    whole=json.loads(body);d=whole['devices'][index];key=lambda text,kind:(lambda raw:raw[1:] if raw[0]==kind else None)(unb64(text))
    out=dict(valid=b'\xff',identityKey=key(whole['identityKey'],5),deviceId=bytes([d['deviceId']]),registrationId=d['registrationId'].to_bytes(4,'big'),
        signedPrekeyId=d['signedPreKey']['keyId'].to_bytes(4,'big'),signedPrekey=key(d['signedPreKey']['publicKey'],5),signedPrekeySignature=unb64(d['signedPreKey']['signature']),
        kyberPrekeyId=d['pqPreKey']['keyId'].to_bytes(4,'big'),kyberPrekey=key(d['pqPreKey']['publicKey'],8),kyberPrekeySignature=unb64(d['pqPreKey']['signature']))
    if d['preKey'] is not None:out.update(oneTimePrekeyId=d['preKey']['keyId'].to_bytes(4,'big'),oneTimePrekey=key(d['preKey']['publicKey'],5))
    return out
def reference_layout(body):
    """The `bundle-device` parameter lists, from the text itself (independent of the opened flags)."""
    whole=json.loads(body);rows=[];start=body.index(b'[')+1
    for d in whole['devices']:
        text=json.dumps(d,separators=(',',':')).encode()
        if body[start:start+len(text)]!=text:raise AssertionError('reference layout')
        width=lambda n:len(str(n))
        rows.append(['bundle-device',len(body),start,width(d['deviceId']),width(d['registrationId']),width(d['signedPreKey']['keyId']),
            0 if d['preKey'] is None else width(d['preKey']['keyId']),width(d['pqPreKey']['keyId'])]);start+=len(text)+1
    return rows
def lean_layout(mask):
    """BundleResponse.layout? (Lean) on the opened flags, when the emitter offers it."""
    path=SCRATCH/'mask.txt';path.write_text(''.join('1' if b else '0' for b in mask))
    out=subprocess.run([EMITTER,'layout',str(path)],check=True,capture_output=True).stdout.decode().strip().split('\n')
    return None if out==['none'] else [[row.split()[0],*map(int,row.split()[1:])] for row in out]

def varint(n):
    out=b''
    while n>=128:out+=bytes([n%128+128]);n//=128
    return out+bytes([n])
def field(tag,data):return bytes([tag])+varint(len(data))+data
def websocket_request(verb,path,headers,body,request_id):
    """WebSocketMessage{type: REQUEST, request{verb, path, body, headers, id}} as the client writes it."""
    request=field(0x0a,verb)+field(0x12,path)+(field(0x1a,body) if body is not None else b'')+b'\x20'+varint(request_id)+b''.join(field(0x2a,h) for h in headers)
    return b'\x08\x01'+field(0x12,request)
def frame(payload,mask):
    """A masked binary WebSocket frame; returns it and where the payload starts."""
    if len(payload)<126:head=bytes([0x82,0x80|len(payload)])
    else:head=bytes([0x82,0xfe])+len(payload).to_bytes(2,'big')
    return head+mask+bytes(b^mask[i%4] for i,b in enumerate(payload)),len(head)+4
def tls_parts(block,sequence,plaintext):
    """header, ciphertext without tag, and the tag pad AES_K(J0), for one TLS 1.3 application record."""
    key,iv=block[32:48],block[48:60];nonce=bytes(a^b for a,b in zip(iv,bytes(4)+sequence));inner=plaintext+b'\x17'
    header=b'\x17\x03\x03'+(len(inner)+16).to_bytes(2,'big');sealed=AESGCM(key).encrypt(nonce,inner,header)
    e=Cipher(algorithms.AES(key),modes.ECB()).encryptor();return header,sealed[:-16],e.update(nonce+b'\x00\x00\x00\x01')
def uuid_text(raw):h=raw.hex();return '-'.join((h[:8],h[8:12],h[12:16],h[16:20],h[20:])).encode()
def record(rng,identity,uuid,access,device,registration,version=4):
    """A 319-byte contact record: session block (262) and metadata (57)."""
    session=bytes([version])+rng.randbytes(149)+identity+rng.randbytes(80)
    return session+uuid+access+bytes(8)+rng.randbytes(8)+bytes([device])+registration.to_bytes(4,'big')+bytes(4)
def blanked(real,at,payload,secrets):
    """The frame the controllers build: `real` with zero bytes where each secret is (given as
    (unique context, length of the secret at its end)); and the secrets' offsets in the frame."""
    offsets=[]
    for context,size in secrets:
        if payload.count(context)!=1:raise AssertionError('slot is ambiguous')
        start=at+payload.index(context)+len(context)-size;real=real[:start]+bytes(size)+real[start+size:];offsets.append(start)
    return real,offsets

def main():
    rng=random.Random(20261111);report={'kernels':{},'cases':{}}
    def load(*args,opens=()):
        run,ands,opened=kernel(*args);report['kernels'][' '.join(map(str,args))]=dict(and_gates=ands)
        if opened!=set(opens):raise AssertionError('%s opens %s'%(args[0],sorted(opened)))
        return run
    identity=rng.randbytes(32)
    one=[make_device(rng,1,16383,16777215,2147483647,8388607)]
    three=[make_device(rng,1,7,5,1,None),make_device(rng,12,902,123456,4096,77),make_device(rng,127,12345,2147483647,99999999,None)]
    for label,devices in (('one device with a one-time prekey',one),('three devices, mixed',three)):
        body=response(identity,devices);size=len(body)
        # 1. the opened shape is exactly the punctuation flags
        shape=load('bundle-shape',size,opens=['shape'])(body=body)['shape']
        if shape!=flags(body):raise AssertionError('bundle-shape')
        # 2. the layout the controllers derive from the flags
        rows=reference_layout(body)
        if EMITTER:
            if lean_layout(shape)!=rows:raise AssertionError('layout? disagrees with the reference')
            for at in (0,size//2,size-1):   # one wrong flag anywhere: no layout
                if lean_layout(shape[:at]+bytes([255-shape[at]])+shape[at+1:]) is not None:raise AssertionError('layout? accepted altered flags')
        # 3. every device's fields, all private
        runs=[]
        for index,row in enumerate(rows):
            run=load(*row);runs.append(run);got=run(body=body);want=expected_device(body,index)
            if got!=want:raise AssertionError('bundle-device %d: %s'%(index,[k for k in want if got.get(k)!=want[k]]))
        # 4. a body that is not the template releases nothing
        def rejected(index,altered,why):
            got=runs[index](body=altered)
            if any(any(v) for v in got.values()):raise AssertionError('accepted or released: '+why)
        text=body.decode();d0=devices[0];count=0
        def swap(old,new,index=0,occurrence=0):
            nonlocal count
            parts=text.split(old)
            if len(parts)<2+occurrence or len(old)!=len(new):raise AssertionError('tamper '+old)
            rejected(index,(old.join(parts[:occurrence+1])+new+old.join(parts[occurrence+1:])).encode(),'%s -> %s'%(old,new));count+=1
        swap('"identityKey"','"identitykey"');swap('"deviceId"','"deviceID"');swap('"signature"','"signaturE"');swap('"pqPreKey"','"pqPrekey"')
        swap('"registrationId":%d'%d0['registration'],'"registrationId":%s'%('0'*len(str(d0['registration']))) if len(str(d0['registration']))>1 else '"registrationId":a')   # leading zeros, or not a digit
        swap(b64(b'\x05'+d0['signed_key']),b64(b'\x06'+d0['signed_key']))                       # wrong key type
        swap(b64(b'\x08'+d0['kyber_key']),b64(b'\x05'+d0['kyber_key']))
        swap(b64(b'\x05'+identity),b64(b'\x05'+identity)[:-1]+'*')                              # not base64
        swap(b64(b'\x05'+identity),b64(b'\x05'+identity)[:-1]+'=')                              # padding where data belongs
        signature=b64(d0['signed_signature'],False);last='ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/'.index(signature[-1])
        swap(signature,signature[:-1]+'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/'[last|1])   # spare bits set
        swap(']}','],',0,text.count(']}')-1)                                                    # the end of the body
        if d0['one_time_id'] is not None:swap('"preKey":{"keyId"','"preKey":{"keyID"')
        # numbers out of range, with the same digit counts (so the same kernel)
        for name,old,new in (('"deviceId":',127,128),('"keyId":',2147483647,4294967296)):
            for index,d in enumerate(devices):
                if '%s%d,'%(name,old) in text:
                    at=text.index('%s%d,'%(name,old))
                    if rows[index][2]<=at and (index+1==len(rows) or at<rows[index+1][2]):
                        rejected(index,text.replace('%s%d,'%(name,old),'%s%d,'%(name,new),1).encode(),'%s%d'%(name,new));count+=1
        # the kernel for another layout (a wrong width, or a wrong start) on the genuine body
        for index,row in enumerate(rows):
            for column in (2,5,7):
                other=list(row);other[column]+=1
                try:run,_,_=kernel(*other)
                except subprocess.CalledProcessError:continue      # Lean refuses the parameters
                if any(any(v) for v in run(body=body).values()):raise AssertionError('wrong layout accepted');
                count+=1
        # a tampered item fails that device only
        if len(devices)>1:
            broken=text.replace('"registrationId":902','"registrationId":9x2').encode()
            if runs[0](body=broken)!=expected_device(body,0) or any(any(v) for v in runs[1](body=broken).values()):raise AssertionError('item isolation')
        report['cases'][label]=dict(body_bytes=size,devices=len(devices),fields_match_reference=True,rejected_bodies_release_nothing=count,
            layout_from_lean=bool(EMITTER))
    # 5. binding to the contact
    uuid,access=rng.randbytes(16),rng.randbytes(16);known=record(rng,identity,uuid,access,1,16383)
    bind=load('bundle-bind')
    got=bind(record=known,valid=b'\xff',verified=b'\xff',identityKey=identity)
    if got!=dict(verified=b'\xff',uuid=uuid,accessKey=access):raise AssertionError('bundle-bind')
    other=bytes([identity[0]^1])+identity[1:];dead=record(rng,identity,uuid,access,1,16383,version=0)
    for values in (dict(valid=b'\x00'),dict(verified=b'\x00'),dict(valid=b'\x01'),dict(identityKey=other),dict(record=dead),dict(record=bytes(319),identityKey=bytes(32))):
        if any(any(v) for v in bind(**{**dict(record=known,valid=b'\xff',verified=b'\xff',identityKey=identity),**values}).values()):raise AssertionError('bundle-bind released: %s'%sorted(values))
    report['cases']['bind']=dict(matches_reference=True,rejected_release_nothing=6)
    # 5b. the binding that accepts a changed identity key (what the sessions use): the same check
    # without the comparison of identity keys, and the one opened byte `changed`
    rebind=load('bundle-rebind',opens=['changed'])
    accepted=dict(record=known,valid=b'\xff',verified=b'\xff',identityKey=identity)
    if rebind(**accepted)!=dict(verified=b'\xff',uuid=uuid,accessKey=access,changed=b'\x00'):raise AssertionError('bundle-rebind')
    if rebind(**{**accepted,'identityKey':other})!=dict(verified=b'\xff',uuid=uuid,accessKey=access,changed=b'\xff'):raise AssertionError('bundle-rebind: changed identity key')
    for values in (dict(valid=b'\x00'),dict(verified=b'\x00'),dict(valid=b'\x01'),dict(record=dead),dict(valid=b'\x00',identityKey=other),dict(verified=b'\x00',identityKey=other)):
        if any(any(v) for v in rebind(**{**accepted,**values}).values()):raise AssertionError('bundle-rebind released: %s'%sorted(values))
    report['cases']['rebind']=dict(matches_reference=True,changed_identity_key_accepted_and_flagged=True,rejected_release_nothing=6)
    # 6. the prekey fetch: the kernel's record is the TLS encryption of the real request frame
    block,sequence,mask=rng.randbytes(60),(41).to_bytes(8,'big'),rng.randbytes(4)
    key_text=b64(access).encode()
    payload=websocket_request(b'GET',b'/v2/keys/'+uuid_text(uuid)+b'/*',[b'Unidentified-Access-Key:'+key_text,b'Accept:application/json',b'X-Signal-Agent:OWA'],None,7)
    real,at=frame(payload,mask);clear,offsets=blanked(real,at,payload,[(uuid_text(uuid),36),(key_text,24)])
    fetch=load('bundle-fetch-ctr',len(clear),at,*offsets,opens=['accepted','header','ciphertext'])
    got=fetch(clientApplication=block,sequence=sequence,record=known,frame=clear,mask=mask);header,ciphertext,pad=tls_parts(block,sequence,real)
    if got!=dict(accepted=b'\xff',header=header,ciphertext=ciphertext,pad=pad):raise AssertionError('bundle-fetch-ctr')
    got=fetch(clientApplication=block,sequence=sequence,record=dead,frame=clear,mask=mask)
    if got['accepted']!=b'\x00' or any(got['ciphertext']):raise AssertionError('bundle-fetch-ctr sealed for a dead record')
    fetch_bytes=len(clear)
    # 7. a send to two devices
    records=[known,record(rng,identity,uuid,access,12,902)];slots=[]
    for r in records:slots+=[b'"destinationDeviceId":'+str(r[310]).ljust(3).encode(),b'"destinationRegistrationId":'+str(int.from_bytes(r[311:315],'big')).ljust(10).encode()]
    messages=b','.join(b'{"type":6,'+slots[2*i]+b','+slots[2*i+1]+b',"content":"'+b64(rng.randbytes(30)).encode()+b'"}' for i in range(2))
    body=b'{"messages":['+messages+b'],"online":false,"urgent":true,"timestamp":1900000000000}'
    payload=websocket_request(b'PUT',b'/v1/messages/'+uuid_text(uuid),[b'Unidentified-Access-Key:'+key_text,b'content-type:application/json'],body,8)
    real,at=frame(payload,mask)
    clear,offsets=blanked(real,at,payload,[(uuid_text(uuid),36),(key_text,24)]+[(slot,3 if i%2==0 else 10) for i,slot in enumerate(slots)])
    send=load('bundle-request-ctr',len(clear),at,*offsets,opens=['accepted','header','ciphertext'])
    got=send(clientApplication=block,sequence=sequence,records=b''.join(records),frame=clear,mask=mask);header,ciphertext,pad=tls_parts(block,sequence,real)
    if got!=dict(accepted=b'\xff',header=header,ciphertext=ciphertext,pad=pad):raise AssertionError('bundle-request-ctr')
    got=send(clientApplication=block,sequence=sequence,records=known+dead[:262]+records[1][262:],frame=clear,mask=mask)
    if got['accepted']!=b'\x00' or any(got['ciphertext']):raise AssertionError('bundle-request-ctr sealed with a dead record')
    report['cases']['requests']=dict(fetch_frame_bytes=fetch_bytes,send_frame_bytes=len(clear),send_devices=2,
        records_are_tls_encryptions_of_real_frames=True,dead_record_seals_nothing=2)
    shutil.rmtree(SCRATCH)
    (HERE/'bundle-kernels-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
if __name__=='__main__':main()
