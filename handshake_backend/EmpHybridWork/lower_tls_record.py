"""Export, check and pin the TLS 1.3 record seal and open circuits.

Circuits: `TlsRecord.sealCore` and `TlsReceive.openCore` from the existing Lean
development (AES-128-GCM, application_data), printed by EmitHybridKdf.lean and
lowered by the shared unverified adapter. Reference: AES-GCM from the
`cryptography` library with the RFC 8446 nonce and additional data, independent
of the circuit. Profiles and fixture lanes are written for the MPC runner.
"""
import hashlib,json,pathlib,subprocess,sys
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent;OUT=ROOT/'.deps/emp-hybrid-word-v1';OUT.mkdir(exist_ok=True)
sys.path.insert(0,str(ROOT));sys.path.insert(0,str(HERE))
from hybrid_lowering import lower,flat_text,byte_bits,evaluate_bytes
SIZE,PADDING=64,0
def sample(label,n):
    out=b'';i=0
    while len(out)<n:out+=hashlib.sha256(('hybrid-tls-record:%s:%d'%(label,i)).encode()).digest();i+=1
    return out[:n]
def seal(key,iv,seq,content):
    inner=content+b'\x17'+bytes(PADDING);header=b'\x17\x03\x03'+(len(inner)+16).to_bytes(2,'big')
    nonce=bytes(a^b for a,b in zip(iv,bytes(4)+seq))
    return header+AESGCM(key).encrypt(nonce,inner,header)
key,iv,content=sample('key',16),sample('iv',12),sample('content',SIZE)
subprocess.run(['lake','build','hybrid_kdf_emitter','word_mask_emitter'],cwd=ROOT,check=True,capture_output=True)
report={}
def publish(name,args,lanes):
    raw=subprocess.run(['lake','exe','hybrid_kdf_emitter',*args],cwd=ROOT,check=True,capture_output=True).stdout
    n,gates,outputs=lower(json.loads(raw));fixtures=[]
    for label,data,want in lanes(len(outputs)//8):
        if 8*len(data)!=n or 8*len(want)!=len(outputs):raise ValueError(name+' shape')
        if evaluate_bytes(gates,outputs,byte_bits(data))!=want:raise AssertionError((name,label))
        fixtures.append(dict(label=label,input=data.hex(),output=want.hex()))
    text=flat_text(n,gates,outputs);(OUT/(name+'.flat')).write_text(text);digest=hashlib.sha256(text.encode()).hexdigest()
    equal=subprocess.run(['lake','exe','word_mask_emitter','equal',str(len(outputs))],cwd=ROOT,check=True,capture_output=True).stdout.decode()
    (OUT/(name+'-equal.flat')).write_text(equal)
    (OUT/(name+'.json')).write_text(json.dumps(dict(circuit=name+'.flat',circuit_sha256=digest,equal=name+'-equal.flat',equal_sha256=hashlib.sha256(equal.encode()).hexdigest(),input_bits=n,output_bits=len(outputs),fixtures=fixtures),indent=2)+'\n')
    report[name]=dict(arguments=args,lean_image_sha256=hashlib.sha256(raw).hexdigest(),flat_sha256=digest,and_gates=sum(g[0]=='A' for g in gates),input_bits=n,output_bits=len(outputs),lanes=[f['label'] for f in fixtures])
def seal_lanes(out_bytes):
    for label,seq in (('sequence-0',bytes(8)),('sequence-large',(2**40+7).to_bytes(8,'big'))):
        yield label,key+iv+seq+content,seal(key,iv,seq,content)
publish('tls-seal-record',['tls-seal-record',str(SIZE),str(PADDING)],seal_lanes)
WIRE=5+SIZE+1+PADDING+16
def open_lanes(out_bytes):
    seq=(3).to_bytes(8,'big');record=seal(key,iv,seq,content);buffer=out_bytes-4
    yield 'valid-record',key+iv+seq+record,bytes([255,23])+len(content).to_bytes(2,'big')+content+bytes(buffer-len(content))
    forged=bytearray(record);forged[-1]^=1
    yield 'forged-tag-zeroes-output',key+iv+seq+bytes(forged),bytes(out_bytes)
    yield 'wrong-sequence-zeroes-output',key+iv+(4).to_bytes(8,'big')+record,bytes(out_bytes)
publish('tls-open-record',['tls-open-record',str(WIRE)],open_lanes)
out=dict(passed=True,circuits=report,reference='cryptography AESGCM, RFC 8446 section 5.2/5.3 nonce and additional data',scope='TLS 1.3 application-data record seal and open as Lean circuits, checked against an independent AES-GCM on valid, forged-tag and wrong-sequence lanes. Lowered by the shared unverified adapter. Connection state policy (sequence reservation, key update) is outside these circuits.')
(HERE/'tls-record-circuit-report.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:dict(and_gates=v['and_gates'],input_bits=v['input_bits'],output_bits=v['output_bits']) for k,v in report.items()}))
