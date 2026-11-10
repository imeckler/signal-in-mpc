"""Export the Lean key-derivation circuits that consume the X25519 word.

Circuits: `TlsMpc/HybridKdf.lean` (`tlsHandshakeSecrets`, `signalDhRatchet`),
which wrap the existing Lean TLS and Signal derivations so that the DH result
enters as the 255-bit word produced by the field conversion; the split into
little-endian bytes is part of the Lean circuit. Compiled by the bit-vector
compiler and printed by `EmitHybridKdf.lean`. The DAG traversal and XOR
recognition here are the shared, unverified `backend_adapter.aig` code.

One bit order everywhere: variable v, bit b (weight 2^b) is wire offset(v)+b;
output 8*j+b is bit b of output byte j. Inputs: the 255-bit word, then 32 bytes
(transcript hash for TLS, root key for Signal). Each circuit is checked against
an independent HMAC/HKDF implementation before it is pinned. Also pins the
equality circuits (TlsMpc/WordMask.lean) used by the fixtures.
"""
import hashlib,hmac,json,pathlib,random,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent;OUT=ROOT/'.deps/emp-hybrid-word-v1';OUT.mkdir(exist_ok=True)
sys.path.insert(0,str(ROOT))
from backend_adapter.aig import validate,_plan,_xor_sources
P=2**255-19
def lower(image):
    validate(image)
    offsets=[];n=0
    for w in image['input_widths']:offsets.append(n);n+=w
    gates=[]
    def gate(op,a,b=0):gates.append((op,a,b));return n+len(gates)-1
    zero=None;negated={}
    def inv(w):
        if w not in negated:negated[w]=gate('N',w)
        return negated[w]
    nodes=image['nodes'];kinds=_plan(nodes,image['outputs'],True);wires={}
    for i,node in enumerate(nodes):
        if not kinds[i]:continue
        if node==[0]:
            if zero is None:zero=gate('X',0,0)
            wires[i]=zero
        elif node[0]==1:wires[i]=offsets[node[1]]+node[3]
        else:
            a,ai,b,bi=_xor_sources(nodes,node) if kinds[i]==2 else node[1:]
            a,b=wires[a],wires[b];wires[i]=gate('X' if kinds[i]==2 else 'A',inv(a) if ai else a,inv(b) if bi else b)
    return n,gates,[inv(wires[w]) if flip else wires[w] for w,flip in image['outputs']]
def evaluate(gates,outputs,word,other):
    wires=[(word>>i)&1 for i in range(255)]+[(byte>>b)&1 for byte in other for b in range(8)]
    for op,a,b in gates:wires.append(1-wires[a] if op=='N' else (wires[a]^wires[b] if op=='X' else wires[a]&wires[b]))
    out=[wires[w] for w in outputs];return bytes(sum(out[8*j+b]<<b for b in range(8)) for j in range(len(out)//8))
def extract(salt,ikm):return hmac.new(salt,ikm,hashlib.sha256).digest()
def expand_label(secret,label,context):
    full=b'tls13 '+label;info=(32).to_bytes(2,'big')+bytes([len(full)])+full+bytes([len(context)])+context
    return hmac.new(secret,info+b'\x01',hashlib.sha256).digest()
def tls_reference(ecdhe,transcript):
    empty=hashlib.sha256(b'').digest();zero=bytes(32)
    handshake=extract(expand_label(extract(zero,zero),b'derived',empty),ecdhe)
    return handshake+expand_label(handshake,b'c hs traffic',transcript)+expand_label(handshake,b's hs traffic',transcript)+extract(expand_label(handshake,b'derived',empty),zero)
def hkdf(salt,ikm,info,length):
    prk=extract(salt,ikm);out=b'';block=b'';i=1
    while len(out)<length:block=hmac.new(prk,block+info+bytes([i]),hashlib.sha256).digest();out+=block;i+=1
    return out[:length]
def ratchet_reference(agreement,root):
    if agreement==bytes(32):return bytes([0])+root+bytes(36)
    return bytes([255])+hkdf(root,agreement,b'WhisperRatchet',64)+bytes(4)
CIRCUITS={'tls-handshake-secrets':(tls_reference,128,'TLS_HANDSHAKE_SECRETS'),'signal-dh-ratchet':(ratchet_reference,69,'SIGNAL_DH_RATCHET')}
subprocess.run(['lake','build','hybrid_kdf_emitter','word_mask_emitter'],cwd=ROOT,check=True,capture_output=True)
rng=random.Random(20261110);report={};pins=[]
for name,(reference,out_bytes,ident) in CIRCUITS.items():
    raw=subprocess.run(['lake','exe','hybrid_kdf_emitter',name],cwd=ROOT,check=True,capture_output=True).stdout
    n,gates,outputs=lower(json.loads(raw))
    if n!=511 or len(outputs)!=8*out_bytes:raise ValueError(name+' shape')
    for case in range(4):
        word=0 if case==3 else rng.randrange(P);other=rng.randbytes(32)
        if evaluate(gates,outputs,word,other)!=reference(word.to_bytes(32,'little'),other):raise AssertionError(name)
    text='EMP_HYBRID_BOOL_V1\n%d %d %d\n'%(n,len(gates),len(outputs))+''.join(('N %d\n'%a) if op=='N' else '%s %d %d\n'%(op,a,b) for op,a,b in gates)+'O '+' '.join(map(str,outputs))+'\n'
    (OUT/(name+'.flat')).write_text(text);digest=hashlib.sha256(text.encode()).hexdigest();pins.append('inline constexpr const char* %s_SHA="%s";'%(ident,digest))
    report[name]=dict(lean_image_sha256=hashlib.sha256(raw).hexdigest(),flat_sha256=digest,and_gates=sum(g[0]=='A' for g in gates),input_bits=n,output_bytes=out_bytes,cases_checked=4)
for width in (1024,552):
    text=subprocess.run(['lake','exe','word_mask_emitter','equal',str(width)],cwd=ROOT,check=True,capture_output=True).stdout.decode()
    (OUT/('equal-%d.flat'%width)).write_text(text);digest=hashlib.sha256(text.encode()).hexdigest();pins.append('inline constexpr const char* EQUAL_%d_SHA="%s";'%(width,digest))
    report['equal-%d'%width]=dict(flat_sha256=digest,and_gates=text.count('\nA '))
(OUT/'kdf_circuit_pins.h').write_text('#pragma once\nnamespace emp_hybrid {\n'+'\n'.join(pins)+'\n}\n')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
out=dict(passed=True,circuits=report,lean_sources={f:sha(ROOT/f) for f in ('TlsMpc/HybridKdf.lean','TlsMpc/TlsKdf.lean','TlsMpc/Signal/DhRatchet.lean','handshake_backend/EmpHybridWork/EmitHybridKdf.lean')},reference='hashlib HMAC/HKDF-SHA256: RFC 8446 handshake key schedule; Signal WhisperRatchet with all-zero agreement keeping the old root',scope='Lean key-derivation circuits taking the X25519 word directly, lowered by the shared unverified adapter with one fixed bit order and checked against an independent implementation. The Lean theorems cover the bit-vector expressions and their compiled graphs; the lowering and loader are outside them.')
(HERE/'kdf-circuit-report.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v['and_gates'] for k,v in report.items()}))
