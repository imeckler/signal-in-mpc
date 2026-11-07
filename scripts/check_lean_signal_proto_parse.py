#!/usr/bin/env python3
"""Compare shared Signal protobuf parser with pinned Prost and compiler artifacts.
Prost fixtures are differential evidence, not an Aeneas refinement theorem.
"""
import argparse, hashlib, json, os, random, re, subprocess, sys
from datetime import datetime, timezone
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load
from backend_adapter.aig import statistics
from scripts.check_lean_crypto import evaluate_lanes, compile_and_check

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def vi(n,width=None):
    a=[n&127]; n >>=7
    while n: a.append(n&127); n >>=7
    if width: a += [0]*(width-len(a))
    return bytes(x|(128 if i+1<len(a) else 0) for i,x in enumerate(a))
def field(tag,data): return vi(tag*8+2)+vi(len(data))+data
def scalar(tag,value): return vi(tag*8)+vi(value)
def parse_body(b):
    at=0; stack=[]; fields={}
    def read():
        nonlocal at
        n=0
        for i in range(10):
            if at>=len(b): raise ValueError('underflow')
            x=b[at];at+=1
            if i==9 and x>1: raise ValueError('overflow')
            n|=(x&127)<<(i*7)
            if x<128:return n
        raise ValueError('varint')
    while at<len(b):
        key=read();tag=key>>3;kind=key&7
        if key>0xffffffff or not tag or kind>5:raise ValueError('key')
        known=not stack and tag<=6
        if known and kind != (0 if tag in (2,3) else 2):raise ValueError('type')
        if kind==4:
            if not stack or stack.pop()!=tag:raise ValueError('group')
            continue
        if len(stack)>=100:raise ValueError('depth')
        if kind==3:stack.append(tag);continue
        if kind==0:
            value=read();span=(at,value,value&0xffffffff)
        else:
            n=read() if kind==2 else (8 if kind==1 else 4)
            if n>len(b)-at:raise ValueError('span')
            span=(at,n,b[at:at+n]);at+=n
        if known:fields[tag]=span
    if stack:raise ValueError('unclosed')
    return fields

def oracle_view(b):
    try:f=parse_body(b)
    except ValueError:return 'err'
    parts=['ok']
    for tag in range(1,7):
        if tag not in f:parts.append('-')
        elif tag in(2,3):parts.append(str(f[tag][2]))
        else:parts.append(f[tag][2].hex())
    return '|'.join(parts)
def parse(w):
    try:
        if len(w)<9 or w[0]>>4 not in(3,4):raise ValueError('version')
        f=parse_body(w[1:-8])
        if not all(t in f for t in(1,2,4)):raise ValueError('required')
        pk=f[1][2]
        if len(pk)<33 or pk[0]!=5:raise ValueError('pk')
        word=lambda n:n.to_bytes(8,'big')
        span=lambda tag:word(f[tag][0])+word(f[tag][1]) if tag in f else bytes(16)
        return b'\xff'+pk[1:33]+f[2][2].to_bytes(4,'big')+f.get(3,(0,0,0))[2].to_bytes(4,'big')+span(4)+span(5)+bytes([6 in f])+span(6)
    except ValueError:return bytes(90)

def fixtures():
    rng=random.Random(0x50524f544f);pk=b'\x05'+rng.randbytes(32)
    base=field(1,pk)+scalar(2,7)+field(4,rng.randbytes(16)); cases=[]
    def add(label,b,version=0x34):cases.append((label,bytes([version])+b+bytes(8)))
    add('minimal',base); add('empty-ciphertext',field(1,pk)+scalar(2,0)+field(4,b''))
    for v in range(256):add(f'version-{v}',base,v)
    for tag in range(1,7):
        good=scalar(tag,99) if tag in(2,3) else field(tag,pk if tag==1 else b'')
        add(f'duplicate-{tag}',base+good)
        add(f'wrong-type-{tag}',base+(field(tag,b'') if tag in(2,3) else scalar(tag,0))+good)
    for val in(0,127,128,2**32-1,2**32,2**64-1):
        for tag in(2,3,7):add(f'scalar-{tag}-{val}',base+scalar(tag,val))
    for byte in range(256):add(f'tenth-byte-{byte}',base+b'\x10'+b'\x80'*9+bytes([byte]))
    for width in range(1,11):
        add(f'noncanonical-{width}',base+b'\x10'+vi(9,width))
        add(f'noncanonical-key-{width}',base+vi(56,width)+b'\x00')
    for kind in range(8):
        for n in range(11):add(f'unknown-kind-{kind}-tail-{n}',base+bytes([56+kind])+rng.randbytes(n))
    for depth in(1,2,98,99,100,101):
        for middle in(b'',b'\x40\x01',b'\x0a\x00'):
            add(f'group-{depth}-{middle.hex()}',base+b'\x3b'*depth+middle+b'\x3c'*depth)
    for b in(b'\x3b\x44',b'\x3b',b'\x3c',b'\x3b\x0a\x01\xff\x3c',b'\x39'+bytes(8),b'\x3d'+bytes(4),b'\x3a\x00'):
        add('unknown-'+b.hex(),base+b)
    for tag in range(1,7):
        for n in(0,1,31,32,33,34,64):
            add(f'bytes-{tag}-{n}',base+field(tag,(pk+bytes(64))[:n]))
    for i in range(200):
        fields=[field(1,pk),scalar(2,rng.randrange(2**64)),scalar(3,rng.randrange(2**64)),field(4,rng.randbytes(rng.randrange(33))),field(5,rng.randbytes(rng.randrange(20))),field(6,rng.randbytes(rng.randrange(40)))]
        rng.shuffle(fields);b=b''.join(fields);add(f'reorder-{i}',b)
        if i<100:
            j=rng.randrange(len(b));add(f'mutation-{i}',b[:j]+rng.randbytes(1)+b[j+1:])
    for n in range(len(base)+1):add(f'truncate-{n}',base[:n])
    for n in(0,1,8):cases.append((f'short-{n}',bytes(n)))
    for i in range(100):add(f'random-{i}',rng.randbytes(rng.randrange(100)))
    for key in(0,1,7,2**32-1,2**32,2**64-1):add(f'key-{key}',base+vi(key)+bytes(9))
    return cases

def main():
    cli=argparse.ArgumentParser();cli.add_argument('--artifacts',action='store_true');cli.add_argument('--compile-backend',action='store_true');opt=cli.parse_args()
    subprocess.run(['lake','build','TlsMpc.Signal.ProtoParseProofs'],cwd=ROOT,check=True)
    checks=ROOT/'SignalReference/ProtoParseChecks.lean'
    checked=subprocess.run(['lake','env','lean',str(checks)],cwd=ROOT,capture_output=True,text=True,check=True)
    names=re.findall(r'^#print axioms (\S+)',checks.read_text(),re.M)
    found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",checked.stdout)
    assert [n for n,_ in found]==names
    for n,a in found:assert not({x.strip() for x in a.split(',') if x.strip()}-{'propext','Quot.sound','Classical.choice'}),(n,a)
    oracle=ROOT/'SignalReference/ProtoParseWork/Oracle'; env=os.environ.copy();env['RUSTC']=str(ROOT/'.deps/rust-nightly-2026-08-18/bin/rustc')
    target=ROOT/'.deps/signal-prost-oracle-target'
    subprocess.run([str(ROOT/'.deps/rust-nightly-2026-08-18/bin/cargo'),'build','--offline','--target-dir',str(target)],cwd=oracle,env=env,check=True)
    work=ROOT/'SignalReference/ProtoParseWork'
    assert (work/'Export.lean').read_bytes()==(ROOT/'SignalReference/ProtoParseExport.lean').read_bytes()
    subprocess.run(['lake','build'],cwd=work,check=True)
    exporter=str(work/'.lake/build/bin/emit_proto_parse')
    cases=fixtures();bodies=[w[1:-8] if len(w)>=9 else b'' for _,w in cases]
    observed=subprocess.run([str(target/'debug/signal-prost-parser-oracle')],input=''.join(b.hex()+'\n' for b in bodies),capture_output=True,text=True,check=True).stdout.splitlines()
    expected=[oracle_view(b) for b in bodies]
    assert observed==expected,[(cases[i][0],got,want) for i,(got,want) in enumerate(zip(observed,expected)) if got!=want][:20]
    result=subprocess.run([exporter,'evaluate'],cwd=ROOT,input=''.join(json.dumps(list(w))+'\n' for _,w in cases),capture_output=True,text=True,check=True,timeout=600)
    got=[bytes(json.loads(x)) for x in result.stdout.splitlines()];want=[parse(w) for _,w in cases]
    assert len(got)==len(want),(len(got),len(want),result.stderr)
    assert got==want,[(label,w.hex(),g.hex(),e.hex()) for (label,w),g,e in zip(cases,got,want) if g!=e][:10]
    directory=ROOT/'.deps/signal-proto-parse-artifacts';directory.mkdir(exist_ok=True)
    fixture=directory/'fixtures.json';fixture.write_text(json.dumps([{'label':l,'input':w.hex(),'output':e.hex(),'prost':p} for (l,w),e,p in zip(cases,want,observed)],indent=2)+'\n')
    rows=[]
    if opt.artifacts or opt.compile_backend:
        # Add unknown length-delimited padding to make one public capacity.
        for size in(64,128):
            selected=[]
            for label,w in cases:
                if len(w)>size-2:continue
                b=w[1:-8]+b'\x7a'+vi(size-len(w)-2)+bytes(size-len(w)-2)
                padded=w[:1]+b+w[-8:]
                if len(padded)!=size:continue
                selected.append((label,padded,parse(padded)))
            path=directory/f'signal-protobuf-parse-{size}.json'
            with path.open('w') as out:subprocess.run([exporter,'signal-protobuf-parse',str(size)],cwd=ROOT,stdout=out,check=True,timeout=600)
            artifact=load(path);got=evaluate_lanes(artifact,[w for _,w,_ in selected]);assert got==[e for _,_,e in selected],size
            row={'wire_bytes':size,'fixture_lanes':len(selected),'artifact_sha256':digest(path),'adapter_operations':statistics(artifact),'all_outputs_match':True}
            if opt.compile_backend:
                picked=[next(x for x in selected if x[2][0]==255)]+[x for x in selected if x[2][0]==0][:15]
                row['mpc_compilations']=[compile_and_check(path,[x[1] for x in picked],[x[2] for x in picked],batch) for batch in(1,16)]
            rows.append(row);print(json.dumps(row),flush=True)
    files=set()
    def visit(module):
        if not module.startswith('TlsMpc'):return
        p=ROOT/(module.replace('.','/')+'.lean')
        if p in files:return
        files.add(p)
        for m in re.findall(r'^import ([\w.]+)',p.read_text(),re.M):visit(m)
    visit('TlsMpc.Signal.ProtoParseProofs')
    files|={work/'Export.lean',work/'lakefile.toml',work/'lean-toolchain',Path(__file__),checks,ROOT/'SignalReference/ProtoParseExport.lean',oracle/'Cargo.toml',oracle/'Cargo.lock',oracle/'src/main.rs',ROOT/'.deps/libsignal-vendor/prost-0.14.4/src/encoding.rs',ROOT/'.deps/libsignal-vendor/prost-0.14.4/src/encoding/varint.rs',ROOT/'.deps/libsignal-vendor/prost-0.14.4/src/message.rs',ROOT/'.deps/libsignal-v0.106.1/rust/protocol/src/proto/wire.proto',ROOT/'.deps/libsignal-v0.106.1/rust/protocol/src/protocol.rs',ROOT/'.deps/libsignal-v0.106.1/rust/core/src/curve.rs'}
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'checked_endpoints':len(names),'fixture_count':len(cases),'prost_oracle_all_match':True,'concrete_all_match':True,'fixture_sha256':digest(fixture),'cases':rows,'source_sha256':{str(p.relative_to(ROOT)):digest(p) for p in sorted(files)},'full_actual_rust_parser_refinement':False,'native_mpc_executed':False,'public_parameters':['wire byte length'],'output_bytes':90,'semantics':['last duplicate wins','unknown fields and groups','recursion limit100','uint64 overflow rejected','uint32 truncation','publickey trailing bytes allowed'],'custom_axioms':[]}
    (ROOT/'benchmarks/results/lean-signal-proto-parse-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    (ROOT/'SignalReference/proto-parse-axioms.txt').write_text(checked.stdout)
    (ROOT/'SignalReference/proto-parse-proof-check.json').write_text(json.dumps({'checked_endpoints':len(names),'theorems':names,'source_sha256':report['source_sha256'],'custom_axioms':[],'full_actual_rust_parser_refinement':False},indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='source_sha256'}),flush=True)
if __name__=='__main__':main()
