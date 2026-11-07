#!/usr/bin/env python3
"""General shared-layout receive against OpenSSL CBC, Python HMAC and pinned-Prost-checked parsing."""
import argparse,hashlib,hmac,json,re,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from scripts.check_lean_signal_proto_parse import parse,parse_body,field,scalar,vi,digest
from scripts.check_lean_signal_receive import cbc,mac,sample
from scripts.check_lean_crypto import evaluate_lanes,compile_and_check
from backend_adapter.boolean import load
from backend_adapter.aig import statistics

def expected(raw):
    key,iv,mk,si,ri,wanted,wire=raw[:32],raw[32:48],raw[48:80],raw[80:112],raw[112:144],raw[144:180],raw[180:]
    capacity=max(0,len(wire)-9)//16*16;bad=bytes(9+capacity)
    if parse(wire)[0]!=255:return bad
    f=parse_body(wire[1:-8]);ct=f[4][2]
    if not ct or len(ct)%16 or len(ct)>capacity:return bad
    if not hmac.compare_digest(mac(mk,si,ri,wire[:-8]),wire[-8:]):return bad
    if 6 in f:
        if f[6][2]!=wanted or wanted[0] not in(0,1) or wanted[18] not in(0,1) or not(1<=wanted[17]<=127 and 1<=wanted[35]<=127):return bad
    plain=cbc(key,iv,ct,True);n=plain[-1]
    if not(1<=n<=16) or plain[-n:]!=bytes([n])*n:return bad
    plain=plain[:-n]
    return b'\xff'+len(plain).to_bytes(8,'big')+plain+bytes(capacity-len(plain))

def fixtures(size):
    material=sample('proto-receive-material',144);key,iv,mk,si,ri=material[:32],material[32:48],material[48:80],material[80:112],material[112:]
    address=b'\x00'+sample('sender',16)+b'\x01\x01'+sample('receiver',16)+b'\x7f'
    pk=b'\x05'+sample('ratchet',32);cases=[]
    def add(label,ct=None,padded=None,extra=b'',version=0x44,fields=None,tamper=None,wanted=address):
        if ct is None:ct=cbc(key,iv,padded if padded is not None else b'hello'+b'\x0b'*11)
        body=(field(1,pk)+scalar(2,9)+field(4,ct) if fields is None else fields)+extra
        gap=size-9-len(body)
        if gap<2:return
        n=gap-2
        if n>=128:n-=1
        body+=field(15,bytes(n))
        assert len(body)+9==size
        content=bytes([version])+body;wire=content+mac(mk,si,ri,content)
        raw=material+wanted+wire
        if tamper is not None:
            raw=bytearray(raw);raw[tamper]^=1;raw=bytes(raw)
        cases.append((label,raw,expected(raw)))
    add('valid')
    add('bad-mac',tamper=-1)
    add('wrong-sender',tamper=80)
    add('wrong-receiver',tamper=112)
    add('wrong-mac-key',tamper=48)
    add('wrong-cipher-key',tamper=0)
    add('wrong-iv',tamper=32)
    for n in range(1,17):add(f'padding-{n}',padded=sample('plain',16-n)+bytes([n])*n)
    for n in(0,17,255):add(f'bad-padding-{n}',padded=bytes(15)+bytes([n]))
    add('bad-padding-suffix',padded=bytes(13)+b'\x03\x02\x03')
    for n in(0,1,15,17,31):add(f'ct-length-{n}',ct=bytes(n))
    for n in(32,48,64):add(f'ct-blocks-{n}',padded=sample('plaintext',n-1)+b'\x01')
    for version in(0x00,0x2f,0x30,0x3f,0x40,0x4f,0x50):add(f'version-{version}',version=version)
    add('duplicate-last-valid',extra=field(4,cbc(key,iv,b'world'+b'\x0b'*11)))
    add('duplicate-last-empty',extra=field(4,b''))
    add('duplicate-last-malformed',extra=scalar(4,0))
    add('unknown-group',extra=b'\x3b\x22\x01\xff\x3c')
    add('unknown-group-mismatch',extra=b'\x3b\x44')
    add('u32-truncation',extra=scalar(2,2**63+9))
    add('u64-overflow',extra=b'\x10'+b'\x80'*9+b'\x02')
    for a,label in((address,'valid'),(b'','empty'),(address[:-1],'short'),(bytes(36),'bad')):
        add('address-'+label,extra=field(6,a))
    add('address-last-valid',extra=field(6,bytes(36))+field(6,address))
    add('address-last-bad',extra=field(6,address)+field(6,bytes(36)))
    invalid=b'\x02'+address[1:];add('expected-kind-invalid',extra=field(6,invalid),wanted=invalid)
    invalid=address[:17]+b'\x00'+address[18:];add('expected-device-invalid',extra=field(6,invalid),wanted=invalid)
    add('reordered',fields=field(4,cbc(key,iv,b'hello'+b'\x0b'*11))+scalar(2,7)+field(1,pk))
    return cases

def main():
    cli=argparse.ArgumentParser();cli.add_argument('--compile-backend',action='store_true');opt=cli.parse_args()
    work=ROOT/'SignalReference/ProtoReceiveWork';assert(work/'Export.lean').read_bytes()==(ROOT/'SignalReference/ProtoReceiveExport.lean').read_bytes()
    subprocess.run(['lake','build'],cwd=work,check=True)
    checks=ROOT/'SignalReference/ProtoReceiveChecks.lean';p=subprocess.run(['lake','env','lean',str(checks)],cwd=ROOT,check=True,text=True,capture_output=True)
    names=re.findall(r'^#print axioms (\S+)',checks.read_text(),re.M);found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",p.stdout)
    assert [n for n,_ in found]==names
    for n,a in found:assert not({x.strip() for x in a.split(',') if x.strip()}-{'propext','Quot.sound','Classical.choice'}),(n,a)
    command=str(work/'.lake/build/bin/emit_proto_receive');directory=ROOT/'.deps/signal-proto-receive-artifacts';directory.mkdir(exist_ok=True);rows=[]
    for size in(96,160):
        cases=fixtures(size);result=subprocess.run([command,'evaluate'],input=''.join(json.dumps(list(w))+'\n' for _,w,_ in cases),text=True,capture_output=True,check=True,timeout=600)
        got=[bytes(json.loads(x)) for x in result.stdout.splitlines()];want=[e for _,_,e in cases]
        assert got==want,[(l,g.hex(),e.hex()) for(l,_,e),g in zip(cases,got) if g!=e]
        path=directory/f'signal-protobuf-receive-{size}.json'
        with path.open('w') as out:subprocess.run([command,'signal-protobuf-receive',str(size)],stdout=out,check=True,timeout=600)
        artifact=load(path);got=evaluate_lanes(artifact,[w for _,w,_ in cases]);assert got==want,[(l,g.hex(),e.hex()) for(l,_,e),g in zip(cases,got) if g!=e]
        fixture=path.with_name(path.stem+'-fixtures.json');fixture.write_text(json.dumps([{'label':l,'input':w.hex(),'output':e.hex()} for l,w,e in cases],indent=2)+'\n')
        row={'wire_bytes':size,'fixture_lanes':len(cases),'artifact_sha256':digest(path),'fixture_sha256':digest(fixture),'adapter_operations':statistics(artifact),'all_outputs_match':True}
        if opt.compile_backend:row['mpc_compilations']=[compile_and_check(path,[w for _,w,_ in cases],[e for _,_,e in cases],batch) for batch in(1,16)]
        rows.append(row);print(json.dumps(row),flush=True)
    files=set()
    def visit(module):
        if not module.startswith('TlsMpc'):return
        p=ROOT/(module.replace('.','/')+'.lean')
        if p in files:return
        files.add(p)
        for m in re.findall(r'^import ([\w.]+)',p.read_text(),re.M):visit(m)
    visit('TlsMpc.Signal.ProtoReceive')
    files|={Path(__file__),checks,ROOT/'SignalReference/ProtoReceiveExport.lean',work/'Export.lean',work/'lakefile.toml',ROOT/'scripts/check_lean_signal_proto_parse.py',ROOT/'scripts/check_lean_signal_receive.py'}
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'checked_endpoints':len(names),'source_sha256':{str(p.relative_to(ROOT)):digest(p) for p in sorted(files)},'cases':rows,'full_actual_rust_receive_refinement':False,'native_mpc_executed':False,'all_runtime_values_secret':True,'public_parameters':['wire byte length'],'session_key_selection_and_commit':False,'custom_axioms':[]}
    (ROOT/'benchmarks/results/lean-signal-proto-receive-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    (ROOT/'SignalReference/proto-receive-axioms.txt').write_text(p.stdout)
    (ROOT/'SignalReference/proto-receive-proof-check.json').write_text(json.dumps({'checked_endpoints':len(names),'theorems':names,'source_sha256':report['source_sha256'],'custom_axioms':[]},indent=2)+'\n')
if __name__=='__main__':main()
