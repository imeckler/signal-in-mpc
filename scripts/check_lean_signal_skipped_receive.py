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

from scripts.check_lean_signal_proto_receive import expected as proto_expected

def material(seed,salt):
    prk=hmac.digest(salt,seed,'sha256');block=b'';out=b''
    for i in range(1,4):block=hmac.digest(prk,block+b'WhisperMessageKeys'+bytes([i]),'sha256');out+=block
    return out[:32],out[32:64],out[64:80]
def expected(raw,count=4):
    p=raw[0];pq,sender,receiver,address=raw[1:33],raw[33:65],raw[65:97],raw[97:133]
    old=raw[133:133+69*count];wire=raw[133+69*count:];parsed=parse(wire)
    slots=[old[i*69:(i+1)*69] for i in range(count)];hit=None
    for i,slot in enumerate(slots):
        if slot[0]==255 and slot[1:33]==parsed[1:33] and slot[33:37]==parsed[33:37]:hit=i;break
    seed=slots[hit][37:] if hit is not None else bytes(32)
    key,mk,iv=material(seed,pq if p==1 else bytes(32));opened=proto_expected(key+iv+mk+sender+receiver+address+wire)
    if hit is not None and opened[0]==255 and p in(0,1):return b'\xff'+b''.join(slots[:hit]+slots[hit+1:]+[bytes(69)])+opened[1:]
    return b'\x00'+old+bytes(len(opened)-1)
def fixtures(size):
    ratchet=sample('skip-ratchet',32);seed=sample('skip-seed',32);pq=sample('skip-pq',32);sender=sample('skip-sender',32);receiver=sample('skip-receiver',32)
    address=b'\x00'+sample('sender',16)+b'\x01\x01'+sample('receiver',16)+b'\x7f';counter=(9).to_bytes(4,'big')
    good=b'\xff'+ratchet+counter+seed;other=b'\xff'+sample('other-key',32)+bytes(4)+sample('other-seed',32);cases=[]
    def add(label,slots=None,present=0,tamper=None,extra=b'',padded=None):
        if slots is None:slots=[other,good,other,bytes(69)]
        key,mk,iv=material(seed,pq if present==1 else bytes(32));ct=cbc(key,iv,padded if padded is not None else b'hello'+b'\x0b'*11)
        body=field(1,b'\x05'+ratchet)+scalar(2,9)+field(4,ct)+extra;gap=size-9-len(body)
        if gap<2:return
        body+=field(15,bytes(gap-2));assert len(body)+9==size
        content=b'\x44'+body;wire=content+mac(mk,sender,receiver,content)
        raw=bytes([present])+pq+sender+receiver+address+b''.join(slots)+wire
        if tamper is not None:raw=bytearray(raw);raw[tamper]^=1;raw=bytes(raw)
        cases.append((label,raw,expected(raw)))
    add('valid');add('mac-failure',tamper=-1);add('sender-failure',tamper=33)
    for p in(0,1,2,255):add(f'PQpresence-{p}',present=p)
    for at in range(4):
        slots=[other]*4;slots[at]=good;add(f'slot-{at}',slots)
    add('not-found',[other]*4);add('empty-store',[bytes(69)]*4)
    add('duplicate-first',[good,other,good,other]);add('duplicate-bad-first',[good[:37]+bytes(32),good,other,other])
    for valid in(0,1,127,254,255):add(f'valid-mask-{valid}',[bytes([valid])+good[1:],other,other,other])
    add('counter-not-found',extra=scalar(2,10));add('counter-duplicate-last-found',extra=scalar(2,10)+scalar(2,9))
    add('bad-padding',padded=bytes(16))
    add('unknown-group',extra=b'\x3b\x10\x01\x3c')
    return cases

def main():
    cli=argparse.ArgumentParser();cli.add_argument('--compile-backend',action='store_true');opt=cli.parse_args()
    work=ROOT/'SignalReference/SkippedReceiveWork';assert(work/'Export.lean').read_bytes()==(ROOT/'SignalReference/SkippedReceiveExport.lean').read_bytes()
    subprocess.run(['lake','build'],cwd=work,check=True)
    checks=ROOT/'SignalReference/SkippedReceiveChecks.lean';p=subprocess.run(['lake','env','lean',str(checks)],cwd=ROOT,check=True,text=True,capture_output=True)
    names=re.findall(r'^#print axioms (\S+)',checks.read_text(),re.M);found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",p.stdout)
    assert [n for n,_ in found]==names
    for n,a in found:assert not({x.strip() for x in a.split(',') if x.strip()}-{'propext','Quot.sound','Classical.choice'}),(n,a)
    command=str(work/'.lake/build/bin/emit_skipped_receive');directory=ROOT/'.deps/signal-skipped-receive-artifacts';directory.mkdir(exist_ok=True);rows=[]
    for size in(96,):
        cases=fixtures(size);result=subprocess.run([command,'evaluate','4'],input=''.join(json.dumps(list(w))+'\n' for _,w,_ in cases),text=True,capture_output=True,check=True,timeout=600)
        got=[bytes(json.loads(x)) for x in result.stdout.splitlines()];want=[e for _,_,e in cases]
        assert got==want,[(l,g.hex(),e.hex()) for(l,_,e),g in zip(cases,got) if g!=e]
        path=directory/f'signal-skipped-receive-4-{size}.json'
        with path.open('w') as out:subprocess.run([command,'signal-skipped-receive','4',str(size)],stdout=out,check=True,timeout=600)
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
    visit('TlsMpc.Signal.SkippedReceive')
    files|={Path(__file__),checks,ROOT/'SignalReference/SkippedReceiveExport.lean',work/'Export.lean',work/'lakefile.toml',ROOT/'scripts/check_lean_signal_proto_parse.py',ROOT/'scripts/check_lean_signal_receive.py',ROOT/'scripts/check_lean_signal_proto_receive.py'}
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'checked_endpoints':len(names),'source_sha256':{str(p.relative_to(ROOT)):digest(p) for p in sorted(files)},'cases':rows,'full_actual_rust_receive_refinement':False,'native_mpc_executed':False,'all_runtime_values_secret':True,'public_parameters':['wire byte length'],'skipped_seed_lookup_and_transactional_commit':True,'legacy_expanded_key_records':False,'custom_axioms':[]}
    (ROOT/'benchmarks/results/lean-signal-skipped-receive-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    (ROOT/'SignalReference/skipped-receive-axioms.txt').write_text(p.stdout)
    (ROOT/'SignalReference/skipped-receive-proof-check.json').write_text(json.dumps({'checked_endpoints':len(names),'theorems':names,'source_sha256':report['source_sha256'],'custom_axioms':[]},indent=2)+'\n')
if __name__=='__main__':main()
