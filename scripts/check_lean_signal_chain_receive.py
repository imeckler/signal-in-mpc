#!/usr/bin/env python3
"""Transactional selected-chain receive against independent HMAC/CBC derivation fixtures."""
import argparse,hashlib,hmac,json,re,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from scripts.check_lean_signal_proto_parse import parse,parse_body,field,scalar,vi,digest
from scripts.check_lean_signal_receive import cbc,mac,sample
from scripts.check_lean_crypto import evaluate_lanes,compile_and_check
from backend_adapter.boolean import load
from backend_adapter.aig import statistics

from scripts.check_lean_signal_chain_send import derive
from scripts.check_lean_signal_proto_receive import expected as proto_expected

def expected(raw):
    present=raw[0];ratchet=raw[1:33];counter=raw[33:37];chain=raw[37:69];pq=raw[69:101]
    sender,receiver,addresses,wire=raw[101:133],raw[133:165],raw[165:201],raw[201:]
    next_key,key,mk,iv=derive(chain,pq if present==1 else bytes(32))
    opened=proto_expected(key+iv+mk+sender+receiver+addresses+wire)
    parsed=parse(wire)
    accept=opened[0]==255 and parsed[1:33]==ratchet and parsed[33:37]==counter and present in(0,1) and counter!=b'\xff'*4
    if accept:return b'\xff'+next_key+(int.from_bytes(counter,'big')+1).to_bytes(4,'big')+opened[1:]
    return b'\x00'+chain+counter+bytes(len(opened)-1)

def fixtures(size):
    ratchet=sample('chain-receive-ratchet',32);chain=sample('chain-receive-chain',32);pq=sample('chain-receive-pq',32)
    sender=sample('chain-receive-sender',32);receiver=sample('chain-receive-receiver',32)
    address=b'\x00'+sample('sender',16)+b'\x01\x01'+sample('receiver',16)+b'\x7f';cases=[]
    def add(label,present=0,counter=9,extra=b'',tamper=None,padded=None):
        next_key,key,mk,iv=derive(chain,pq if present==1 else bytes(32))
        ct=cbc(key,iv,padded if padded is not None else b'hello'+b'\x0b'*11)
        body=field(1,b'\x05'+ratchet)+scalar(2,counter)+field(4,ct)+extra
        gap=size-9-len(body)
        if gap<2:return
        n=gap-2
        if n>=128:n-=1
        body+=field(15,bytes(n));assert len(body)+9==size
        content=b'\x44'+body;wire=content+mac(mk,sender,receiver,content)
        raw=bytes([present])+ratchet+counter.to_bytes(4,'big')+chain+pq+sender+receiver+address+wire
        if tamper is not None:
            raw=bytearray(raw);raw[tamper]^=1;raw=bytes(raw)
        cases.append((label,raw,expected(raw)))
    add('valid')
    for p in(0,1,2,255):add(f'presence-{p}',present=p)
    for off,label in((1,'ratchet'),(36,'counter'),(37,'chain'),(69,'pq'),(101,'sender'),(133,'receiver'),(-1,'mac')):
        add('tamper-'+label,tamper=off)
        if off==69:add('tamper-present-pq',present=1,tamper=off)
    for c in(0,127,128,2**32-2,2**32-1):add(f'counter-{c}',counter=c)
    for n in(1,16,17,32):add(f'plaintext-blocks-{n}',padded=sample('plain',((n//16)+1)*16-n)+bytes([n])*n if n<=16 else bytes(15)+b'\x00')
    add('duplicate-counter-last-mismatch',extra=scalar(2,8))
    add('duplicate-counter-last-match',extra=scalar(2,8)+scalar(2,9))
    add('address-valid',extra=field(6,address))
    add('address-invalid',extra=field(6,bytes(36)))
    add('unknown-group',extra=b'\x3b\x10\x01\x3c')
    return cases

def main():
    cli=argparse.ArgumentParser();cli.add_argument('--compile-backend',action='store_true');opt=cli.parse_args()
    work=ROOT/'SignalReference/ChainReceiveWork';assert(work/'Export.lean').read_bytes()==(ROOT/'SignalReference/ChainReceiveExport.lean').read_bytes()
    subprocess.run(['lake','build'],cwd=work,check=True)
    checks=ROOT/'SignalReference/ChainReceiveChecks.lean';p=subprocess.run(['lake','env','lean',str(checks)],cwd=ROOT,check=True,text=True,capture_output=True)
    names=re.findall(r'^#print axioms (\S+)',checks.read_text(),re.M);found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",p.stdout)
    assert [n for n,_ in found]==names
    for n,a in found:assert not({x.strip() for x in a.split(',') if x.strip()}-{'propext','Quot.sound','Classical.choice'}),(n,a)
    command=str(work/'.lake/build/bin/emit_chain_receive');directory=ROOT/'.deps/signal-chain-receive-artifacts';directory.mkdir(exist_ok=True);rows=[]
    for size in(96,):
        cases=fixtures(size);result=subprocess.run([command,'evaluate'],input=''.join(json.dumps(list(w))+'\n' for _,w,_ in cases),text=True,capture_output=True,check=True,timeout=600)
        got=[bytes(json.loads(x)) for x in result.stdout.splitlines()];want=[e for _,_,e in cases]
        assert got==want,[(l,g.hex(),e.hex()) for(l,_,e),g in zip(cases,got) if g!=e]
        path=directory/f'signal-chain-receive-{size}.json'
        with path.open('w') as out:subprocess.run([command,'signal-chain-receive',str(size)],stdout=out,check=True,timeout=600)
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
    visit('TlsMpc.Signal.ChainReceive')
    files|={Path(__file__),checks,ROOT/'SignalReference/ChainReceiveExport.lean',work/'Export.lean',work/'lakefile.toml',ROOT/'scripts/check_lean_signal_proto_parse.py',ROOT/'scripts/check_lean_signal_receive.py',ROOT/'scripts/check_lean_signal_chain_send.py',ROOT/'scripts/check_lean_signal_proto_receive.py'}
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'checked_endpoints':len(names),'source_sha256':{str(p.relative_to(ROOT)):digest(p) for p in sorted(files)},'cases':rows,'full_actual_rust_receive_refinement':False,'native_mpc_executed':False,'all_runtime_values_secret':True,'public_parameters':['wire byte length'],'selected_in_order_chain_transition':True,'skipped_or_new_ratchet_selection':False,'custom_axioms':[]}
    (ROOT/'benchmarks/results/lean-signal-chain-receive-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    (ROOT/'SignalReference/chain-receive-axioms.txt').write_text(p.stdout)
    (ROOT/'SignalReference/chain-receive-proof-check.json').write_text(json.dumps({'checked_endpoints':len(names),'theorems':names,'source_sha256':report['source_sha256'],'custom_axioms':[]},indent=2)+'\n')
if __name__=='__main__':main()
