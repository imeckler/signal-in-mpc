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
def expected(raw,count=4,jump=2):
    p=raw[0];ratchet,chain,counter=raw[1:33],raw[33:65],raw[65:69];current=int.from_bytes(counter,'big')
    pq,sender,receiver,address=raw[69:101],raw[101:133],raw[133:165],raw[165:201]
    old=raw[201:201+69*count];wire=raw[201+69*count:];parsed=parse(wire);key=parsed[1:33];target=int.from_bytes(parsed[33:37],'big')
    slots=[old[i*69:(i+1)*69] for i in range(count)];nextslots=slots[:];nextchain=chain;nextcounter=counter;seed=bytes(32);found=False
    if key==ratchet and current<=target:
        if target<2**32-1 and target-current<=jump:
            found=True
            for c in range(current,target+1):
                seed=hmac.digest(nextchain,b'\x01','sha256');nextchain=hmac.digest(nextchain,b'\x02','sha256')
                if c<target:nextslots=([b'\xff'+ratchet+c.to_bytes(4,'big')+seed]+nextslots)[:count]
            nextcounter=(target+1).to_bytes(4,'big')
    else:
        for i,slot in enumerate(slots):
            if slot[0]==255 and slot[1:33]==key and slot[33:37]==parsed[33:37]:
                found=True;seed=slot[37:];nextslots=slots[:i]+slots[i+1:]+[bytes(69)];break
    ck,mk,iv=material(seed,pq if p==1 else bytes(32));opened=proto_expected(ck+iv+mk+sender+receiver+address+wire)
    if found and opened[0]==255 and p in(0,1):return b'\xff'+nextchain+nextcounter+b''.join(nextslots)+opened[1:]
    return b'\x00'+chain+counter+old+bytes(len(opened)-1)

def fixtures(size):
    ratchet=sample('bounded-ratchet',32);chain=sample('bounded-chain',32);pq=sample('bounded-pq',32)
    sender=sample('bounded-sender',32);receiver=sample('bounded-receiver',32);oldkey=sample('old-ratchet',32)
    seed6=sample('oldseed6',32);seed5=sample('oldseed5',32)
    address=b'\x00'+sample('sender',16)+b'\x01\x01'+sample('receiver',16)+b'\x7f'
    initial=[b'\xff'+ratchet+(6).to_bytes(4,'big')+seed6,b'\xff'+oldkey+(5).to_bytes(4,'big')+seed5,bytes(69),bytes(69)]
    cases=[]
    def add(label,target=7,current=7,key=ratchet,slots=None,present=0,tamper=None,extra=b'',padded=None):
        if slots is None:slots=initial
        if key==ratchet and target>=current and target-current<8:
            ch=chain
            for _ in range(target-current):ch=hmac.digest(ch,b'\x02','sha256')
            seed=hmac.digest(ch,b'\x01','sha256')
        else:seed=seed6 if key==ratchet and target==6 else seed5
        ck,mk,iv=material(seed,pq if present==1 else bytes(32));ct=cbc(ck,iv,padded if padded is not None else b'hello'+b'\x0b'*11)
        body=field(1,b'\x05'+key)+scalar(2,target)+field(4,ct)+extra;gap=size-9-len(body)
        if gap<2:return
        body+=field(15,bytes(gap-2));assert len(body)+9==size
        content=b'\x44'+body;wire=content+mac(mk,sender,receiver,content)
        raw=bytes([present])+ratchet+chain+current.to_bytes(4,'big')+pq+sender+receiver+address+b''.join(slots)+wire
        if tamper is not None:raw=bytearray(raw);raw[tamper]^=1;raw=bytes(raw)
        cases.append((label,raw,expected(raw)))
    for target in(7,8,9,10,6,5):add(f'target-{target}',target=target)
    add('old-ratchet',target=5,key=oldkey);add('unknown-ratchet',target=5,key=bytes(32))
    for target in(7,8,9,6):add(f'bad-mac-target-{target}',target=target,tamper=-1)
    for p in(0,1,2,255):add(f'PQpresence-{p}',target=9,present=p)
    for current,target in((2**32-2,2**32-2),(2**32-2,2**32-1),(2**32-1,0),(0,0),(0,2),(0,3)):
        add(f'boundary-{current}-{target}',current=current,target=target)
    duplicate=initial[0][:37]+bytes(32);add('duplicate-bad-first',target=6,slots=[duplicate,initial[0],initial[1],bytes(69)])
    add('malformed-valid',target=6,slots=[b'\x01'+initial[0][1:],*initial[1:]])
    # A stored key does not bypass the bounded-future policy on the current chain.
    ch=chain
    for _ in range(3):ch=hmac.digest(ch,b'\x02','sha256')
    add('future-cache-no-bypass',target=10,slots=[b'\xff'+ratchet+(10).to_bytes(4,'big')+hmac.digest(ch,b'\x01','sha256'),*initial[1:]])
    add('bad-padding',target=9,padded=bytes(16));add('wrong-counter-last',extra=scalar(2,9))
    return cases

def main():
    cli=argparse.ArgumentParser();cli.add_argument('--compile-backend',action='store_true');opt=cli.parse_args()
    work=ROOT/'SignalReference/BoundedReceiveWork';assert(work/'Export.lean').read_bytes()==(ROOT/'SignalReference/BoundedReceiveExport.lean').read_bytes()
    subprocess.run(['lake','build'],cwd=work,check=True)
    checks=ROOT/'SignalReference/BoundedReceiveChecks.lean';p=subprocess.run(['lake','env','lean',str(checks)],cwd=ROOT,check=True,text=True,capture_output=True)
    names=re.findall(r'^#print axioms (\S+)',checks.read_text(),re.M);found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",p.stdout)
    assert [n for n,_ in found]==names
    for n,a in found:assert not({x.strip() for x in a.split(',') if x.strip()}-{'propext','Quot.sound','Classical.choice'}),(n,a)
    command=str(work/'.lake/build/bin/emit_bounded_receive');directory=ROOT/'.deps/signal-bounded-receive-artifacts';directory.mkdir(exist_ok=True);rows=[]
    for size in(96,):
        cases=fixtures(size);result=subprocess.run([command,'evaluate','2','4'],input=''.join(json.dumps(list(w))+'\n' for _,w,_ in cases),text=True,capture_output=True,check=True,timeout=600)
        got=[bytes(json.loads(x)) for x in result.stdout.splitlines()];want=[e for _,_,e in cases]
        assert got==want,[(l,g.hex(),e.hex()) for(l,_,e),g in zip(cases,got) if g!=e]
        path=directory/f'signal-bounded-receive-2-4-{size}.json'
        with path.open('w') as out:subprocess.run([command,'signal-bounded-receive','2','4',str(size)],stdout=out,check=True,timeout=600)
        artifact=load(path);got=evaluate_lanes(artifact,[w for _,w,_ in cases]);assert got==want,[(l,g.hex(),e.hex()) for(l,_,e),g in zip(cases,got) if g!=e]
        fixture=path.with_name(path.stem+'-fixtures.json');fixture.write_text(json.dumps([{'label':l,'input':w.hex(),'output':e.hex()} for l,w,e in cases],indent=2)+'\n')
        by_label={l:(raw,out) for l,raw,out in cases}
        state=None;transactions=[]
        for label in ('target-9','target-7','target-7','bad-mac-target-8','target-8','target-6','old-ratchet'):
            raw=by_label[label][0]
            if state is not None:
                key,counter,store=state
                raw=raw[:33]+key+counter+raw[69:201]+store+raw[477:]
            got_one=evaluate_lanes(artifact,[raw])[0];assert got_one==expected(raw),label
            state=(got_one[1:33],got_one[33:37],got_one[37:313])
            transactions.append({'label':label,'accepted':got_one[0]==255,'next_counter':int.from_bytes(got_one[33:37],'big')})
        row={'wire_bytes':size,'fixture_lanes':len(cases),'artifact_sha256':digest(path),'fixture_sha256':digest(fixture),'adapter_operations':statistics(artifact),'all_outputs_match':True,'artifact_transactions':transactions}
        if opt.compile_backend:row['mpc_compilations']=[compile_and_check(path,[w for _,w,_ in cases],[e for _,_,e in cases],batch) for batch in(1,16)]
        rows.append(row);print(json.dumps(row),flush=True)
    files=set()
    def visit(module):
        if not module.startswith('TlsMpc'):return
        p=ROOT/(module.replace('.','/')+'.lean')
        if p in files:return
        files.add(p)
        for m in re.findall(r'^import ([\w.]+)',p.read_text(),re.M):visit(m)
    visit('TlsMpc.Signal.BoundedReceive')
    files|={Path(__file__),checks,ROOT/'SignalReference/BoundedReceiveExport.lean',work/'Export.lean',work/'lakefile.toml',ROOT/'scripts/check_lean_signal_proto_parse.py',ROOT/'scripts/check_lean_signal_receive.py',ROOT/'scripts/check_lean_signal_proto_receive.py'}
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'checked_endpoints':len(names),'source_sha256':{str(p.relative_to(ROOT)):digest(p) for p in sorted(files)},'cases':rows,'full_actual_rust_receive_refinement':False,'native_mpc_executed':False,'all_runtime_values_secret':True,'public_parameters':['wire byte length'],'bounded_forward_and_skipped_transaction':True,'max_jump':2,'capacity':4,'legacy_expanded_key_records':False,'custom_axioms':[]}
    (ROOT/'benchmarks/results/lean-signal-bounded-receive-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    (ROOT/'SignalReference/bounded-receive-axioms.txt').write_text(p.stdout)
    (ROOT/'SignalReference/bounded-receive-proof-check.json').write_text(json.dumps({'checked_endpoints':len(names),'theorems':names,'source_sha256':report['source_sha256'],'custom_axioms':[]},indent=2)+'\n')
if __name__=='__main__':main()
