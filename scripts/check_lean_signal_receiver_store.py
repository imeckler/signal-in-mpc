#!/usr/bin/env python3
"""Retained receiver-store fixtures, duplicate semantics and append/eviction transactions."""
import json,random,re,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from scripts.check_lean_signal_ratchet_step import digest
from scripts.check_lean_crypto import evaluate_lanes
from backend_adapter.boolean import load
from backend_adapter.aig import statistics

def expected(raw,op,capacity,skips):
    width=69+69*skips;auth=raw[0];key=raw[1:33];next=raw[33:33+width];old=[raw[33+(i+1)*width:33+(i+2)*width] for i in range(capacity)]
    hit=None
    for i,e in enumerate(old):
        if e[0]==255 and e[1:33]==key:hit=i;break
    if op=='lookup':return old[hit] if hit is not None else bytes(width)
    if auth!=255:return b''.join(old)
    if op=='replace' and hit is not None:old[hit]=next
    if op=='insert':old=(old[1:]+[next])[:capacity]
    return b''.join(old)

def main():
    work=ROOT/'SignalReference/ReceiverStoreWork';assert(work/'Export.lean').read_bytes()==(ROOT/'SignalReference/ReceiverStoreExport.lean').read_bytes()
    subprocess.run(['lake','build'],cwd=work,check=True)
    checks=ROOT/'SignalReference/ReceiverStoreChecks.lean';p=subprocess.run(['lake','env','lean',str(checks)],cwd=ROOT,check=True,text=True,capture_output=True)
    names=re.findall(r'^#print axioms (\S+)',checks.read_text(),re.M);found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",p.stdout)
    assert [n for n,_ in found]==names
    for n,a in found:assert not({x.strip() for x in a.split(',') if x.strip()}-{'propext','Quot.sound','Classical.choice'}),(n,a)
    command=str(work/'.lake/build/bin/emit_receiver_store');directory=ROOT/'.deps/signal-receiver-store-artifacts';directory.mkdir(exist_ok=True);rows=[];rng=random.Random(551002)
    artifacts={}
    for capacity,skips in((0,0),(1,0),(5,0),(5,2)):
        width=69+69*skips;cases=[]
        for i in range(144):
            key=rng.randbytes(32);auth=[0,1,127,254,255,255][i%6];new=b'\xff'+key+rng.randbytes(width-33);old=[]
            for j in range(capacity):
                valid=[0,1,255][(i+j)%3];identifier=key if (i+j)%4 else rng.randbytes(32)
                old.append(bytes([valid])+identifier+rng.randbytes(width-33))
            if i%7==0 and capacity:old[0]=b'\xff'+key+old[0][33:]
            if i%7==0 and capacity>1:old[-1]=b'\xff'+key+old[-1][33:]
            cases.append(bytes([auth])+key+new+b''.join(old))
        for op in('lookup','replace','insert'):
            want=[expected(raw,op,capacity,skips) for raw in cases]
            result=subprocess.run([command,'evaluate',op,str(capacity),str(skips)],input=''.join(json.dumps(list(raw))+'\n' for raw in cases),text=True,capture_output=True,check=True)
            assert [bytes(json.loads(line)) for line in result.stdout.splitlines()]==want
            path=directory/f'signal-receiver-store-{op}-{capacity}-{skips}.json'
            with path.open('w') as out:subprocess.run([command,'signal-receiver-store',op,str(capacity),str(skips)],stdout=out,check=True)
            image=load(path);assert evaluate_lanes(image,cases)==want;artifacts[(op,capacity,skips)]=image
            fixture=path.with_name(path.stem+'-fixtures.json');fixture.write_text(json.dumps([{'input':raw.hex(),'output':out.hex()} for raw,out in zip(cases,want)],indent=2)+'\n')
            rows.append({'operation':op,'capacity':capacity,'skips':skips,'fixture_lanes':len(cases),'artifact_sha256':digest(path),'fixture_sha256':digest(fixture),'adapter_operations':statistics(image),'all_outputs_match':True})
    width=207;state=bytes(5*width);transactions=[]
    for i in range(8):
        key=i.to_bytes(32,'big');entry=b'\xff'+key+bytes([i])*174;raw=b'\xff'+key+entry+state
        state=evaluate_lanes(artifacts[('insert',5,2)],[raw])[0];assert state==expected(raw,'insert',5,2)
        valid=[int.from_bytes(state[j*width+1:j*width+33],'big') for j in range(5) if state[j*width]==255]
        assert valid==list(range(max(0,i-4),i+1));transactions.append({'inserted':i,'retained':valid})
    for op,auth,keyid in(('replace',0,4),('replace',255,4),('replace',255,0)):
        key=keyid.to_bytes(32,'big');entry=b'\xff'+key+bytes([99])*174;raw=bytes([auth])+key+entry+state
        got=evaluate_lanes(artifacts[(op,5,2)],[raw])[0];assert got==expected(raw,op,5,2);state=got
    files=[Path(__file__),ROOT/'TlsMpc/Signal/ReceiverStore.lean',ROOT/'TlsMpc/Signal/SkippedKeys.lean',checks,ROOT/'SignalReference/ReceiverStoreExport.lean',work/'Export.lean',work/'lakefile.toml',ROOT/'.deps/libsignal-v0.106.1/rust/protocol/src/double_ratchet.rs',ROOT/'scripts/check_lean_crypto.py']
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'checked_endpoints':len(names),'source_sha256':{str(f.relative_to(ROOT)):digest(f) for f in files},'cases':rows,'artifact_transactions':transactions,'custom_axioms':[],'full_actual_rust_store_refinement':False,'native_mpc_executed':False,'all_runtime_values_secret':True,'initialization_invariant':'invalid prefix followed by valid oldest-to-newest entries','pinned_retention_capacity':5}
    (ROOT/'benchmarks/results/lean-signal-receiver-store-checks.json').write_text(json.dumps(report,indent=2)+'\n');(ROOT/'SignalReference/receiver-store-axioms.txt').write_text(p.stdout)
    print(json.dumps({'endpoints':len(names),'numeric_lanes':len(rows)*144,'transactions':len(transactions)+3,'cases':rows}),flush=True)
if __name__=='__main__':main()
