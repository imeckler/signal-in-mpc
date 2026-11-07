#!/usr/bin/env python3
"""Secret retained-chain selection and authenticated updates against independent Python state transitions."""
import json,random,re,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from scripts.check_lean_signal_ratchet_step import digest
from scripts.check_lean_signal_bounded_receive import fixtures as bounded_fixtures,expected as bounded_expected
from scripts.check_lean_signal_proto_parse import parse
from scripts.check_lean_crypto import evaluate_lanes
from backend_adapter.boolean import load
from backend_adapter.aig import statistics

def expected(raw,chains=5,skips=4,jump=2):
    width=69+69*skips;wire=raw[133+chains*width:];key=parse(wire)[1:33]
    old=[raw[133+i*width:133+(i+1)*width] for i in range(chains)];selected=bytes(width);hit=None
    for i,e in enumerate(old):
        if e[0]==255 and e[1:33]==key:hit=i;selected=e;break
    inner=raw[:1]+selected[1:33]+selected[33:65]+selected[65:69]+raw[1:133]+selected[69:]+wire
    opened=bounded_expected(inner,skips,jump);tail=opened[37+69*skips:]
    if hit is None or opened[0]!=255:return bytes(1)+b''.join(old)+bytes(len(tail))
    old[hit]=b'\xff'+selected[1:33]+opened[1:37]+opened[37:37+69*skips]
    return b'\xff'+b''.join(old)+tail

def fixtures():
    cases=[];rng=random.Random(777212);width=345
    for label,raw,_ in bounded_fixtures(96):
        selected=b'\xff'+raw[1:33]+raw[33:65]+raw[65:69]+raw[201:477]
        old=[b'\xff'+rng.randbytes(width-1) for _ in range(5)];old[2]=selected
        full=raw[:1]+raw[69:201]+b''.join(old)+raw[477:];cases.append((label,full,expected(full)))
    raw=cases[0][1];entries=[raw[133+i*width:133+(i+1)*width] for i in range(5)];selected=entries[2]
    for position in range(5):
        old=entries[:];old[position],old[2]=old[2],old[position]
        full=raw[:133]+b''.join(old)+raw[133+5*width:];cases.append((f'selected-position-{position}',full,expected(full)))
    bad=b'\xff'+selected[1:33]+bytes(32)+selected[65:]
    for label,old in [('bad-first-duplicate',[bad,entries[1],selected,entries[3],entries[4]]),
                      ('bad-later-duplicate',[selected,entries[1],bad,entries[3],entries[4]]),
                      ('invalid-selected',[*entries[:2],b'\x01'+selected[1:],*entries[3:]]),
                      ('empty-prefix',[bytes(width),bytes(width),selected,entries[3],entries[4]]),
                      ('all-empty',[bytes(width)]*5)]:
        full=raw[:133]+b''.join(old)+raw[133+5*width:];cases.append((label,full,expected(full)))
    return cases

def main():
    work=ROOT/'SignalReference/RetainedReceiveWork';assert(work/'Export.lean').read_bytes()==(ROOT/'SignalReference/RetainedReceiveExport.lean').read_bytes()
    subprocess.run(['lake','build'],cwd=work,check=True)
    checks=ROOT/'SignalReference/RetainedReceiveChecks.lean';p=subprocess.run(['lake','env','lean',str(checks)],cwd=ROOT,check=True,text=True,capture_output=True)
    names=re.findall(r'^#print axioms (\S+)',checks.read_text(),re.M);found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",p.stdout)
    assert [n for n,_ in found]==names
    for n,a in found:assert not({x.strip() for x in a.split(',') if x.strip()}-{'propext','Quot.sound','Classical.choice'}),(n,a)
    cases=fixtures();inputs=[raw for _,raw,_ in cases];outputs=[out for _,_,out in cases];command=str(work/'.lake/build/bin/emit_retained_receive')
    result=subprocess.run([command,'evaluate','2','5','4'],input=''.join(json.dumps(list(w))+'\n' for w in inputs),text=True,capture_output=True,check=True,timeout=600)
    got=[bytes(json.loads(line)) for line in result.stdout.splitlines()]
    assert got==outputs,[(l,g.hex(),e.hex()) for(l,_,e),g in zip(cases,got) if g!=e]
    directory=ROOT/'.deps/signal-retained-receive-artifacts';directory.mkdir(exist_ok=True);path=directory/'signal-retained-receive-2-5-4-96.json'
    with path.open('w') as out:subprocess.run([command,'signal-retained-receive','2','5','4','96'],stdout=out,check=True,timeout=600)
    artifact=load(path);assert evaluate_lanes(artifact,inputs)==outputs
    fixture=path.with_name(path.stem+'-fixtures.json');fixture.write_text(json.dumps([{'label':l,'input':w.hex(),'output':e.hex()} for l,w,e in cases],indent=2)+'\n')
    bylabel={l:raw for l,raw,_ in cases};state=None;transactions=[]
    for label in('target-9','target-7','target-7','bad-mac-target-8','target-8','target-6'):
        raw=bylabel[label]
        if state is not None:raw=raw[:133]+state+raw[1858:]
        actual=evaluate_lanes(artifact,[raw])[0];assert actual==expected(raw);state=actual[1:1726]
        transactions.append({'label':label,'accepted':actual[0]==255})
    row={'fixture_lanes':len(cases),'artifact_sha256':digest(path),'fixture_sha256':digest(fixture),'adapter_operations':statistics(artifact),'all_outputs_match':True,'wire_bytes':96,'receiver_chains':5,'skipped_slots':4,'max_jump':2,'artifact_transactions':transactions}
    files=set()
    def visit(module):
        if not module.startswith('TlsMpc'):return
        p=ROOT/(module.replace('.','/')+'.lean')
        if p in files:return
        files.add(p)
        for m in re.findall(r'^import ([\w.]+)',p.read_text(),re.M):visit(m)
    visit('TlsMpc.Signal.RetainedReceive')
    files|={Path(__file__),checks,ROOT/'SignalReference/RetainedReceiveExport.lean',work/'Export.lean',work/'lakefile.toml',ROOT/'scripts/check_lean_signal_bounded_receive.py',ROOT/'scripts/check_lean_signal_proto_receive.py',ROOT/'scripts/check_lean_signal_proto_parse.py',ROOT/'scripts/check_lean_signal_receive.py',ROOT/'scripts/check_lean_crypto.py'}
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'checked_endpoints':len(names),'source_sha256':{str(f.relative_to(ROOT)):digest(f) for f in sorted(files)},'cases':[row],'custom_axioms':[],'full_actual_rust_receive_refinement':False,'native_mpc_executed':False,'all_runtime_values_secret':True,'remaining':['new-versus-retained session branch composition','SPQR evolution','legacy expanded key records','persistent atomic commit']}
    (ROOT/'benchmarks/results/lean-signal-retained-receive-checks.json').write_text(json.dumps(report,indent=2)+'\n');(ROOT/'SignalReference/retained-receive-axioms.txt').write_text(p.stdout);print(json.dumps(row),flush=True)
if __name__=='__main__':main()
