#!/usr/bin/env python3
"""Combined new-DH/retained-chain transaction with secret branch selection."""
import json,random,re,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from scripts.check_lean_signal_ratchet_step import digest
from scripts.check_lean_signal_new_ratchet_receive import fixtures as new_fixtures,expected as new_expected
from scripts.check_lean_signal_bounded_receive import fixtures as bounded_fixtures
from scripts.check_lean_signal_retained_receive import expected as retained_expected
from scripts.check_lean_signal_proto_parse import parse
from scripts.check_lean_crypto import evaluate_lanes
from backend_adapter.boolean import load
from backend_adapter.aig import statistics

def expected(raw,chains=5,skips=2,jump=2):
    width=69+69*skips;store=raw[429:429+chains*width];wire=raw[429+chains*width:];key=parse(wire)[1:33]
    old=[store[i*width:(i+1)*width] for i in range(chains)]
    if any(e[0]==255 and e[1:33]==key for e in old):
        opened=retained_expected(raw[:1]+raw[297:429]+store+wire,chains,skips,jump)
        return opened[:1]+raw[1:137]+opened[1:]
    opened=new_expected(raw[:429]+wire,skips,jump)
    if opened[0]==255:
        entry=b'\xff'+opened[137:205]+opened[205:205+69*skips]
        old=(old[1:]+[entry])[:chains]
    return opened[:137]+b''.join(old)+opened[205+69*skips:]

def fixtures():
    cases=[];rng=random.Random(555200);width=207
    for label,raw,_ in new_fixtures():
        for full in (False,True) if label=='counter-0' else (False,):
            store=b''.join(b'\xff'+rng.randbytes(width-1) for _ in range(5)) if full else bytes(5*width)
            whole=raw[:429]+store+raw[429:];cases.append(('new-'+label+('-full' if full else ''),whole,expected(whole)))
    base=new_fixtures()[0][1]
    for label,raw,_ in bounded_fixtures(96):
        entry=b'\xff'+raw[1:33]+raw[33:65]+raw[65:69]+raw[201:339]
        store=[bytes(width),bytes(width),entry,b'\xff'+rng.randbytes(width-1),b'\xff'+rng.randbytes(width-1)]
        whole=raw[:1]+base[1:265]+raw[1:33]+raw[69:201]+b''.join(store)+raw[477:]
        cases.append(('retained-'+label,whole,expected(whole)))
    return cases

def main():
    work=ROOT/'SignalReference/SessionReceiveWork';assert(work/'Export.lean').read_bytes()==(ROOT/'SignalReference/SessionReceiveExport.lean').read_bytes()
    subprocess.run(['lake','build'],cwd=work,check=True)
    checks=ROOT/'SignalReference/SessionReceiveChecks.lean';p=subprocess.run(['lake','env','lean',str(checks)],cwd=ROOT,check=True,text=True,capture_output=True)
    names=re.findall(r'^#print axioms (\S+)',checks.read_text(),re.M);found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",p.stdout)
    assert [n for n,_ in found]==names
    for n,a in found:assert not({x.strip() for x in a.split(',') if x.strip()}-{'propext','Quot.sound','Classical.choice'}),(n,a)
    cases=fixtures();inputs=[raw for _,raw,_ in cases];outputs=[out for _,_,out in cases];command=str(work/'.lake/build/bin/emit_session_receive')
    result=subprocess.run([command,'evaluate','2','5','2'],input=''.join(json.dumps(list(w))+'\n' for w in inputs),text=True,capture_output=True,check=True,timeout=600)
    got=[bytes(json.loads(line)) for line in result.stdout.splitlines()]
    assert got==outputs,[(l,g.hex(),e.hex()) for(l,_,e),g in zip(cases,got) if g!=e]
    directory=ROOT/'.deps/signal-session-receive-artifacts';directory.mkdir(exist_ok=True);path=directory/'signal-session-receive-2-5-2-96.json'
    with path.open('w') as out:subprocess.run([command,'signal-session-receive','2','5','2','96'],stdout=out,check=True,timeout=600)
    artifact=load(path);assert evaluate_lanes(artifact,inputs)==outputs
    fixture=path.with_name(path.stem+'-fixtures.json');fixture.write_text(json.dumps([{'label':l,'input':w.hex(),'output':e.hex()} for l,w,e in cases],indent=2)+'\n')
    bylabel={l:raw for l,raw,_ in cases};state=None;transactions=[]
    for label in('new-counter-0','new-counter-2','new-counter-1','new-counter-1','new-bad-mac-0'):
        raw=bylabel[label]
        if state is not None:raw=raw[:1]+state[:136]+raw[137:429]+state[136:]+raw[1464:]
        actual=evaluate_lanes(artifact,[raw])[0];assert actual==expected(raw);state=actual[1:1172]
        transactions.append({'label':label,'accepted':actual[0]==255,'sender_index':int.from_bytes(actual[129:133],'big'),'previous_counter':int.from_bytes(actual[133:137],'big')})
    row={'fixture_lanes':len(cases),'artifact_sha256':digest(path),'fixture_sha256':digest(fixture),'adapter_operations':statistics(artifact),'all_outputs_match':True,'wire_bytes':96,'receiver_chains':5,'skipped_slots':2,'max_jump':2,'artifact_transactions':transactions}
    files=set()
    def visit(module):
        if not module.startswith('TlsMpc'):return
        p=ROOT/(module.replace('.','/')+'.lean')
        if p in files:return
        files.add(p)
        for m in re.findall(r'^import ([\w.]+)',p.read_text(),re.M):visit(m)
    visit('TlsMpc.Signal.SessionReceive')
    files|={Path(__file__),checks,ROOT/'SignalReference/SessionReceiveExport.lean',work/'Export.lean',work/'lakefile.toml',ROOT/'scripts/check_lean_signal_retained_receive.py',ROOT/'scripts/check_lean_signal_new_ratchet_receive.py',ROOT/'scripts/check_lean_signal_ratchet_step.py',ROOT/'scripts/check_lean_signal_bounded_receive.py',ROOT/'scripts/check_lean_signal_proto_receive.py',ROOT/'scripts/check_lean_signal_proto_parse.py',ROOT/'scripts/check_lean_signal_receive.py',ROOT/'scripts/check_lean_crypto.py'}
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'checked_endpoints':len(names),'source_sha256':{str(f.relative_to(ROOT)):digest(f) for f in sorted(files)},'cases':[row],'custom_axioms':[],'full_actual_rust_session_refinement':False,'native_mpc_executed':False,'all_runtime_values_secret':True,'remaining':['SPQR evolution and message-key production','legacy expanded key records','persistent atomic commit/refresh/erasure','actual RustCrypto and whole parser/session refinement']}
    (ROOT/'benchmarks/results/lean-signal-session-receive-checks.json').write_text(json.dumps(report,indent=2)+'\n');(ROOT/'SignalReference/session-receive-axioms.txt').write_text(p.stdout);print(json.dumps(row),flush=True)
if __name__=='__main__':main()
