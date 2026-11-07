#!/usr/bin/env python3
"""Bounded secret rejection/compaction versus list filtering and hashlib XOF."""
import hashlib,json,random,re,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from scripts.check_lean_signal_ratchet_step import digest
from scripts.check_lean_crypto import evaluate_lanes
from backend_adapter.boolean import load
from backend_adapter.aig import statistics

def pack(values):return sum(x<<(12*i) for i,x in enumerate(values)).to_bytes(3*len(values)//2,'little')
def reference(raw,count):
    n=int.from_bytes(raw,'little');values=[(n>>(12*i))%4096 for i in range(2*len(raw)//3)]
    accepted=[x for x in values if x<3329][:count]
    return bytes([255 if len(accepted)==count else 0])+ (b''.join(x.to_bytes(2,'little') for x in accepted) if len(accepted)==count else bytes(2*count))
def main():
    work=ROOT/'SignalReference/MlKemSampleWork';assert(work/'Export.lean').read_bytes()==(ROOT/'SignalReference/MlKemSampleExport.lean').read_bytes()
    subprocess.run(['lake','build'],cwd=work,check=True)
    checks=ROOT/'SignalReference/MlKemSampleChecks.lean';p=subprocess.run(['lake','env','lean',str(checks)],cwd=ROOT,check=True,text=True,capture_output=True)
    names=re.findall(r'^#print axioms (\S+)',checks.read_text(),re.M);found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",p.stdout)
    assert [n for n,_ in found]==names
    for n,a in found:assert not({x.strip() for x in a.split(',') if x.strip()}-{'propext','Quot.sound','Classical.choice'}),(n,a)
    command=str(work/'.lake/build/bin/emit_mlkem_sample');rng=random.Random(2563329);directory=ROOT/'.deps/signal-mlkem-sample-artifacts';directory.mkdir(exist_ok=True);rows=[]
    for mode,count,pairs in [('sample',0,0),('sample',1,1),('sample',256,168),('sample',256,224),('matrix',256,168),('matrix',256,224)]:
        if pairs==0:inputs=[b'']
        elif count==1:inputs=[pack([x,4095]) for x in range(4096)]+[pack([4095,x]) for x in (0,1,3328,3329,4095)]
        elif mode=='sample':
            n=2*pairs
            values=[[0]*n,[4095]*n,[3328]*n,[3329]*n,list(range(255))+[4095]*(n-255),list(range(256))+[4095]*(n-256),[4095]*(n-256)+list(range(256)),*[([4095,0,3329,3328]*(n//4))[:n]],*[[rng.randrange(4096) for _ in range(n)] for _ in range(8)]]
            inputs=[pack(v) for v in values]
        else:
            inputs=[bytes(32)+bytes([i,j]) for i in range(4) for j in range(4)]+[bytes([255])*34]
            if pairs==168:
                # Include an XOF prefix that really exhausts this fixed budget.
                for i in range(10000):
                    raw=i.to_bytes(32,'little')+bytes(2)
                    if reference(hashlib.shake_128(raw).digest(3*pairs),count)[0]==0:inputs.append(raw);break
                else:raise AssertionError('missing exhaustion fixture')
        outputs=[reference(raw if mode=='sample' else hashlib.shake_128(raw).digest(3*pairs),count) for raw in inputs]
        args=[mode,str(count),str(pairs)]
        result=subprocess.run([command,'evaluate',*args],input=''.join(json.dumps(list(raw))+'\n' for raw in inputs),text=True,capture_output=True,check=True,timeout=600)
        assert [bytes(json.loads(line)) for line in result.stdout.splitlines()]==outputs,args
        path=directory/f'signal-mlkem-{mode}-{count}-{pairs}.json'
        with path.open('w') as out:subprocess.run([command,'signal-mlkem-sample',*args],stdout=out,check=True,timeout=600)
        image=load(path);assert evaluate_lanes(image,inputs)==outputs,args
        fixture=path.with_name(path.stem+'-fixtures.json');fixture.write_text(json.dumps([{'input':raw.hex(),'output':out.hex()} for raw,out in zip(inputs,outputs)],indent=2)+'\n')
        row={'mode':mode,'count':count,'pairs':pairs,'fixture_lanes':len(inputs),'accepted_lanes':sum(x[0]==255 for x in outputs),'aborted_lanes':sum(x[0]==0 for x in outputs),'artifact_sha256':digest(path),'fixture_sha256':digest(fixture),'adapter_operations':statistics(image),'all_outputs_match':True};rows.append(row);print(json.dumps(row),flush=True);del image
    files=set()
    def visit(module):
        if not module.startswith('TlsMpc'):return
        p=ROOT/(module.replace('.','/')+'.lean')
        if p in files:return
        files.add(p)
        for m in re.findall(r'^import ([\w.]+)',p.read_text(),re.M):visit(m)
    visit('TlsMpc.Signal.MlKemSample')
    files|={Path(__file__),checks,ROOT/'SignalReference/MlKemSampleExport.lean',work/'Export.lean',work/'lakefile.toml',ROOT/'scripts/check_lean_crypto.py',ROOT/'.deps/libsignal-vendor/libcrux-ml-kem-0.0.10/src/matrix.rs'}
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'checked_endpoints':len(names),'source_sha256':{str(f.relative_to(ROOT)):digest(f) for f in sorted(files)},'cases':rows,'fixture_lanes':sum(r['fixture_lanes'] for r in rows),'custom_axioms':[],'actual_libcrux_aeneas_refinement':False,'actual_libcrux_differential':False,'native_mpc_executed':False,'all_runtime_values_secret':True,'full_mlkem':False,'bounded_abort':'secret status0 and zero coefficients if prefix has fewer than count candidates below3329; status255 otherwise; no retry or outcome revelation','matrix_input':'seed32 || two index bytes; transpose/orientation belongs to caller'}
    (ROOT/'benchmarks/results/lean-signal-mlkem-sample-checks.json').write_text(json.dumps(report,indent=2)+'\n');(ROOT/'SignalReference/mlkem-sample-axioms.txt').write_text(p.stdout)
if __name__=='__main__':main()
