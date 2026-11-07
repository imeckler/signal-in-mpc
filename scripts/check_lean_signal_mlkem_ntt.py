#!/usr/bin/env python3
"""ML-KEM transforms versus direct polynomial evaluation/interpolation; no mirrored butterfly reference."""
import json,random,re,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from scripts.check_lean_signal_ratchet_step import digest
from scripts.check_lean_crypto import evaluate_lanes
from backend_adapter.boolean import load
from backend_adapter.aig import statistics
Q=3329
ROOTS=[pow(17,2*int(f'{i:07b}'[::-1],2)+1,Q) for i in range(128)]

def wire(poly):return b''.join(x.to_bytes(2,'little') for x in poly)
def words(raw):return [int.from_bytes(raw[i:i+2],'little') for i in range(0,len(raw),2)]
def forward(poly):
    out=[]
    for gamma in ROOTS:
        even=odd=0;power=1
        for k in range(128):
            even=(even+poly[2*k]*power)%Q;odd=(odd+poly[2*k+1]*power)%Q;power=power*gamma%Q
        out += [even,odd]
    return out

def inverse(poly):
    out=[0]*256
    for i,gamma in enumerate(ROOTS):
        step=pow(gamma,-1,Q);power=1
        for k in range(128):
            out[2*k]=(out[2*k]+poly[2*i]*power)%Q;out[2*k+1]=(out[2*k+1]+poly[2*i+1]*power)%Q;power=power*step%Q
    return [x*pow(128,-1,Q)%Q for x in out]
def multiply(a,b):
    out=[]
    for i,gamma in enumerate(ROOTS):
        x,y=a[2*i:2*i+2];u,v=b[2*i:2*i+2];out += [(x*u+gamma*y*v)%Q,(x*v+y*u)%Q]
    return out

def negacyclic(a,b):
    out=[0]*256
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[(i+j)%256]=(out[(i+j)%256]+(1 if i+j<256 else -1)*x*y)%Q
    return out

def main():
    work=ROOT/'SignalReference/MlKemNttWork';assert(work/'Export.lean').read_bytes()==(ROOT/'SignalReference/MlKemNttExport.lean').read_bytes()
    subprocess.run(['lake','build'],cwd=work,check=True)
    checks=ROOT/'SignalReference/MlKemNttChecks.lean';p=subprocess.run(['lake','env','lean',str(checks)],cwd=ROOT,check=True,text=True,capture_output=True)
    names=re.findall(r'^#print axioms (\S+)',checks.read_text(),re.M);found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",p.stdout)
    assert [n for n,_ in found]==names
    for n,a in found:assert not({x.strip() for x in a.split(',') if x.strip()}-{'propext','Quot.sound','Classical.choice'}),(n,a)
    command=str(work/'.lake/build/bin/emit_mlkem_ntt');rng=random.Random(171283329);directory=ROOT/'.deps/signal-mlkem-ntt-artifacts';directory.mkdir(exist_ok=True);rows=[];images={}
    polys=[[0]*256,[1]*256,[3328]*256,list(range(256)),*[([0]*i+[1]+[0]*(255-i)) for i in(0,1,2,127,128,254,255)],*[[rng.randrange(Q) for _ in range(256)] for _ in range(5)]]
    for poly in polys:assert inverse(forward(poly))==poly
    for mode in ('forward','inverse','multiply'):
        if mode=='multiply':
            inputs=[wire(a)+wire(b) for a,b in zip(polys,polys[::-1])];outputs=[wire(multiply(a,b)) for a,b in zip(polys,polys[::-1])]
        else:inputs=[wire(p) for p in polys];outputs=[wire((forward if mode=='forward' else inverse)(p)) for p in polys]
        result=subprocess.run([command,'evaluate',mode],input=''.join(json.dumps(list(raw))+'\n' for raw in inputs),text=True,capture_output=True,check=True,timeout=600)
        assert [bytes(json.loads(line)) for line in result.stdout.splitlines()]==outputs,mode
        path=directory/f'signal-mlkem-ntt-{mode}.json'
        with path.open('w') as out:subprocess.run([command,'signal-mlkem-ntt',mode],stdout=out,check=True,timeout=600)
        image=load(path);assert evaluate_lanes(image,inputs)==outputs,mode;images[mode]=image
        fixture=path.with_name(path.stem+'-fixtures.json');fixture.write_text(json.dumps([{'input':raw.hex(),'output':out.hex()} for raw,out in zip(inputs,outputs)],indent=2)+'\n')
        row={'mode':mode,'fixture_lanes':len(inputs),'artifact_sha256':digest(path),'fixture_sha256':digest(fixture),'adapter_operations':statistics(image),'all_outputs_match':True};rows.append(row);print(json.dumps(row),flush=True)
    a,b=polys[-1],polys[-2]
    transformed=evaluate_lanes(images['forward'],[wire(a),wire(b)])
    product=evaluate_lanes(images['multiply'],[transformed[0]+transformed[1]])[0]
    actual=evaluate_lanes(images['inverse'],[product])[0]
    assert actual==wire(negacyclic(a,b))
    files=set()
    def visit(module):
        if not module.startswith('TlsMpc'):return
        p=ROOT/(module.replace('.','/')+'.lean')
        if p in files:return
        files.add(p)
        for m in re.findall(r'^import ([\w.]+)',p.read_text(),re.M):visit(m)
    visit('TlsMpc.Signal.MlKemNtt')
    files|={Path(__file__),checks,ROOT/'SignalReference/MlKemNttExport.lean',work/'Export.lean',work/'lakefile.toml',ROOT/'scripts/check_lean_crypto.py',ROOT/'.deps/libsignal-vendor/libcrux-ml-kem-0.0.10/src/ntt.rs',ROOT/'.deps/libsignal-vendor/libcrux-ml-kem-0.0.10/src/invert_ntt.rs'}
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'checked_endpoints':len(names),'source_sha256':{str(f.relative_to(ROOT)):digest(f) for f in sorted(files)},'cases':rows,'numeric_negacyclic_convolution_pipeline':True,'custom_axioms':[],'actual_libcrux_aeneas_refinement':False,'actual_libcrux_ntt_differential':False,'native_mpc_executed':False,'all_runtime_values_secret':True,'full_mlkem':False,'input_precondition':'256 canonical coefficients0..3328 per input polynomial','reference':'independent direct evaluation/interpolation, then full negacyclic schoolbook multiplication'}
    (ROOT/'benchmarks/results/lean-signal-mlkem-ntt-checks.json').write_text(json.dumps(report,indent=2)+'\n');(ROOT/'SignalReference/mlkem-ntt-axioms.txt').write_text(p.stdout)
if __name__=='__main__':main()
