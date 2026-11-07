#!/usr/bin/env python3
"""Modulo3329 arithmetic/CBD/SHAKE-noise fixtures with independent integer reference."""
import hashlib,json,random,re,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from scripts.check_lean_signal_ratchet_step import digest
from scripts.check_lean_crypto import evaluate_lanes
from backend_adapter.boolean import load
from backend_adapter.aig import statistics

def expected(mode,eta,raw):
    if mode=='arithmetic':
        x,y=int.from_bytes(raw[:2],'little'),int.from_bytes(raw[2:],'little')
        assert x<3329 and y<3329
        return b''.join(n.to_bytes(2,'little') for n in((x+y)%3329,(x-y)%3329,x*y%3329))
    if mode=='noise':raw=hashlib.shake_256(raw).digest(64*eta)
    bits=[(byte>>i)&1 for byte in raw for i in range(8)]
    return b''.join(((sum(bits[2*eta*i:2*eta*i+eta])-sum(bits[2*eta*i+eta:2*eta*(i+1)]))%3329).to_bytes(2,'little') for i in range(256))

def main():
    work=ROOT/'SignalReference/MlKemArithmeticWork';assert(work/'Export.lean').read_bytes()==(ROOT/'SignalReference/MlKemArithmeticExport.lean').read_bytes()
    subprocess.run(['lake','build'],cwd=work,check=True)
    checks=ROOT/'SignalReference/MlKemArithmeticChecks.lean';p=subprocess.run(['lake','env','lean',str(checks)],cwd=ROOT,check=True,text=True,capture_output=True)
    names=re.findall(r'^#print axioms (\S+)',checks.read_text(),re.M);found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",p.stdout)
    assert [n for n,_ in found]==names
    for n,a in found:assert not({x.strip() for x in a.split(',') if x.strip()}-{'propext','Quot.sound','Classical.choice'}),(n,a)
    command=str(work/'.lake/build/bin/emit_mlkem_arithmetic');rng=random.Random(332932);directory=ROOT/'.deps/signal-mlkem-arithmetic-artifacts';directory.mkdir(exist_ok=True);rows=[]
    for mode,eta in [('arithmetic',2),('cbd',2),('cbd',3),('noise',2),('noise',3)]:
        if mode=='arithmetic':
            pairs=[(x,y) for x in(0,1,2,1664,3327,3328) for y in(0,1,2,1664,3327,3328)] + [(rng.randrange(3329),rng.randrange(3329)) for _ in range(1024)]
            inputs=[x.to_bytes(2,'little')+y.to_bytes(2,'little') for x,y in pairs]
        elif mode=='noise':inputs=[rng.randbytes(32)+bytes([nonce]) for nonce in(0,1,2,3,4,5,6,7,8,9,15,31,63,127,254,255)]
        else:
            if eta==2:inputs=[bytes([n])*128 for n in range(256)]
            else:
                inputs=[]
                for n in range(64):
                    bits=[(n>>i)&1 for _ in range(256) for i in range(6)]
                    inputs.append(bytes(sum(bits[8*j+i]<<i for i in range(8)) for j in range(192)))
            inputs += [rng.randbytes(64*eta) for _ in range(16)]
        outputs=[expected(mode,eta,raw) for raw in inputs]
        result=subprocess.run([command,'evaluate',mode,str(eta)],input=''.join(json.dumps(list(raw))+'\n' for raw in inputs),text=True,capture_output=True,check=True,timeout=300)
        assert [bytes(json.loads(line)) for line in result.stdout.splitlines()]==outputs,(mode,eta)
        path=directory/f'signal-mlkem-{mode}-{eta}.json'
        with path.open('w') as out:subprocess.run([command,'signal-mlkem',mode,str(eta)],stdout=out,check=True,timeout=300)
        artifact=load(path);assert evaluate_lanes(artifact,inputs)==outputs,(mode,eta)
        fixture=path.with_name(path.stem+'-fixtures.json');fixture.write_text(json.dumps([{'input':raw.hex(),'output':out.hex()} for raw,out in zip(inputs,outputs)],indent=2)+'\n')
        row={'mode':mode,'eta':eta,'fixture_lanes':len(inputs),'artifact_sha256':digest(path),'fixture_sha256':digest(fixture),'adapter_operations':statistics(artifact),'all_outputs_match':True};rows.append(row);print(json.dumps(row),flush=True)
    files=set()
    def visit(module):
        if not module.startswith('TlsMpc'):return
        p=ROOT/(module.replace('.','/')+'.lean')
        if p in files:return
        files.add(p)
        for m in re.findall(r'^import ([\w.]+)',p.read_text(),re.M):visit(m)
    visit('TlsMpc.Signal.MlKemArithmetic')
    files|={Path(__file__),checks,ROOT/'SignalReference/MlKemArithmeticExport.lean',work/'Export.lean',work/'lakefile.toml',ROOT/'scripts/check_lean_crypto.py'}
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'checked_endpoints':len(names),'source_sha256':{str(f.relative_to(ROOT)):digest(f) for f in sorted(files)},'cases':rows,'custom_axioms':[],'actual_libcrux_aeneas_refinement':False,'actual_libcrux_cbd_differential':False,'native_mpc_executed':False,'all_runtime_values_secret':True,'full_mlkem':False,'arithmetic_precondition':'input coefficients canonical0..3328; kernel-checked modular correctness','cbd_values_proved':'all input byte lists/counts for eta<=3, missing input bytes interpreted as zero; exporters enforce exact64eta length'}
    (ROOT/'benchmarks/results/lean-signal-mlkem-arithmetic-checks.json').write_text(json.dumps(report,indent=2)+'\n');(ROOT/'SignalReference/mlkem-arithmetic-axioms.txt').write_text(p.stdout)
if __name__=='__main__':main()
