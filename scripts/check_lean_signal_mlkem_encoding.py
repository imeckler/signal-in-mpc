#!/usr/bin/env python3
"""Exhaustive scalar domains and numeric packed ML-KEM encoding/compression."""
import json,random,re,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from scripts.check_lean_signal_ratchet_step import digest
from scripts.check_lean_crypto import evaluate_lanes
from backend_adapter.boolean import load
from backend_adapter.aig import statistics

def words(poly):return b''.join(x.to_bytes(2,'little') for x in poly)
def pack(poly,d):return sum(x<<(d*i) for i,x in enumerate(poly)).to_bytes(32*d,'little')
def unpack(raw,d):
    n=int.from_bytes(raw,'little');return [(n>>(d*i))%2**d for i in range(256)]
def main():
    work=ROOT/'SignalReference/MlKemEncodingWork';assert(work/'Export.lean').read_bytes()==(ROOT/'SignalReference/MlKemEncodingExport.lean').read_bytes()
    subprocess.run(['lake','build'],cwd=work,check=True)
    checks=ROOT/'SignalReference/MlKemEncodingChecks.lean';p=subprocess.run(['lake','env','lean',str(checks)],cwd=ROOT,check=True,text=True,capture_output=True)
    names=re.findall(r'^#print axioms (\S+)',checks.read_text(),re.M);found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",p.stdout)
    assert [n for n,_ in found]==names
    for n,a in found:assert not({x.strip() for x in a.split(',') if x.strip()}-{'propext','Quot.sound','Classical.choice'}),(n,a)
    command=str(work/'.lake/build/bin/emit_mlkem_encoding');rng=random.Random(332912);directory=ROOT/'.deps/signal-mlkem-encoding-artifacts';directory.mkdir(exist_ok=True);rows=[]
    for d in (1,4,5,10,11,12):
      for mode in ('encode','decode','compress','decompress'):
        if d==12 and mode in ('compress','decompress'):continue
        modulus=3329 if mode=='compress' else 2**d
        polys=[[(start+i)%modulus for i in range(256)] for start in range(0,modulus,256)]
        polys += [[0]*256,[modulus-1]*256,*[[rng.randrange(modulus) for _ in range(256)] for _ in range(2)]]
        inputs=[words(a) if mode in ('encode','compress') else pack(a,d) for a in polys]
        if mode=='encode':outputs=[pack(a,d) for a in polys]
        elif mode=='decode':outputs=[words(a) for a in polys]
        elif mode=='compress':outputs=[pack([((x*2**d+1664)//3329)%2**d for x in a],d) for a in polys]
        else:outputs=[words([(x*3329+2**(d-1))//2**d for x in a]) for a in polys]
        result=subprocess.run([command,'evaluate',mode,str(d)],input=''.join(json.dumps(list(raw))+'\n' for raw in inputs),text=True,capture_output=True,check=True,timeout=600)
        assert [bytes(json.loads(line)) for line in result.stdout.splitlines()]==outputs,(mode,d)
        path=directory/f'signal-mlkem-encoding-{mode}-{d}.json'
        with path.open('w') as out:subprocess.run([command,'signal-mlkem-encoding',mode,str(d)],stdout=out,check=True,timeout=600)
        image=load(path);assert evaluate_lanes(image,inputs)==outputs,(mode,d)
        fixture=path.with_name(path.stem+'-fixtures.json');fixture.write_text(json.dumps([{'input':raw.hex(),'output':out.hex()} for raw,out in zip(inputs,outputs)],indent=2)+'\n')
        row={'mode':mode,'width':d,'fixture_lanes':len(inputs),'exhaustive_scalar_domain':modulus,'artifact_sha256':digest(path),'fixture_sha256':digest(fixture),'adapter_operations':statistics(image),'all_outputs_match':True};rows.append(row);print(json.dumps(row),flush=True)
        del image
    files=set()
    def visit(module):
        if not module.startswith('TlsMpc'):return
        p=ROOT/(module.replace('.','/')+'.lean')
        if p in files:return
        files.add(p)
        for m in re.findall(r'^import ([\w.]+)',p.read_text(),re.M):visit(m)
    visit('TlsMpc.Signal.MlKemEncoding')
    files|={Path(__file__),checks,ROOT/'SignalReference/MlKemEncodingExport.lean',work/'Export.lean',work/'lakefile.toml',ROOT/'scripts/check_lean_crypto.py',ROOT/'.deps/libsignal-vendor/libcrux-ml-kem-0.0.10/src/serialize.rs'}
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'checked_endpoints':len(names),'source_sha256':{str(f.relative_to(ROOT)):digest(f) for f in sorted(files)},'cases':rows,'fixture_lanes':sum(r['fixture_lanes'] for r in rows),'custom_axioms':[],'actual_libcrux_aeneas_refinement':False,'actual_libcrux_differential':False,'native_mpc_executed':False,'all_runtime_values_secret':True,'full_mlkem':False,'input_precondition':'256 coefficients; compression requires canonical0..3328; encoding requires0..2^width-1; raw12-bit decoding does not validate public-key canonicality'}
    (ROOT/'benchmarks/results/lean-signal-mlkem-encoding-checks.json').write_text(json.dumps(report,indent=2)+'\n');(ROOT/'SignalReference/mlkem-encoding-axioms.txt').write_text(p.stdout)
if __name__=='__main__':main()
