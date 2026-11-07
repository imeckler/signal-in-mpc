#!/usr/bin/env python3
"""Exhaustive secret type/status byte checks for Signal KEM framing."""
import json,re,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from scripts.check_lean_signal_ratchet_step import digest
from scripts.check_lean_crypto import evaluate_lanes
from backend_adapter.boolean import load
from backend_adapter.aig import statistics

def main():
    work=ROOT/'SignalReference/KemWireWork';subprocess.run(['lake','build'],cwd=work,check=True)
    checks=ROOT/'SignalReference/KemWireChecks.lean';p=subprocess.run(['lake','env','lean',str(checks)],cwd=ROOT,check=True,text=True,capture_output=True)
    names=re.findall(r'^#print axioms (\S+)',checks.read_text(),re.M);found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",p.stdout)
    assert [n for n,_ in found]==names
    for n,a in found:assert not({x.strip() for x in a.split(',') if x.strip()}-{'propext','Quot.sound','Classical.choice'}),(n,a)
    command=str(work/'.lake/build/bin/emit_kem_wire');directory=ROOT/'.deps/signal-kem-wire-artifacts';directory.mkdir(exist_ok=True);rows=[]
    for variant,rank,tag in [('kyber768',3,7),('kyber1024',4,8),('mlkem1024',4,10)]:
      sksize=768*rank+96;pksize=384*rank+32;ctsize=1088 if rank==3 else 1568
      for mode in ('keygen','encapsulate','decapsulate'):
        size=sksize+pksize if mode=='keygen' else ctsize+32 if mode=='encapsulate' else 32
        payload=bytes(i%251 for i in range(size));headers=[bytes([tag,tag,status]) for status in range(256)]
        if mode!='keygen':headers +=[bytes([x,tag,255]) for x in range(256)]
        if mode=='decapsulate':headers +=[bytes([tag,x,255]) for x in range(256)]
        inputs=[h+payload for h in headers];outputs=[]
        framed=bytes([tag])+payload[:sksize]+bytes([tag])+payload[sksize:] if mode=='keygen' else bytes([tag])+payload if mode=='encapsulate' else payload
        for h in headers:
          valid=h[2]==255 and (mode=='keygen' or h[0]==tag) and (mode!='decapsulate' or h[1]==tag)
          outputs.append(bytes([255 if valid else 0])+(framed if valid else bytes(len(framed))))
        result=subprocess.run([command,'evaluate',mode,variant],input=''.join(json.dumps(list(raw))+'\n' for raw in inputs),text=True,capture_output=True,check=True,timeout=600)
        assert [bytes(json.loads(line)) for line in result.stdout.splitlines()]==outputs,(mode,variant)
        path=directory/f'signal-kem-wire-{mode}-{variant}.json'
        with path.open('w') as out:subprocess.run([command,'signal-kem-wire',mode,variant],stdout=out,check=True,timeout=600)
        image=load(path);assert evaluate_lanes(image,inputs)==outputs,(mode,variant)
        fixture=path.with_name(path.stem+'-fixtures.json');fixture.write_text(json.dumps([{'input':raw.hex(),'output':out.hex()} for raw,out in zip(inputs,outputs)],indent=2)+'\n')
        row={'mode':mode,'variant':variant,'fixture_lanes':len(inputs),'artifact_sha256':digest(path),'fixture_sha256':digest(fixture),'adapter_operations':statistics(image),'all_outputs_match':True};rows.append(row);print(json.dumps(row),flush=True)
    files=set()
    def visit(module):
      if not module.startswith('TlsMpc'):return
      p=ROOT/(module.replace('.','/')+'.lean')
      if p in files:return
      files.add(p)
      for m in re.findall(r'^import ([\w.]+)',p.read_text(),re.M):visit(m)
    visit('TlsMpc.Signal.KemWire');files|={Path(__file__),checks,work/'Export.lean',work/'lakefile.toml',ROOT/'.deps/libsignal-v0.106.1/rust/protocol/src/kem.rs'}
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'checked_endpoints':len(names),'source_sha256':{str(f.relative_to(ROOT)):digest(f) for f in sorted(files)},'cases':rows,'fixture_lanes':sum(r['fixture_lanes'] for r in rows),'custom_axioms':[],'actual_signal_aeneas_refinement':False,'actual_signal_differential':False,'native_mpc_executed':False,'all_runtime_values_secret':True,'scope':'framing candidate KEM output; whole composed compiler theorem also checked; malformed key arithmetic not covered'}
    (ROOT/'benchmarks/results/lean-signal-kem-wire-checks.json').write_text(json.dumps(report,indent=2)+'\n');(ROOT/'SignalReference/kem-wire-axioms.txt').write_text(p.stdout)
if __name__=='__main__':main()
