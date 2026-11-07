#!/usr/bin/env python3
"""Actual numeric circuit composition through every KEM stage, all lanes public test fixtures."""
import hashlib,json,subprocess,sys
from datetime import datetime,timezone
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from SignalReference.MlKemWork.adapter import MlKem
from SignalReference.MlKemWork.artifacts import Registry,artifact_spec
from backend_adapter.boolean import load
from scripts.check_lean_signal_ratchet_step import digest

def packed(raws):
    return [sum(((raw[i//8]>>(7-i%8))&1)<<lane for lane,raw in enumerate(raws)) for i in range(8*len(raws[0]))]
def unpack(bits,lanes):
    return [bytes(sum(((bits[8*i+j]>>lane)&1)<<(7-j) for j in range(8)) for i in range(len(bits)//8)) for lane in range(lanes)]

def main():
    subprocess.run(['lake','build'],cwd=ROOT/'SignalReference/MlKemPolyWork',check=True)
    oracle=ROOT/'.deps/signal-libcrux-mlkem-oracle-target/debug/signal-libcrux-mlkem-oracle'
    manifest={'artifacts':{}};seen=set();rows=[];work=ROOT/'SignalReference/MlKemWork';registry_path=work/'artifact-manifest.json'
    def prepare(key):
        if key in seen:return
        path,command,args=artifact_spec(key)
        if not path.exists():
            assert command is not None,key
            path.parent.mkdir(exist_ok=True)
            with path.open('w') as out:subprocess.run([str(command),*args],stdout=out,check=True,timeout=600)
        image=load(path);manifest['artifacts'][str(path.relative_to(ROOT))]={'sha256':digest(path),'input_bits':image['input_bits'],'output_bits':len(image['outputs'])};del image
        seen.add(key);registry_path.write_text(json.dumps(manifest,indent=2)+'\n')
    for variant in ('mlkem1024','kyber1024'):
        seed=bytes(range(64));entropy=bytes(range(32))
        output=subprocess.run([str(oracle)],input=f'{variant}|{seed.hex()}|{entropy.hex()}\n',text=True,capture_output=True,check=True)
        sk,pk,ct,ss,recovered=map(bytes.fromhex,output.stdout.strip().split('|'));assert ss==recovered
        bad=bytearray(ct);bad[len(ct)//2]^=1;bad=bytes(bad)
        rejected=subprocess.run([str(oracle)],input=f'decap-{variant}|{sk.hex()}|{bad.hex()}\n',text=True,capture_output=True,check=True)
        badss=bytes.fromhex(rejected.stdout.strip())
        for mode,inputs,outputs in [('keygen',[seed],[b'\xff'+sk+pk]),('encapsulate',[pk+entropy],[b'\xff'+ct+ss]),('decapsulate',[sk+ct,sk+bad],[b'\xff'+ss,b'\xff'+badss])]:
            lanes=len(inputs);registry=Registry(manifest,0,2**lanes-1);calls=[]
            def invoke(key,bits):
                prepare(key);calls.append(key);print(variant,mode,'stage',len(calls),key,flush=True);return registry(key,bits)
            kem=MlKem(variant,invoke,0,2**lanes-1)
            actual=unpack(getattr(kem,mode)(packed(inputs)),lanes)
            assert actual==outputs,(variant,mode)
            fixture=work/f'adapter-{variant}-{mode}-fixtures.json';fixture.write_text(json.dumps([{'input':x.hex(),'output':y.hex()} for x,y in zip(inputs,outputs)],indent=2)+'\n')
            rows.append({'variant':variant,'mode':mode,'fixture_lanes':lanes,'stage_calls':len(calls),'fixture_sha256':digest(fixture),'all_outputs_match':True})
            registry.image.cache_clear();print(json.dumps(rows[-1]),flush=True)
            (work/'adapter-report.json').write_text(json.dumps({'complete':len(rows)==6,'checked_at_utc':datetime.now(timezone.utc).isoformat(),'cases':rows,'artifact_manifest_sha256':digest(registry_path),'native_mpc_executed':False,'mixed_compiler_executed':False,'actual_numeric_circuit_composition':True,'source_sha256':{str(p.relative_to(ROOT)):digest(p) for p in [Path(__file__),work/'adapter.py',work/'artifacts.py',ROOT/'TlsMpc/Signal/MlKemPoly.lean',ROOT/'SignalReference/MlKemPolyWork/Export.lean',ROOT/'backend_adapter/aig.py',ROOT/'backend_adapter/boolean.py']}},indent=2)+'\n')
if __name__=='__main__':main()
