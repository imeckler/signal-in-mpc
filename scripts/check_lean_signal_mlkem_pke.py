#!/usr/bin/env python3
"""Differential PKE composition versus actual pinned libcrux public KEM API."""
import hashlib,json,random,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from scripts.check_lean_signal_ratchet_step import digest

def main():
    work=ROOT/'SignalReference/MlKemPkeWork';subprocess.run(['lake','build'],cwd=work,check=True)
    subprocess.run(['cargo','build','--offline','--target-dir',str(ROOT/'.deps/signal-libcrux-mlkem-oracle-target')],cwd=work/'Oracle',check=True)
    oracle=ROOT/'.deps/signal-libcrux-mlkem-oracle-target/debug/signal-libcrux-mlkem-oracle';lean=work/'.lake/build/bin/emit_mlkem_pke';rows=[];rng=random.Random(10243329)
    for variant in ('mlkem512','mlkem768','mlkem1024','kyber1024'):
        rank={'mlkem512':2,'mlkem768':3}.get(variant,4)
        vectors=[(bytes(64),bytes(32)),(bytes(range(64)),bytes(range(32))), (bytes(rng.randrange(256) for _ in range(64)),bytes(rng.randrange(256) for _ in range(32)))]
        response=subprocess.run([str(oracle)],input=''.join(f'{variant}|{seed.hex()}|{entropy.hex()}\n' for seed,entropy in vectors),text=True,capture_output=True,check=True)
        fixtures=[]
        for (seed,entropy),line in zip(vectors,response.stdout.splitlines()):
            sk,pk,ct,ss,recovered=map(bytes.fromhex,line.split('|'));assert ss==recovered
            message=hashlib.sha3_256(entropy).digest() if variant.startswith('kyber') else entropy
            expanded=hashlib.sha3_512(message+hashlib.sha3_256(pk).digest()).digest();coins=expanded[32:]
            for mode,raw,expected in [('keygen',seed[:32],b'\xff'+sk[:384*rank]+pk),('encrypt',pk+message+coins,b'\xff'+ct),('decrypt',sk[:384*rank]+ct,message)]:
                result=subprocess.run([str(lean),mode,variant],input=json.dumps(list(raw))+'\n',text=True,capture_output=True,check=True,timeout=600)
                actual=bytes(json.loads(result.stdout));assert actual==expected,(variant,mode,next((i for i,(a,b) in enumerate(zip(actual,expected)) if a!=b),None),len(actual),len(expected))
                fixtures.append({'mode':mode,'input':raw.hex(),'output':expected.hex()});print(variant,mode,len(raw),'pass',flush=True)
        path=work/f'{variant}-fixtures.json';path.write_text(json.dumps(fixtures,indent=2)+'\n');rows.append({'variant':variant,'fixture_lanes':len(fixtures),'fixture_sha256':digest(path),'all_outputs_match':True})
    report={'cases':rows,'actual_pinned_libcrux_public_api_differential':True,'pke_composition_compiler_proof':False,'pke_numeric_artifact_composition_checked':False,'actual_libcrux_aeneas_refinement':False,'full_mlkem_cca':False,'native_mpc_executed':False}
    (ROOT/'benchmarks/results/lean-signal-mlkem-pke-checks.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
