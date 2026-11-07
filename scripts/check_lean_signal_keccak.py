#!/usr/bin/env python3
"""Shared Keccak sponge versus Python hashlib and unchanged pinned libcrux-sha3."""
import hashlib,json,os,random,re,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from scripts.check_lean_signal_ratchet_step import digest
from scripts.check_lean_crypto import evaluate_lanes
from backend_adapter.boolean import load
from backend_adapter.aig import statistics

def expected(mode,raw,count):
    if mode=='sha3-256':return hashlib.sha3_256(raw).digest()
    if mode=='sha3-512':return hashlib.sha3_512(raw).digest()
    if mode=='shake128':return hashlib.shake_128(raw).digest(count)
    return hashlib.shake_256(raw).digest(count)

def main():
    work=ROOT/'SignalReference/KeccakWork';assert(work/'Export.lean').read_bytes()==(ROOT/'SignalReference/KeccakExport.lean').read_bytes()
    subprocess.run(['lake','build'],cwd=work,check=True)
    checks=ROOT/'SignalReference/KeccakChecks.lean';p=subprocess.run(['lake','env','lean',str(checks)],cwd=ROOT,check=True,text=True,capture_output=True)
    names=re.findall(r'^#print axioms (\S+)',checks.read_text(),re.M);found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",p.stdout)
    assert [n for n,_ in found]==names
    for n,a in found:assert not({x.strip() for x in a.split(',') if x.strip()}-{'propext','Quot.sound','Classical.choice'}),(n,a)
    env=os.environ.copy();env['RUSTC']=str(ROOT/'.deps/rust-nightly-2026-08-18/bin/rustc');target=ROOT/'.deps/signal-libcrux-sha3-oracle-target'
    subprocess.run([str(ROOT/'.deps/rust-nightly-2026-08-18/bin/cargo'),'build','--offline','--target-dir',str(target)],cwd=work/'Oracle',env=env,check=True)
    oracle=target/'debug/signal-libcrux-sha3-oracle';command=str(work/'.lake/build/bin/emit_keccak');rng=random.Random(5433543);cases=[]
    for mode,count in [('sha3-256',32),('sha3-512',64),('shake128',0),('shake128',32),('shake128',504),('shake256',32),('shake256',137),('shake256',272)]:
        inputs=[b'',b'abc',*map(lambda n:rng.randbytes(n),(1,31,32,33,34,63,64,71,72,73,135,136,137,167,168,169,200,336,1024))]
        outputs=[expected(mode,raw,count) for raw in inputs]
        result=subprocess.run([command,'evaluate',mode,str(count)],input=''.join(json.dumps(list(raw))+'\n' for raw in inputs),text=True,capture_output=True,check=True,timeout=300)
        got=[bytes(json.loads(line)) for line in result.stdout.splitlines()];assert got==outputs,mode
        observed=subprocess.run([str(oracle)],input=''.join(f'{mode}|{count}|{raw.hex()}\n' for raw in inputs),capture_output=True,text=True,check=True)
        assert [bytes.fromhex(line) for line in observed.stdout.splitlines()]==outputs,mode
        cases += [(mode,count,raw,out) for raw,out in zip(inputs,outputs)]
    directory=ROOT/'.deps/signal-keccak-artifacts';directory.mkdir(exist_ok=True);rows=[]
    profiles=[('sha3-256',32,32),('sha3-256',136,32),('sha3-512',64,64),('sha3-512',72,64),('shake128',34,504),('shake128',168,32),('shake256',33,272),('shake256',136,137)]
    for mode,size,count in profiles:
        inputs=[bytes(size),bytes([255])*size,*[rng.randbytes(size) for _ in range(14)]];outputs=[expected(mode,raw,count) for raw in inputs]
        path=directory/f'signal-keccak-{mode}-{size}-{count}.json'
        with path.open('w') as out:subprocess.run([command,'signal-keccak',mode,str(size),str(count)],stdout=out,check=True,timeout=300)
        artifact=load(path);assert evaluate_lanes(artifact,inputs)==outputs,(mode,size,count)
        fixture=path.with_name(path.stem+'-fixtures.json');fixture.write_text(json.dumps([{'input':raw.hex(),'output':out.hex()} for raw,out in zip(inputs,outputs)],indent=2)+'\n')
        row={'mode':mode,'input_bytes':size,'output_bytes':count,'fixture_lanes':len(inputs),'artifact_sha256':digest(path),'fixture_sha256':digest(fixture),'adapter_operations':statistics(artifact),'all_outputs_match':True};rows.append(row);print(json.dumps(row),flush=True)
    files=set()
    def visit(module):
        if not module.startswith('TlsMpc'):return
        p=ROOT/(module.replace('.','/')+'.lean')
        if p in files:return
        files.add(p)
        for m in re.findall(r'^import ([\w.]+)',p.read_text(),re.M):visit(m)
    visit('TlsMpc.Signal.Keccak')
    files|={Path(__file__),checks,ROOT/'SignalReference/KeccakExport.lean',work/'Export.lean',work/'lakefile.toml',work/'Oracle/Cargo.toml',work/'Oracle/Cargo.lock',work/'Oracle/src/main.rs',ROOT/'scripts/check_lean_crypto.py',oracle}
    for dep in ('libcrux-sha3-0.0.10','libcrux-intrinsics-0.0.8','libcrux-traits-0.0.8'):
        files.update((ROOT/'.deps/libsignal-vendor'/dep/'src').rglob('*.rs'))
    fixture=directory/'concrete-fixtures.json';fixture.write_text(json.dumps([{'mode':m,'output_bytes':c,'input':raw.hex(),'output':out.hex()} for m,c,raw,out in cases],indent=2)+'\n')
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'checked_endpoints':len(names),'source_sha256':{str(f.relative_to(ROOT)):digest(f) for f in sorted(files)},'concrete_and_actual_libcrux_cases':len(cases),'concrete_fixture_sha256':digest(fixture),'cases':rows,'custom_axioms':[],'actual_libcrux_aeneas_refinement':False,'native_mpc_executed':False,'all_runtime_values_secret':True,'full_mlkem':False}
    (ROOT/'benchmarks/results/lean-signal-keccak-checks.json').write_text(json.dumps(report,indent=2)+'\n');(ROOT/'SignalReference/keccak-axioms.txt').write_text(p.stdout)
if __name__=='__main__':main()
