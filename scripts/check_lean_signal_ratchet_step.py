#!/usr/bin/env python3
"""Public two-half ratchet fixtures; independent Python HKDF and byte-preserving rollback.
Does not claim full libsignal extraction or validate the provenance of supplied DH values.
"""
import argparse,hashlib,hmac,json,random,re,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from scripts.check_lean_crypto import evaluate_lanes,compile_and_check
from backend_adapter.boolean import load
from backend_adapter.aig import statistics

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def hkdf(root,dh):
    prk=hmac.digest(root,dh,'sha256');first=hmac.digest(prk,b'WhisperRatchet\x01','sha256')
    return first,hmac.digest(prk,first+b'WhisperRatchet\x02','sha256')
def expected(raw):
    old=raw[1:137]
    if raw[0]!=255 or raw[201:233]==bytes(32) or raw[233:265]==bytes(32):return bytes(1)+old+bytes(36)
    intermediate,receiver=hkdf(old[:32],raw[201:233]);root,sender=hkdf(intermediate,raw[233:265])
    previous=max(0,int.from_bytes(old[128:132],'big')-1).to_bytes(4,'big')
    return b'\xff'+root+raw[137:201]+sender+bytes(4)+previous+receiver+bytes(4)
def fixtures():
    rng=random.Random(615005);cases=[]
    for i,index in enumerate([0,1,2,255,256,65535,65536,2**31,2**32-1]):
        old=rng.randbytes(128)+index.to_bytes(4,'big')+rng.randbytes(4);new=rng.randbytes(128)
        for auth in(0,1,127,254,255):
            raw=bytes([auth])+old+new;cases.append((f'index-{index}-auth-{auth}',raw,expected(raw)))
        for name,agreements in(('zero-receive',bytes(32)+new[96:]),('zero-send',new[64:96]+bytes(32)),('both-zero',bytes(64))):
            raw=b'\xff'+old+new[:64]+agreements;cases.append((f'{name}-{index}',raw,expected(raw)))
    return cases

def main():
    cli=argparse.ArgumentParser();cli.add_argument('--compile-backend',action='store_true');args=cli.parse_args()
    work=ROOT/'SignalReference/RatchetStepWork';assert(work/'Export.lean').read_bytes()==(ROOT/'SignalReference/RatchetStepExport.lean').read_bytes()
    subprocess.run(['lake','build'],cwd=work,check=True)
    checks=ROOT/'SignalReference/RatchetStepChecks.lean';p=subprocess.run(['lake','env','lean',str(checks)],cwd=ROOT,check=True,text=True,capture_output=True)
    names=re.findall(r'^#print axioms (\S+)',checks.read_text(),re.M);found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",p.stdout)
    assert [n for n,_ in found]==names
    for n,a in found:assert not({x.strip() for x in a.split(',') if x.strip()}-{'propext','Quot.sound','Classical.choice'}),(n,a)
    cases=fixtures();inputs=[raw for _,raw,_ in cases];outputs=[out for _,_,out in cases];command=str(work/'.lake/build/bin/emit_ratchet_step')
    result=subprocess.run([command,'evaluate'],input=''.join(json.dumps(list(w))+'\n' for w in inputs),text=True,capture_output=True,check=True,timeout=300)
    assert [bytes(json.loads(line)) for line in result.stdout.splitlines()]==outputs
    directory=ROOT/'.deps/signal-ratchet-step-artifacts';directory.mkdir(exist_ok=True);path=directory/'signal-ratchet-step.json'
    with path.open('w') as out:subprocess.run([command,'signal-ratchet-step'],stdout=out,check=True,timeout=300)
    artifact=load(path);assert evaluate_lanes(artifact,inputs)==outputs
    fixture=path.with_name(path.stem+'-fixtures.json');fixture.write_text(json.dumps([{'label':l,'input':w.hex(),'output':e.hex()} for l,w,e in cases],indent=2)+'\n')
    row={'fixture_lanes':len(cases),'artifact_sha256':digest(path),'fixture_sha256':digest(fixture),'adapter_operations':statistics(artifact),'all_outputs_match':True}
    if args.compile_backend:row['mpc_compilations']=[compile_and_check(path,inputs,outputs,batch) for batch in(1,16)]
    files=set()
    def visit(module):
        if not module.startswith('TlsMpc'):return
        p=ROOT/(module.replace('.','/')+'.lean')
        if p in files:return
        files.add(p)
        for m in re.findall(r'^import ([\w.]+)',p.read_text(),re.M):visit(m)
    visit('TlsMpc.Signal.RatchetStep')
    files|={Path(__file__),checks,ROOT/'SignalReference/RatchetStepExport.lean',work/'Export.lean',work/'lakefile.toml',ROOT/'.deps/libsignal-v0.106.1/rust/protocol/src/double_ratchet.rs',ROOT/'scripts/check_lean_crypto.py'}
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'checked_endpoints':len(names),'source_sha256':{str(p.relative_to(ROOT)):digest(p) for p in sorted(files)},'cases':[row],'full_actual_rust_ratchet_refinement':False,'native_mpc_executed':False,'all_runtime_values_secret':True,'custom_axioms':[],'remaining_boundaries':['X25519 agreement provenance','fresh shared keypair provenance','receiver chain selection and retention','first-message authentication composition','atomic persistent commit']}
    (ROOT/'benchmarks/results/lean-signal-ratchet-step-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    (ROOT/'SignalReference/ratchet-step-axioms.txt').write_text(p.stdout)
    print(json.dumps(row),flush=True)
if __name__=='__main__':main()
