#!/usr/bin/env python3
"""Complete bounded CCA semantics against unchanged pinned libcrux, including implicit rejection."""
import hashlib,json,random,re,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from scripts.check_lean_signal_ratchet_step import digest

def audit():
    names=[];out=''
    for module in ('MlKemPke','MlKem'):
        p=ROOT/f'SignalReference/{module}Checks.lean';names+=re.findall(r'^#print axioms (\S+)',p.read_text(),re.M)
        out+=subprocess.run(['lake','env','lean',str(p)],cwd=ROOT,check=True,text=True,capture_output=True).stdout
    found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",out)
    assert [n for n,_ in found]==names
    for n,a in found:assert not({x.strip() for x in a.split(',') if x.strip()}-{'propext','Quot.sound','Classical.choice'}),(n,a)
    (ROOT/'SignalReference/mlkem-cca-axioms.txt').write_text(out)
    return len(names)

def source_files():
    files=set()
    def visit(module):
        if not module.startswith('TlsMpc'):return
        p=ROOT/(module.replace('.','/')+'.lean')
        if p in files:return
        files.add(p)
        for m in re.findall(r'^import ([\w.]+)',p.read_text(),re.M):visit(m)
    visit('TlsMpc.Signal.MlKem')
    files|={Path(__file__),ROOT/'scripts/check_lean_signal_mlkem_pke.py',ROOT/'SignalReference/MlKemChecks.lean',ROOT/'SignalReference/MlKemPkeChecks.lean'}
    for work in ('MlKemWork','MlKemPkeWork'):
        files|={ROOT/f'SignalReference/{work}/Export.lean',ROOT/f'SignalReference/{work}/lakefile.toml'}
    oracle=ROOT/'SignalReference/MlKemPkeWork/Oracle'
    files|={oracle/'Cargo.toml',oracle/'Cargo.lock',oracle/'.cargo/config.toml',oracle/'src/main.rs',oracle/'manifest-only.diff',oracle/'source-provenance.json'}
    provenance=json.loads((oracle/'source-provenance.json').read_text())
    for f,h in provenance['unchanged_rust_source_sha256'].items():
        a=ROOT/'.deps/libsignal-vendor/libcrux-ml-kem-0.0.10'/f;b=ROOT/'.deps/signal-mlkem-oracle-source'/f
        assert digest(a)==digest(b)==h,f;files|={a,b}
    for p in ('libcrux-ml-kem-0.0.10','libcrux-sha3-0.0.10','libcrux-intrinsics-0.0.8','libcrux-platform-0.0.3','libcrux-secrets-0.0.6','libcrux-traits-0.0.8'):
        files |= set((ROOT/'.deps/libsignal-vendor'/p).rglob('*.rs'))
        files.add(ROOT/'.deps/libsignal-vendor'/p/'Cargo.toml')
    files.add(ROOT/'.deps/signal-mlkem-oracle-source/Cargo.toml')
    return files

def main():
    work=ROOT/'SignalReference/MlKemWork';subprocess.run(['lake','build'],cwd=work,check=True)
    subprocess.run(['cargo','build','--offline','--target-dir',str(ROOT/'.deps/signal-libcrux-mlkem-oracle-target')],cwd=ROOT/'SignalReference/MlKemPkeWork/Oracle',check=True)
    count=audit();files=source_files();hashes={str(p.relative_to(ROOT)):digest(p) for p in sorted(files)}
    oracle=ROOT/'.deps/signal-libcrux-mlkem-oracle-target/debug/signal-libcrux-mlkem-oracle';lean=work/'.lake/build/bin/emit_mlkem';rows=[];rng=random.Random(2031024)
    for variant in ('mlkem512','mlkem768','mlkem1024','kyber1024'):
        vectors=[(bytes(64),bytes(32)),(bytes(rng.randrange(256) for _ in range(64)),bytes(rng.randrange(256) for _ in range(32)))]
        response=subprocess.run([str(oracle)],input=''.join(f'{variant}|{seed.hex()}|{entropy.hex()}\n' for seed,entropy in vectors),text=True,capture_output=True,check=True)
        fixtures=[]
        for index,((seed,entropy),line) in enumerate(zip(vectors,response.stdout.splitlines())):
            sk,pk,ct,ss,recovered=map(bytes.fromhex,line.split('|'));assert ss==recovered
            cases=[('keygen',seed,b'\xff'+sk+pk),('encapsulate',pk+entropy,b'\xff'+ct+ss),('decapsulate',sk+ct,b'\xff'+ss)]
            if index==0:
                for offset in (0,len(ct)//2,len(ct)-1):
                    tampered=bytearray(ct);tampered[offset]^=1;tampered=bytes(tampered)
                    result=subprocess.run([str(oracle)],input=f'decap-{variant}|{sk.hex()}|{tampered.hex()}\n',text=True,capture_output=True,check=True)
                    rejected=bytes.fromhex(result.stdout.strip());assert rejected!=ss
                    cases.append(('decapsulate',sk+tampered,b'\xff'+rejected))
            for mode,raw,expected in cases:
                result=subprocess.run([str(lean),mode,variant],input=json.dumps(list(raw))+'\n',text=True,capture_output=True,check=True,timeout=600)
                actual=bytes(json.loads(result.stdout));assert actual==expected,(variant,mode,next((i for i,(a,b) in enumerate(zip(actual,expected)) if a!=b),None),len(actual),len(expected))
                fixtures.append({'mode':mode,'input':raw.hex(),'output':expected.hex()});print(variant,mode,len(raw),'pass',flush=True)
        path=work/f'{variant}-fixtures.json';path.write_text(json.dumps(fixtures,indent=2)+'\n');rows.append({'variant':variant,'fixture_lanes':len(fixtures),'implicit_rejection_cases':3,'fixture_sha256':digest(path),'all_outputs_match':True})
    for p,h in hashes.items():assert digest(ROOT/p)==h,p
    report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'checked_endpoints':count,'custom_axioms':[],'source_sha256':hashes,'cases':rows,'actual_pinned_libcrux_public_api_differential':True,'whole_cca_compiler_proof':True,'full_numeric_artifact_composition_checked':False,'actual_libcrux_aeneas_refinement':False,'native_mpc_executed':False,'all_runtime_values_secret':True,'matrix_budget_bytes_per_entry':672,'bounded_abort':'outer status0 and all output bytes zero on matrix sampler exhaustion; ciphertext mismatch uses secret implicit-rejection selection with status255','input_precondition':'exact variant sizes and valid generated keys; no malformed-key equivalence claim','oracle_manifest_delta':'isolated disabled optional tls_codec dependency removal; every pinned Rust source byte unchanged'}
    (ROOT/'benchmarks/results/lean-signal-mlkem-checks.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
