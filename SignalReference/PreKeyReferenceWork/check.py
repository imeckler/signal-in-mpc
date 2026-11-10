#!/usr/bin/env python3
"""Check scoped actual generated PreKey control flow without changing frozen work."""
import hashlib,json,re,subprocess,tarfile
from pathlib import Path
import build
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(args,**kw):return subprocess.run(args,text=True,capture_output=True,check=True,**kw).stdout

def main():
    frozen={}
    pins=json.loads((ROOT/'SignalReference/pins.json').read_text())
    archive=ROOT/'.deps/aeneas-macos-aarch64-2026-08-27.tar.gz'
    assert sha(archive)==pins['aeneas']['macos_aarch64_archive_sha256']
    model_hashes={}
    with tarfile.open(archive) as tar:
        for p in sorted((build.MODEL/'Aeneas').rglob('*.lean')):
            rel=str(p.relative_to(build.MODEL))
            assert tar.extractfile('backends/lean/'+rel).read()==p.read_bytes(),rel
            model_hashes[rel]=sha(p)
    assert 'version 4.31.0' in run(['lean','--version'])
    for name,expected in [('PreKeyWork','91bf953ee2b7267aae8f06772f4c0c1a693f673d4e2c44979389e7f37798a23b'),('XEdDsaWork','352b001526f35f40e9789f116b2902469b22292cda37734ec8a1b196f758cb9a')]:
        manifest=ROOT/'SignalReference'/name/'completion.json';assert sha(manifest)==expected
        for f,h in json.loads(manifest.read_text())['files'].items():assert sha(ROOT/f)==h,f
        frozen[name]=expected
    inventory=json.loads((HERE/'Artifacts/ContentModels/inventory.json').read_text())
    assert inventory['charon_exit_code']==inventory['aeneas_exit_code']==0 and not inventory['has_errors']
    assert sha(HERE/'extract.py')==inventory['script_sha256']
    assert sha(HERE/'Artifacts/ContentModels/prekey.llbc')==inventory['llbc_sha256']
    for f,h in inventory['generated_files'].items():assert sha(HERE.parent/f)==h,f
    for f,h in inventory['source_sha256'].items():assert sha(ROOT/f)==h,f
    generated=(HERE/'Generated/ContentModels/Funs.lean').read_text()
    assert generated.count('Source: \'rust/protocol/src/state/bundle.rs\', lines 84:4-121:5')==1
    proof=(HERE/'Proofs.lean').read_text()
    for p in [HERE/'Proofs.lean',HERE/'Generated/ContentModels/Funs.lean',HERE/'Generated/ContentModels/Types.lean',HERE/'Generated/ContentModels/FunsExternal.lean',HERE/'Generated/ContentModels/TypesExternal.lean']:
        assert not re.search(r'\b(?:sorry|admit|axiom)\b',p.read_text()),p
    build.main()
    names=['PreKeyReference.Proofs.'+n for n in re.findall(r'^theorem (\w+)',proof,re.M)]
    audit=HERE/'AxiomAudit.lean';audit.write_text('import PreKeyReferenceWork.Proofs\n'+''.join('#print axioms '+n+'\n' for n in names))
    axioms=run(['lean',str(audit)],cwd=HERE.parent,env=build.env)
    (HERE/'axioms.txt').write_text(axioms)
    assert 'sorryAx' not in axioms
    for group in re.findall(r'depends on axioms: \[(.*?)\]',axioms,re.S):
        assert set(re.findall(r'[\w.]+',group)) <= {'propext','Classical.choice','Quot.sound'},group
    actual=run(['lean','--run',str(HERE/'Evaluate.lean')],cwd=HERE.parent,env=build.env)
    rows=[json.loads(line) for line in actual.splitlines()]
    oracle=ROOT/'SignalReference/PreKeyWork/Bin/oracle-base'
    receipt=json.loads((ROOT/'SignalReference/PreKeyWork/report.json').read_text())
    assert sha(oracle)==receipt['oracle_binary_sha256']['base']
    requests=[]
    for n in range(2048):
        requests.append({'mode':'construct','flags':[(n>>i)&1 for i in range(11)],
            'registration':n*1048577,'device':127,'optional_id':[0,1,2**31,2**32-1][n%4],
            'signed_id':[2**32-1,2**31,1,0][n%4],'pq_id':n*65537,
            'ec':'05'+'00'*32,'identity':'05'+'00'*32,'pq':'08'+'00'*1568,
            'ec_sig':'','pq_sig':''})
    native=run([str(oracle)],input=''.join(json.dumps(r)+'\n' for r in requests))
    answers=[json.loads(line) for line in native.splitlines()];expected=[]
    for a in answers:
        if a['code']:expected.append([a['code'],0,0,0,0,0,0]);continue
        m=bytes(a['metadata']);expected.append([0,int(a['optional']),int.from_bytes(m[:4],'big'),m[4],*[int.from_bytes(m[i:i+4],'big') for i in [5,9,13]]])
    assert len(rows)==2048 and rows==expected
    transcript=[{'presence':n,'result':row} for n,row in enumerate(rows)]
    (HERE/'differential-cases.json').write_text(json.dumps(transcript,indent=2)+'\n')
    std=ROOT/'.deps/rust-nightly-2026-08-18/lib/rustlib/src/rust/library/core/src'
    model_sources=[std/'option.rs',std/'num/nonzero.rs',std/'num/niche_types.rs',
                   ROOT/'.deps/libsignal-v0.106.1/rust/protocol/src/state/bundle.rs',
                   ROOT/'.deps/libsignal-v0.106.1/rust/protocol/src/kem/kyber1024.rs']
    report={'candidate_only':True,'accepted_reference':False,'profile':'ContentModels',
        'actual_generated_control_flow':True,'full_actual_aeneas_refinement':False,
        'computational_rust_edits':[],'llbc_edits':[],'generated_lean_edits':[],
        'pinned_aeneas_lean_source_sha256':model_hashes,
        'pinned_versions':inventory['versions'],'llbc_sha256':inventory['llbc_sha256'],
        'proof_endpoints':names,'standard_axioms_only':True,'axiom_audit_sha256':sha(HERE/'axioms.txt'),
        'actual_native_constructor_presence_cases':len(rows),'native_oracle_sha256':sha(oracle),
        'differential_cases_sha256':sha(HERE/'differential-cases.json'),
        'frozen_dependencies':frozen,'external_model_source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in model_sources},
        'external_model_boundaries':['Option::zip','Option::ok_or_else','NonZero representation',
          'InvalidArgument-only error projection','nine missing-field error closures','unused Kyber1024 key_length'],
        'scope':'Default Kyber1024 typed bundle; required presence/order, optional pairing, all payload preservation. No parsing, trust-store policy, signature verification, allocator/destructor semantics, async session state, MPC execution or production wiring.',
        'new_circuit_gate_count':0,'new_backend_artifacts':0}
    (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'{len(names)} kernel endpoints; {len(rows)} actual Rust constructor cases match')
if __name__=='__main__':main()
