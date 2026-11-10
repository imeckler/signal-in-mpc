#!/usr/bin/env python3
"""Kernel audit, generated decoder tests, and unchanged dalek normalization checks."""
import hashlib,json,random,re,subprocess,tarfile
from pathlib import Path
import build,provenance
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(args,**kw):return subprocess.run(args,text=True,capture_output=True,check=True,**kw).stdout

def main():
    frozen={}
    for area,h in [('XEdDsaWork','352b001526f35f40e9789f116b2902469b22292cda37734ec8a1b196f758cb9a'),
                   ('PreKeyWork','91bf953ee2b7267aae8f06772f4c0c1a693f673d4e2c44979389e7f37798a23b'),
                   ('PreKeyReferenceWork','ec47f0a1403345e441c7560aa644ea0adf653f7af5bec888c82564268685eb80')]:
        path=HERE.parent/area/'completion.json';assert sha(path)==h
        for f,fh in json.loads(path.read_text())['files'].items():assert sha(ROOT/f)==fh,f
        frozen[area]=h
    inventory=json.loads((HERE/'Artifacts/FieldDecode/inventory.json').read_text())
    assert inventory['charon_exit_code']==inventory['aeneas_exit_code']==0 and not inventory['has_errors']
    assert inventory['remaining_external_templates']==[]
    assert sha(HERE/'extract.py')==inventory['script_sha256']
    assert sha(HERE/'Artifacts/FieldDecode/field_decode.llbc')==inventory['llbc_sha256']
    for f,h in inventory['source_sha256'].items():assert sha(ROOT/f)==h,f
    for f,h in inventory['generated_files'].items():assert sha(HERE.parent/f)==h,f
    pins=json.loads((HERE.parent/'pins.json').read_text())
    archive=ROOT/'.deps/aeneas-macos-aarch64-2026-08-27.tar.gz'
    assert sha(archive)==pins['aeneas']['macos_aarch64_archive_sha256']
    model_hashes={}
    with tarfile.open(archive) as tar:
        for p in sorted((build.MODEL/'Aeneas').rglob('*.lean')):
            rel=str(p.relative_to(build.MODEL));assert tar.extractfile('backends/lean/'+rel).read()==p.read_bytes(),rel
            model_hashes[rel]=sha(p)
    assert 'version 4.31.0' in run(['lean','--version'])
    provenance.main()
    for p in HERE.glob('*.lean'):
        assert not re.search(r'\b(?:sorry|admit|axiom)\b',p.read_text()),p
    build.main()
    prefix='XEdDsaReference.backend.serial.u64.field.FieldElement51.'
    endpoints=['Aeneas.Std.Array.asNat_eq_sum','Aeneas.Std.Array.index_usize_getElem!_spec',
      'Aeneas.Std.Slice.index_usize_getElem!_spec','Nat.forall_lt_five','Nat.sum_pow_mul_lt',
      'Aeneas.Std.UScalar.and_two_pow_sub_one_spec','Nat.or_shiftLeft_eq_add_pow_mul',prefix+'asNat_eq',
      prefix+'from_bytes.load8_at_spec',prefix+'from_bytes_spec',
      *['XEdDsaReference.RecoveryInput.'+n for n in ['actual_decode_normalizes','decode_nat_value',
        'high_bit_ignored','noncanonical_reduction','compiled_recovery_input',
        'actual_decode_field_alias','compiled_recovery_field_alias']]]
    audit=HERE/'AxiomAudit.lean';audit.write_text('import XEdDsaReferenceWork.RecoveryInput\n'+''.join('#print axioms '+n+'\n' for n in endpoints))
    axioms=run(['lean',str(audit)],cwd=HERE.parent,env=build.env);(HERE/'axioms.txt').write_text(axioms)
    assert 'sorryAx' not in axioms and 'RustAx' not in axioms
    for group in re.findall(r'depends on axioms: \[(.*?)\]',axioms,re.S):
        assert set(re.findall(r'[\w.]+',group)) <= {'propext','Classical.choice','Quot.sound'},group
    p=2**255-19;rng=random.Random(25151)
    low=set(range(21))|set(range(p-1,p+19))|{1<<i for i in range(255)}|{rng.randrange(2**255) for _ in range(128)}
    numbers=sorted(low|{n+2**255 for n in low})
    output=run(['lean','--run',str(HERE/'Evaluate.lean')],cwd=HERE.parent,env=build.env,
      input=''.join(json.dumps(list(n.to_bytes(32,'little')))+'\n' for n in numbers))
    rows=[json.loads(line) for line in output.splitlines()];assert len(rows)==len(numbers)
    for n,row in zip(numbers,rows):
        lo=n%(2**255);assert row==[lo,lo%p,*[(lo>>(51*i))%2**51 for i in range(5)]]
    oracle=ROOT/'.deps/signal-xeddsa-oracle-target/debug/signal-xeddsa-oracle'
    receipt=json.loads((HERE.parent/'XEdDsaWork/report.json').read_text());assert sha(oracle)==receipt['oracle_binary_sha256']
    lines=[]
    for n,row in zip(numbers,rows):
        for sign in [0,1]:
            lines += [f'recover {n.to_bytes(32,"little").hex()} {sign}',f'recover {row[1].to_bytes(32,"little").hex()} {sign}']
    native=run([str(oracle)],input='\n'.join(lines)+'\n').splitlines();assert len(native)==len(lines)
    assert all(native[i]==native[i+1] for i in range(0,len(native),2))
    fixtures=[{'input_hex':n.to_bytes(32,'little').hex(),'decoded':row,
      'native_recovery':[native[4*i],native[4*i+2]]} for i,(n,row) in enumerate(zip(numbers,rows))]
    (HERE/'fixtures.json').write_text(json.dumps(fixtures,indent=2)+'\n')
    report={'candidate_only':True,'accepted_reference':False,'actual_aeneas_field_decoder_refinement':True,
      'full_xeddsa_or_to_edwards_refinement':False,'rust_source_edits':[],'llbc_edits':[],
      'generated_lean_edits':[],'custom_external_models':[],'translator_edits':[],
      'checked_inputs_sha256':{str(p.relative_to(HERE)):sha(p) for p in sorted(HERE.rglob('*'))
        if p.is_file() and (p.suffix in {'.lean','.py'} or p.name=='lean-toolchain')
        and not any(x in {'Build','__pycache__'} for x in p.relative_to(HERE).parts)},
      'proof_endpoints':endpoints,'standard_axioms_only':True,'axioms_sha256':sha(HERE/'axioms.txt'),
      'pinned_versions':inventory['versions'],'llbc_sha256':inventory['llbc_sha256'],
      'pinned_aeneas_lean_source_sha256':model_hashes,'generated_decoder_cases':len(rows),
      'native_original_vs_normalized_recovery_pairs':len(lines)//2,'native_oracle_sha256':sha(oracle),
      'fixtures_sha256':sha(HERE/'fixtures.json'),'baf_provenance_sha256':sha(HERE/'baf-provenance.json'),
      'frozen_dependencies':frozen,'new_circuit_gates':0,'new_backend_artifacts':0,
      'scope':'Actual FieldElement51 from_bytes/load8_at low255 normalization, limb bounds and input bridge to frozen recovery compiler theorem. No full dalek to_edwards, SHA512/scalar reduction, signature authentication, private conversion execution or MPC claim.'}
    (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'{len(endpoints)} kernel endpoints; {len(rows)} generated decoder cases; {len(lines)//2} native normalization pairs')
if __name__=='__main__':main()
