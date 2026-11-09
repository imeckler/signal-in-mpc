#!/usr/bin/env python3
"""Compose actual key generation and AES entry with the compiled candidate."""
import hashlib,importlib.util,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
spec=importlib.util.spec_from_file_location('base',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 receipts=[HERE/'report.json',HERE/'key-schedule-recheck.json']
 for receipt in receipts:
  data=json.loads(receipt.read_text());assert data['passed']
  for name,want in data['source_sha256'].items():assert sha(ROOT/name)==want,name
 modules=['AesCtrBlockWork/FixsliceCircuitV1Work/'+n for n in ['KeySchedule','ComputedCipher64']];names=[]
 for module in modules:
  source=REF/(module+'.lean');body=source.read_text();assert not any(token in body for token in ['#eval','run_cmd','bv_decide','native_decide','sorry','axiom ']);names+=re.findall(r'^theorem (\w+)',body,re.M)
  r=subprocess.run(['lean','-o',str(base.BUILD/(module+'.olean')),module+'.lean'],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stdout+r.stderr
 audit=base.BUILD/'FixsliceComputedAxioms.lean';audit.write_text('import AesCtrBlockWork.FixsliceCircuitV1Work.ComputedCipher64\n'+''.join('#print axioms LibSignalReference.Candidate.FixsliceCircuitV1.'+name+'\n'for name in names))
 text=subprocess.check_output(['lean',str(audit)],cwd=REF,env=base.environment,text=True);assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==len(names)
 for group in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx'not in text and '_native'not in text
 (HERE/'computed-axioms.txt').write_text(text)
 files=[pathlib.Path(__file__),*receipts,*[REF/(m+'.lean')for m in modules]]
 objects=[base.BUILD/(m+'.olean')for m in modules+['AesKeyScheduleWork/FullSchedule','AesCtrBlockWork/FixsliceCircuitV1Work/Cipher64']]
 (HERE/'computed-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,kernel_endpoints=len(names),foundation_axioms_only=True,actual_key_schedule_and_AES256_entry_to_compiled_four_block_circuit=True,all_256_key_bits_and_512_plaintext_bits_unrestricted=True,supplied_expanded_keys_or_crypto_validity_flags=False,actual_generated_body_edits=False,inherited_Std_models_and_metadata_selection_trust_retained=True,trust_boundary_recheck='key-schedule-recheck.json',single_block_reduction=False,ciphertext_interop_tested=False,resource_measurements=False,production_changed=False,endpoints=names,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files},object_sha256={str(p.relative_to(ROOT)):sha(p)for p in objects}),indent=2)+'\n')
 print('PASS:'+str(len(names))+' foundational endpoints; computed key + actual AES entry -> compiled candidate')
if __name__=='__main__':main()
