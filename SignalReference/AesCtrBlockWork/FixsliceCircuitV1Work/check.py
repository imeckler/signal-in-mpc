#!/usr/bin/env python3
"""Isolated actual-source-backed fixslice circuit; production is unchanged."""
import hashlib,importlib.util,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
spec=importlib.util.spec_from_file_location('base',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 receipts=[HERE.parent/'EncryptBoundV1/entry-report.json',HERE.parent/'inverse-layout-report.json']
 for receipt in receipts:
  data=json.loads(receipt.read_text());assert data['passed']
  for name,want in data['source_sha256'].items():assert sha(ROOT/name)==want,name
 modules=['LibSignalReference/Proofs/AesLayout']+['AesCtrBlockWork/FixsliceCircuitV1Work/'+n for n in ['Core','Symbolic64','Layout','Cipher64']]
 names=[]
 for module in modules:
  out=base.BUILD/(module+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
  source=REF/(module+'.lean');body=source.read_text()
  if module.startswith('AesCtrBlockWork/'):
   assert not any(token in body for token in ['#eval','run_cmd','bv_decide','native_decide','sorry','axiom '])
   names+=re.findall(r'^theorem (\w+)',body,re.M)
  r=subprocess.run(['lean','-o',str(out),module+'.lean'],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stdout+r.stderr
 audit=base.BUILD/'FixsliceCircuitV1Axioms.lean';audit.write_text('import AesCtrBlockWork.FixsliceCircuitV1Work.Cipher64\n'+''.join('#print axioms LibSignalReference.Candidate.FixsliceCircuitV1.'+n+'\n'for n in names))
 text=subprocess.check_output(['lean',str(audit)],cwd=REF,env=base.environment,text=True);assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==len(names)
 for group in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx'not in text and '_native'not in text
 (HERE/'axioms.txt').write_text(text)
 files=[pathlib.Path(__file__),*receipts,*[REF/(m+'.lean')for m in modules]]
 objects=[base.BUILD/(m+'.olean')for m in modules+['AesCtrBlockWork/EncryptBoundV1/EntryReference']]
 (HERE/'report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,kernel_endpoints=len(names),foundation_axioms_only=True,actual_AES256_entry_to_compiled_four_block_circuit=True,arbitrary_fifteen_eight_word_expanded_keys=True,all_sixtyfour_plaintext_bytes_unrestricted=True,primitive_correctness_flags_assumed=False,actual_generated_body_edits=False,source_Std_and_indexed_Zip_boundary_unchanged=True,actual_key_schedule_composed=False,single_block_reduced_circuit=False,ciphertext_interop_tested=False,resource_measurements=False,production_changed=False,endpoints=names,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files},object_sha256={str(p.relative_to(ROOT)):sha(p)for p in objects}),indent=2)+'\n')
 print('PASS:'+str(len(names))+' foundational endpoints; actual AES entry -> compiled four-block candidate (expanded keys)')
if __name__=='__main__':main()
