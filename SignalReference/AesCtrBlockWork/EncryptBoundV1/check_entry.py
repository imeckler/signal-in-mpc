#!/usr/bin/env python3
"""Entire actual AES256 block entry -> explicit raw fixslice model."""
import hashlib,importlib.util,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
spec=importlib.util.spec_from_file_location('base',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 receipts=[HERE/'rounds-report.json',HERE.parent/'inverse-layout-report.json']
 for receipt in receipts:
  data=json.loads(receipt.read_text());assert data['passed']
  for name,want in data['source_sha256'].items():assert sha(ROOT/name)==want,name
 module='AesCtrBlockWork/EncryptBoundV1/EntryReference';out=base.BUILD/(module+'.olean')
 r=subprocess.run(['lean','-o',str(out),module+'.lean'],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stdout+r.stderr
 names=['default_state','first_key','last_key','actual_entry']
 audit=base.BUILD/'ActualAesEntryAxioms.lean';audit.write_text('import '+module.replace('/','.')+'\n'+''.join('#print axioms LibSignalReference.Candidate.AesEntryReference.'+name+'\n'for name in names))
 text=subprocess.check_output(['lean',str(audit)],cwd=REF,env=base.environment,text=True);assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==len(names)
 for group in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx'not in text and '_native'not in text
 (HERE/'entry-axioms.txt').write_text(text)
 files=[pathlib.Path(__file__),HERE/'EntryReference.lean',*receipts]
 objects=[base.BUILD/(m+'.olean')for m in [module,'AesCtrBlockWork/EncryptBoundV1/LoopReference','AesCtrBlockWork/InverseLayoutCircuit','AesCtrBlockWork/EncryptBoundV1/Funs']]
 (HERE/'entry-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,kernel_endpoints=len(names),foundation_axioms_only=True,actual_complete_AES256_entry_numeric_model_agreement=True,actual_initial_layout_rounds_final_round_and_inverse=True,all_sixtyfour_input_bytes_unrestricted=True,arbitrary_fifteen_eight_word_keys=True,actual_generated_computational_bodies_unchanged=True,whole_crypto_value_model_assumed=False,Std_content_and_trusted_indexed_Zip_boundary_retained=True,model='EntryReference.finalWords with exact actual raw substitution and fixslice phases',actual_key_schedule_composition=False,model_to_compiled_encryption_circuit=False,full_CTR_stream_wrapper=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files},object_sha256={str(p.relative_to(ROOT)):sha(p)for p in objects}),indent=2)+'\n')
 print('PASS:4 foundational endpoints; complete actual AES256 entry -> raw fixslice model')
if __name__=='__main__':main()
