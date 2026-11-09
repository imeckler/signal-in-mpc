#!/usr/bin/env python3
"""Actual AES round loop -> raw fixslice word model, not ordinary AES yet."""
import hashlib,importlib.util,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
spec=importlib.util.spec_from_file_location('base',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 receipts=[HERE/'report.json',HERE/'raw-sub-report.json']
 for receipt in receipts:
  data=json.loads(receipt.read_text());assert data['passed']
  for name,want in data['source_sha256'].items():assert sha(ROOT/name)==want,name
 modules=['LibSignalReference/Proofs/AesLinearReference','LibSignalReference/Proofs/AesMixPhaseReference','LibSignalReference/Proofs/AesShiftReference']+['AesCtrBlockWork/EncryptBoundV1/'+name for name in ['RoundModel','KeyRanges','LoopReference']]
 for module in modules:
  out=base.BUILD/(module+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
  r=subprocess.run(['lean','-o',str(out),module+'.lean'],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stdout+r.stderr
 endpoints={
 'AesRoundModel':['subArray_reference','scalar_xor','key_reference','mix0_reference','mix1_reference','mix2_reference','mix3_reference'],
 'AesKeyRanges':['key_range','add8','source_range'],
 'AesLoopReference':['body0','body1','body2','body3','loop_reference']}
 audit=base.BUILD/'ActualAesRoundAxioms.lean';audit.write_text('import AesCtrBlockWork.EncryptBoundV1.LoopReference\n'+''.join('#print axioms LibSignalReference.Candidate.'+ns+'.'+name+'\n'for ns,names in endpoints.items()for name in names))
 text=subprocess.check_output(['lean',str(audit)],cwd=REF,env=base.environment,text=True);assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==15
 for group in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx'not in text and '_native'not in text
 (HERE/'rounds-axioms.txt').write_text(text)
 files=[pathlib.Path(__file__),*receipts,*[REF/(module+'.lean')for module in modules]]
 objects=[base.BUILD/(module+'.olean')for module in modules+['AesCtrBlockWork/EncryptBoundV1/RawSubReference','AesCtrBlockWork/ZipModelV1/RoundKeyReference']]
 (HERE/'rounds-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,kernel_endpoints=15,foundation_axioms_only=True,actual_four_iteration_round_loop=True,actual_loop_termination_and_full_state_result=True,actual_checked_additions_and_key_ranges=True,arbitrary_eight_word_state=True,arbitrary_fifteen_eight_word_round_keys=True,raw_substitution_NOTs_not_restored=True,generated_body_edits=False,Std_content_and_trusted_indexed_Zip_boundary_retained=True,ordinary_AES_key_compensation_and_CTR_wrapper=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files},object_sha256={str(p.relative_to(ROOT)):sha(p)for p in objects}),indent=2)+'\n')
 print('PASS:15 foundational endpoints; actual four-iteration AES loop vs raw fixslice model')
if __name__=='__main__':main()
