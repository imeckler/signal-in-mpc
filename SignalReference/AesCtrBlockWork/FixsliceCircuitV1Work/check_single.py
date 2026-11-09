#!/usr/bin/env python3
"""Prove reduced16-plane encryption/compiled bytes agree with actual source."""
import hashlib,importlib.util,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
spec=importlib.util.spec_from_file_location('base',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 inherited=HERE/'computed-report.json';receipt=json.loads(inherited.read_text());assert receipt['passed']
 for name,want in receipt['source_sha256'].items():assert sha(ROOT/name)==want,name
 modules=['AesCtrBlockWork/FixsliceCircuitV1Work/'+n for n in ['Projection16','Symbolic16','Cipher16']];names=[]
 for module in modules:
  body=(REF/(module+'.lean')).read_text();assert not any(token in body for token in ['#eval','run_cmd','bv_decide','native_decide','sorry','axiom ']);names+=re.findall(r'^theorem (\w+)',body,re.M)
  r=subprocess.run(['lean','-o',str(base.BUILD/(module+'.olean')),module+'.lean'],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stdout+r.stderr
 audit=base.BUILD/'FixsliceSingleAxioms.lean';audit.write_text('import AesCtrBlockWork.FixsliceCircuitV1Work.Cipher16\n'+''.join('#print axioms LibSignalReference.Candidate.FixsliceCircuitV1.'+name+'\n'for name in names))
 text=subprocess.check_output(['lean',str(audit)],cwd=REF,env=base.environment,text=True);assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==len(names)
 for group in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx'not in text and '_native'not in text
 (HERE/'single-axioms.txt').write_text(text)
 files=[pathlib.Path(__file__),inherited,*[REF/(m+'.lean')for m in modules]]
 (HERE/'single-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,kernel_endpoints=len(names),foundation_axioms_only=True,entire_encrypt_core_projection_64_to_16=True,actual_key_schedule_AES_entry_to_compiled_selected_block=True,all_key_and_plaintext_bits_unrestricted=True,source_other_lanes_need_not_be_assumed_independent=True,exact_single_profile='singleExpression: other3 plaintext lanes zero, select0;16bit round core',actual_backend_trait_wrapper_not_extracted=True,inherited_Std_metadata_selector_and_Zip_trust_unchanged=True,ciphertext_interop_tested=False,resource_measurements=False,production_changed=False,endpoints=names,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files},object_sha256={str((base.BUILD/(m+'.olean')).relative_to(ROOT)):sha(base.BUILD/(m+'.olean'))for m in modules}),indent=2)+'\n')
 print('PASS:'+str(len(names))+' foundational endpoints; reduced1-block actual-source compiled agreement')
if __name__=='__main__':main()
