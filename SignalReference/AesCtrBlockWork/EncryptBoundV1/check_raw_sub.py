#!/usr/bin/env python3
"""Exact actual raw S-box gate/word semantics, without restoring omitted NOTs."""
import hashlib,importlib.util,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
spec=importlib.util.spec_from_file_location('base',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 inherited=HERE/'report.json';receipt=json.loads(inherited.read_text());assert receipt['passed']
 for name,want in receipt['source_sha256'].items():assert sha(ROOT/name)==want,name
 modules=['LibSignalReference/Proofs/AesNetwork','AesCtrBlockWork/EncryptBoundV1/RawSubReference']
 for module in modules:
  out=base.BUILD/(module+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
  r=subprocess.run(['lean','-o',str(out),module+'.lean'],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stdout+r.stderr
 names=['actual_raw','wordHom','rawRun_map','output_value','wordsFromList_list','rawWords_list','output_words','actual_words','rejects_bad_length']
 audit=base.BUILD/'ActualRawSubAxioms.lean';audit.write_text('import AesCtrBlockWork.EncryptBoundV1.RawSubReference\n'+''.join('#print axioms LibSignalReference.Candidate.AesRawSub.'+name+'\n'for name in names))
 text=subprocess.check_output(['lean',str(audit)],cwd=REF,env=base.environment,text=True);assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==len(names)
 for group in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx'not in text and '_native'not in text
 (HERE/'raw-sub-axioms.txt').write_text(text)
 files=[pathlib.Path(__file__),HERE/'RawSubReference.lean',inherited,*[REF/(module+'.lean')for module in modules]]
 (HERE/'raw-sub-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,kernel_endpoints=len(names),foundation_axioms_only=True,actual_raw_sub_bytes_gate_and_word_agreement=True,all_eight_u64_inputs_unrestricted=True,actual_not_operations_not_restored=True,rejects_wrong_length_before_reads=True,actual_function_body_unchanged=True,whole_AES_CTR_refinement=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files}),indent=2)+'\n')
 print('PASS:9 foundational endpoints; actual raw substitution gate/word agreement')
if __name__=='__main__':main()
