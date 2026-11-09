#!/usr/bin/env python3
"""Kernel-only exact source bitslice/inverse roundtrip under explicit Std models."""
import hashlib,importlib.util,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parent;ROOT=REF.parent
spec=importlib.util.spec_from_file_location('base',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 # Prerequisite actual source replay, proof compilation and Rust checks are an
 # independently retained checkpoint; do not silently change inherited sources.
 inherited=HERE/'inverse-composition-report.json';receipt=json.loads(inherited.read_text());assert receipt['passed']and receipt['actual_complete_inverse_equality']
 for name,want in receipt['source_sha256'].items():assert sha(ROOT/name)==want,name
 source_receipt=json.loads((HERE/'inverse-source-report.json').read_text())
 for name,want in source_receipt['source_sha256'].items():assert sha(ROOT/name)==want,name
 dep='LibSignalReference/Proofs/AesLayoutPermutation'
 r=subprocess.run(['lean','-o',str(base.BUILD/(dep+'.olean')),dep+'.lean'],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stdout+r.stderr
 module='AesCtrBlockWork/InverseLayoutCircuit';target=base.BUILD/(module+'.olean')
 r=subprocess.run(['lean','-o',str(target),module+'.lean'],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=90);assert r.returncode==0,r.stdout+r.stderr
 names=['words_ext','transpose_involution','write_read_bytes','inverse_network','actual_inverse_network','actual_bitslice_inverse']
 audit=base.BUILD/'InverseLayoutAxioms.lean';audit.write_text('import '+module.replace('/','.')+'\n'+''.join('#print axioms LibSignalReference.Candidate.AesInverseCircuit.'+name+'\n'for name in names))
 text=subprocess.check_output(['lean',str(audit)],cwd=REF,env=base.environment,text=True)
 assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==len(names)
 for group in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx'not in text and '_native'not in text
 (HERE/'inverse-layout-axioms.txt').write_text(text)
 files=[pathlib.Path(__file__),HERE/'InverseLayoutCircuit.lean',inherited,HERE/'inverse-source-report.json',REF/'LibSignalReference/Proofs/AesLayoutPermutation.lean']
 objects=[base.BUILD/(m+'.olean')for m in ['AesCtrBlockWork/FactoredInverse','AesCtrBlockWork/InverseWritebackLemmas','AesCtrBlockWork/InverseReference','LibSignalReference/Proofs/AesLayoutReference',dep,module]]
 (HERE/'inverse-layout-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,kernel_endpoints=len(names),foundation_axioms_only=True,all_512_input_bits_unrestricted=True,actual_bitslice_inverse_roundtrip=True,actual_functions_unchanged=True,whole_AES_CTR_refinement=False,Std_content_and_translator_boundary_retained=True,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files},object_sha256={str(p.relative_to(ROOT)):sha(p)for p in objects}),indent=2)+'\n')
 print('PASS:6 foundational endpoints; actual bitslice/inverse source roundtrip')
if __name__=='__main__':main()
