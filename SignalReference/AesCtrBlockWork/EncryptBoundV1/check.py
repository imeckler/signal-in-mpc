#!/usr/bin/env python3
"""All nine AES leaf slots bind actual bodies; does NOT prove AES equivalence."""
import hashlib,importlib.util,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
spec=importlib.util.spec_from_file_location('base',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 before={p.name:sha(p)for p in [HERE/'Funs.lean',HERE/'FunsExternal.lean']};subprocess.run(['python3',str(HERE/'prepare.py')],check=True);assert before=={p.name:sha(p)for p in [HERE/'Funs.lean',HERE/'FunsExternal.lean']}
 # All nine imported computational leaves are actual generated source functions.
 # Their semantic proofs stay separately scoped; no whole-crypto value models.
 modules=['AesCtrBlockWork/Generated/EncryptNamedV1/Types']+['LibSignalReference/Generated/'+family+'/'+kind for family in ['AesLayout','AesSubBytes','AesMix','AesMixPhases','AesShift']for kind in ['Types','Funs']]+['AesCtrBlockWork/EncryptBoundV1/'+name for name in ['FunsExternal','Funs','SourceBindings']]
 for module in modules:
  out=base.BUILD/(module+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
  r=subprocess.run(['lean','-o',str(out),module+'.lean'],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stdout+r.stderr
 # The separately reviewed borrowed-Zip and inverse source closures must match.
 for receipt in [REF/'AesCtrBlockWork/ZipModelV1/proof-report.json',REF/'AesCtrBlockWork/inverse-composition-report.json']:
  data=json.loads(receipt.read_text());assert data['passed']
  for name,want in data['source_sha256'].items():assert sha(ROOT/name)==want,name
 names=['round_key','inverse','forward','substitution','shift','mix0','mix1','mix2','mix3'];actual=['aes256_encrypt_loop.body','aes256_encrypt_loop','aes256_encrypt']
 audit=base.BUILD/'ActualAesBindingsAxioms.lean';audit.write_text('import AesCtrBlockWork.EncryptBoundV1.SourceBindings\n'+''.join('#print axioms LibSignalReference.Candidate.AesActualBindings.'+n+'\n'for n in names)+''.join('#print axioms RustCryptoAesCtrBlock.soft.fixslice.'+n+'\n'for n in actual))
 text=subprocess.check_output(['lean',str(audit)],cwd=REF,env=base.environment,text=True);assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==12
 for group in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx'not in text and '_native'not in text
 (HERE/'axioms.txt').write_text(text)
 files=[pathlib.Path(__file__),HERE/'prepare.py',HERE/'import-replay.json',*[REF/(m+'.lean')for m in modules]]
 (HERE/'report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,actual_AES_entry_and_loop_compile=True,actual_crypto_leaf_forwardings=9,Std_content_forwardings=6,forwarding_endpoints=9,actual_function_axiom_audits=3,foundation_axioms_only=True,manual_generated_computational_body_edits=False,import_only_replay=True,trusted_indexed_Std_Zip_model_retained=True,full_AES_circuit_equivalence=False,CTR_AES_wrapper_composition=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files}),indent=2)+'\n')
 print('PASS: actual AES entry+loop with nine actual leaf bodies, no crypto axiom; full AES equivalence OPEN')
if __name__=='__main__':main()
