#!/usr/bin/env python3
"""Full actual inv_bitslice compilation/source leaves; whole inverse equality OPEN."""
import hashlib,importlib.util,json,pathlib,re,subprocess,tempfile
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parent;ROOT=REF.parent
spec=importlib.util.spec_from_file_location('base',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 art=HERE/'Artifacts/InvBitsliceContentV1';gen=HERE/'Generated/InvBitsliceNamedV1';report=json.loads((art/'report.json').read_text());assert report['charon_exit_code']==0 and not report['has_errors']and sha(art/'aes.llbc')==report['llbc_sha256']
 pins=json.loads((REF/'pins.json').read_text());a=(REF/pins['aeneas']['directory']/'aeneas').resolve()
 with tempfile.TemporaryDirectory(prefix='aes-inverse-replay-')as tmp:
  tmp=pathlib.Path(tmp);named=tmp/'named.llbc';subprocess.run(['python3',str(REF/'CtrReferenceV1Work/replay_mono_names.py'),str(art/'aes.llbc'),str(named)],check=True,capture_output=True);assert named.read_bytes()==(art/'named.llbc').read_bytes()
  args=[str(a),'-backend','lean',str(named),'-dest',str(tmp),'-subdir','/AesCtrBlockWork/Generated/InvBitsliceNamedV1','-split-files','-namespace','RustCryptoAesCtrInverse','-warnings-as-errors','-no-progress-bar'];r=subprocess.run(args,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stdout+r.stderr
  for name in ['Types.lean','Funs.lean','FunsExternal_Template.lean','TypesExternal_Template.lean']:assert(tmp/'AesCtrBlockWork/Generated/InvBitsliceNamedV1'/name).read_bytes()==(gen/name).read_bytes()
 before=[sha(gen/n)for n in ['FunsExternal.lean','TypesExternal.lean']];subprocess.run(['python3',str(HERE/'bind_inverse_models.py')],check=True);assert before==[sha(gen/n)for n in ['FunsExternal.lean','TypesExternal.lean']]
 modules=['LibSignalReference/Generated/AesLayout/Types','LibSignalReference/Generated/AesLayout/Funs','LibSignalReference/Proofs/AesLayoutReference','LibSignalReference/Generated/AesInverseWrite/Types','LibSignalReference/Generated/AesInverseWrite/Funs','LibSignalReference/Proofs/AesInverseWrite']+['AesCtrBlockWork/'+n for n in ['Generated/InvBitsliceNamedV1/TypesExternal','Generated/InvBitsliceNamedV1/Types','Generated/InvBitsliceNamedV1/FunsExternal','Generated/InvBitsliceNamedV1/Funs','InverseReference']]
 for module in modules:
  target=base.BUILD/(module+'.olean');target.parent.mkdir(parents=True,exist_ok=True);r=subprocess.run(['lean','-o',str(target),str(REF/(module+'.lean'))],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stdout+r.stderr
 names=['delta_source_same','write_source_same','delta_refines','write_refines','rejects_bad_length','default_batch'];audit=base.BUILD/'InverseSourceAxioms.lean';audit.write_text('import AesCtrBlockWork.InverseReference\n'+''.join('#print axioms LibSignalReference.Candidate.AesCtrInverse.'+n+'\n'for n in names)+'#print axioms RustCryptoAesCtrInverse.soft.fixslice.inv_bitslice\n')
 text=subprocess.check_output(['lean',str(audit)],cwd=REF,env=base.environment,text=True);assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==len(names)+1
 for group in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx'not in text and '_native'not in text
 files=[pathlib.Path(__file__),HERE/'bind_inverse_models.py',*gen.glob('*.lean'),*[REF/(m+'.lean')for m in modules],art/'report.json',art/'aes.llbc',art/'named.llbc']
 (HERE/'inverse-source-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,actual_complete_inverse_body_compiles=True,manual_generated_body_edits=False,source_leaf_equivalences=True,kernel_endpoints=len(names),actual_function_axioms_audited=True,foundation_axioms_only=True,official_Std_content_bindings=6,whole_inverse_numeric_equality=False,whole_AES_CTR_refinement=False,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files}),indent=2)+'\n');print('PASS complete actual inverse body +6 source/bound endpoints; whole inverse numeric equality OPEN')
if __name__=='__main__':main()
