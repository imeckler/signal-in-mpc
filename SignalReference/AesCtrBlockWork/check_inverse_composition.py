#!/usr/bin/env python3
"""Full actual inverse source -> transpose/writeback model, not whole AES."""
import hashlib,importlib.util,json,pathlib,random,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parent;ROOT=REF.parent
spec=importlib.util.spec_from_file_location('base',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 # Rebuild actual source and inherited leaf closure with deterministic source replay.
 subprocess.run(['python3',str(HERE/'check_inverse.py')],check=True)
 for name in ['InverseWritebackLemmas','FactoredInverse']:
  target=base.BUILD/('AesCtrBlockWork/'+name+'.olean')
  r=subprocess.run(['lean','-o',str(target),'AesCtrBlockWork/'+name+'.lean'],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=60)
  assert r.returncode==0,r.stdout+r.stderr
 endpoints={
 'LibSignalReference.Candidate.AesInverseWriteback':['first_write','second_write','pair_write_input','input_range','input_all','pair_write_all','put_pair_0','put_pair_1','put_pair_2','put_pair_3'],
 'LibSignalReference.Candidate.AesInverseComposition':['writeAll_correct','factor_exact','actual_inverse']}
 audit=base.BUILD/'InverseCompositionAxioms.lean';audit.write_text('import AesCtrBlockWork.FactoredInverse\n'+''.join('#print axioms '+ns+'.'+name+'\n'for ns,names in endpoints.items()for name in names))
 text=subprocess.check_output(['lean',str(audit)],cwd=REF,env=base.environment,text=True)
 assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==13
 for group in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx'not in text and '_native'not in text
 binary=ROOT/'.deps/aes-std-borrow-oracle-target/debug/aes-std-borrow-oracle';built=json.loads((HERE/'ZipModelV1/oracle-build-report.json').read_text());assert sha(binary)==built['binary_sha256']
 rng=random.Random(20261110);cases=[]
 for bit in range(512):
  xs=[0]*8;xs[bit//64]=1<<(bit%64);cases.append(dict(mode='inverse',state=xs))
 cases += [dict(mode='inverse',state=[rng.getrandbits(64)for _ in range(8)])for _ in range(64)]
 cases += [dict(mode='inverse',state=[rng.getrandbits(64)for _ in range(n)])for n in range(17)if n!=8]
 data=''.join(json.dumps(c)+'\n'for c in cases)
 actual=subprocess.check_output([str(binary)],input=data,text=True)
 model=subprocess.check_output(['lean','--run','AesCtrBlockWork/InverseEvaluate.lean'],cwd=REF,env=base.environment,input=data,text=True,timeout=60)
 actual=[json.loads(x)for x in actual.splitlines()];model=[json.loads(x)for x in model.splitlines()];assert len(actual)==len(model)==len(cases)
 for i,(a,b)in enumerate(zip(actual,model)):assert a==b,(i,a,b)
 files=[pathlib.Path(__file__),HERE/'InverseWritebackLemmas.lean',HERE/'FactoredInverse.lean',HERE/'InverseEvaluate.lean',HERE/'inverse-source-report.json',HERE/'ZipModelV1/oracle-build-report.json']
 (HERE/'inverse-composition-axioms.txt').write_text(text)
 (HERE/'inverse-composition-report.json').write_text(json.dumps(dict(passed=True,candidate_only=True,kernel_endpoints=13,foundation_axioms_only=True,actual_complete_inverse_equality=True,actual_generated_body_edits=False,official_Std_content_bindings=6,public_actual_Rust_differential_cases=len(cases),whole_AES_CTR_refinement=False,model='AesLayout.transpose + exact inverse byte writeback',source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files},oracle_binary_sha256=sha(binary)),indent=2)+'\n')
 print('PASS: 13 foundational endpoints; complete actual inverse; '+str(len(cases))+' actual Rust public cases')
if __name__=='__main__':main()
