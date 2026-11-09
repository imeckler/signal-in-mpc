#!/usr/bin/env python3
"""Recheck the inherited actual key-schedule proof for this new composition.
No exports/fixtures, no canonical model or historical receipt mutations.
"""
import hashlib,importlib.util,json,pathlib,re,subprocess,sys,tempfile
HERE=pathlib.Path(__file__).resolve().parent;REF=HERE.parents[1];ROOT=REF.parent
sys.path.insert(0,str(REF));sys.path.insert(0,str(ROOT))
from AesKeyScheduleLeavesWork.check import audit_reference
from extract import PINS,check_sources
spec=importlib.util.spec_from_file_location('base',REF/'CtrReferenceV1Work/check_conversion.py');base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 check_sources();reference=audit_reference();order=[];sources={};root_sources={}
 def visit(module):
  rel=module.replace('.','/')+'.lean'
  if module.startswith('TlsMpc'):path=ROOT/rel;dest=root_sources
  elif module.startswith(('LibSignalReference','AesKeySchedule')):path=REF/rel;dest=sources
  else:return
  if rel in dest:return
  dest[rel]=sha(path)
  for imported in re.findall(r'^import ([A-Za-z0-9_.]+)',path.read_text(),re.M):visit(imported)
  if dest is sources:order.append(module.replace('.','/'))
 visit('AesKeyScheduleWork.FullSchedule')
 print('key schedule source closure: '+str(len(order))+' reference modules',flush=True)
 # Replay only the already scoped exact unused-metadata selector and translator.
 selected=REF/'AesKeyScheduleWork/selected.llbc';binary=(REF/PINS['aeneas']['directory']/'aeneas').resolve()
 with tempfile.TemporaryDirectory(prefix='fixslice-key-source-')as tmp:
  tmp=pathlib.Path(tmp)
  r=subprocess.run([str(binary),'-backend','lean',str(selected),'-dest',str(tmp),'-subdir','/AesKeyScheduleWork/Generated','-split-files','-namespace','RustCryptoAesKeySchedule','-warnings-as-errors','-no-progress-bar'],cwd=ROOT,capture_output=True,text=True,timeout=60)
  assert r.returncode==0,r.stdout+r.stderr
  for name in ['Funs.lean','Types.lean']:assert(tmp/'AesKeyScheduleWork/Generated'/name).read_bytes()==(REF/'AesKeyScheduleWork/Generated'/name).read_bytes()
 reused=[]
 prior_path=REF/'AesCtrBlockWork/inverse-layout-report.json';prior=json.loads(prior_path.read_text())
 for module in order:
  if module=='LibSignalReference/Proofs/AesLayoutPermutation':
   source=REF/(module+'.lean');obj=base.BUILD/(module+'.olean')
   assert sha(source)==prior['source_sha256'][str(source.relative_to(ROOT))]
   assert sha(obj)==prior['object_sha256'][str(obj.relative_to(ROOT))]
   reused.append(dict(module=module,receipt=str(prior_path.relative_to(ROOT)),receipt_sha256=sha(prior_path),source_sha256=sha(source),object_sha256=sha(obj)))
   print(module+' exact previously audited source/object reused',flush=True)
   continue
  print(module,flush=True);out=base.BUILD/(module+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
  r=subprocess.run(['lean','-o',str(out),module+'.lean'],cwd=REF,env=base.environment,capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stdout+r.stderr
 audit=base.BUILD/'FixsliceKeyScheduleAxioms.lean';names=['key_schedule_spec','key_schedule_all_arrays','key_schedule_refines_artifact']
 audit.write_text('import AesKeyScheduleWork.FullSchedule\n'+''.join('#print axioms LibSignalReference.Candidate.AesKeySchedule.'+n+'\n'for n in names))
 text=subprocess.check_output(['lean',str(audit)],cwd=REF,env=base.environment,text=True);assert text.count('depends on axioms:')+text.count('does not depend on any axioms')==len(names)
 for group in re.findall(r'depends on axioms: \[(.*?)\]',text,re.S):assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx'not in text and '_native'not in text
 for rel,want in sources.items():assert sha(REF/rel)==want,rel
 for rel,want in root_sources.items():assert sha(ROOT/rel)==want,rel
 (HERE/'key-schedule-axioms.txt').write_text(text)
 (HERE/'key-schedule-recheck.json').write_text(json.dumps(dict(passed=True,candidate_only=True,kernel_endpoints=3,foundation_axioms_only=True,unchanged_actual_generated_files_replayed=True,Std_models_unchanged=True,inherited_metadata_selection_trusted_not_mechanized=True,source_reference=reference,exact_cached_dependencies=reused,source_sha256={**{str((REF/rel).relative_to(ROOT)):value for rel,value in sources.items()},**root_sources,str(pathlib.Path(__file__).relative_to(ROOT)):sha(pathlib.Path(__file__))},object_sha256={str((base.BUILD/(m+'.olean')).relative_to(ROOT)):sha(base.BUILD/(m+'.olean'))for m in order}),indent=2)+'\n')
 print('PASS: actual full key-schedule source replay/closure +3 foundational endpoints',flush=True)
if __name__=='__main__':main()
