#!/usr/bin/env python3
import hashlib,importlib.util,json,os,re,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];REF=ROOT/'SignalReference';KEY=REF/'ProtoParseWork/KeyReferenceWork'
sys.path.insert(0,str(KEY));spec=importlib.util.spec_from_file_location('accepted_key_check',KEY/'check.py');key=importlib.util.module_from_spec(spec);spec.loader.exec_module(key)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 e=key.env();e['LEAN_PATH']=str(HERE/'Build')+os.pathsep+e['LEAN_PATH'];modules=[]
 for profile in ['default','literal']:
  for name in ['Types','FunsExternal','Funs']:
   module='ProtoParseWork.MessageReferenceWork.FnItemCandidate.Generated.candidate_'+profile+'.'+name
   src=HERE/'Generated'/('candidate_'+profile)/(name+'.lean');cwd=REF
   if name=='FunsExternal':src=HERE/'Modules'/(module.replace('.','/')+'.lean');cwd=HERE/'Modules'
   if src.exists():modules.append((module,src,cwd))
  modules.append((profile.title()+'Proof',HERE/'Modules'/(profile.title()+'Proof.lean'),HERE/'Modules'))
 output=''
 for module,src,cwd in modules:
  target=HERE/'Build'/(module.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
  run=subprocess.run(['lean','-o',str(target),str(src)],cwd=cwd,env=e,capture_output=True,text=True);output+=run.stdout+run.stderr
  (HERE/'regression-axioms.txt').write_text(output)
  run.check_returncode()
 (HERE/'regression-axioms.txt').write_text(output)
 entries=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",output,re.S);assert len(entries)==5,len(entries)
 for name,axs in entries:assert {a.strip()for a in axs.split(',')if a.strip()}<={'propext','Classical.choice','Quot.sound'},(name,axs)
 (HERE/'regression-proof-report.json').write_text(json.dumps({'candidate_only':True,'accepted_translator':False,'checked_endpoints':5,'all_compile':True,'axiom_log_sha256':sha(HERE/'regression-axioms.txt'),'sources':{str(p.relative_to(ROOT)):sha(p)for _,p,_ in modules},'objects':{str(p.relative_to(ROOT)):sha(p)for p in sorted((HERE/'Build').rglob('*.olean'))},'scope':'Actual synthetic zero-input default function item and unchanged literal-item path; local default FnOnce result model. Not a whole translator correctness proof.'},indent=2)+'\n');print('5kernelregressionendpoints passed')
if __name__=='__main__':main()
