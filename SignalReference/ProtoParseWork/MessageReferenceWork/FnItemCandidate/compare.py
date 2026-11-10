#!/usr/bin/env python3
import hashlib,json,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];REF=ROOT/'SignalReference'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 build=json.loads((HERE/'build-report.json').read_text());candidate=ROOT/build['binary_path'];assert sha(candidate)==build['binary_sha256'];rows=[]
 for profile in ['default','literal','negative']:
  src=HERE/'Regressions'/(profile+'.llbc')
  for name,binary in [('baseline',ROOT/'.deps/aeneas-2026-08-27/aeneas'),('candidate',candidate)]:
   folder=f'{name}_{profile}';out=HERE/'Generated'/folder;out.mkdir(parents=True,exist_ok=True);log=HERE/(folder+'.log')
   command=[str(binary),'-backend','lean',str(src),'-dest',str(REF),'-subdir','/ProtoParseWork/MessageReferenceWork/FnItemCandidate/Generated/'+folder,'-split-files','-namespace','FnItemRegression','-warnings-as-errors','-no-progress-bar','-print-error-emitters','-sequential']
   with log.open('w')as f:r=subprocess.run(command,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
   expected=0 if profile=='literal' or (name=='candidate' and profile=='default') else 2
   assert r.returncode==expected,(name,profile,r.returncode)
   rows.append({'profile':profile,'translator':name,'exit_code':r.returncode,'expected_exit_code':expected,'llbc_sha256':sha(src),'binary_sha256':sha(binary),'log_sha256':sha(log),'generated_sha256':{str(p.relative_to(ROOT)):sha(p)for p in out.glob('*.lean')},'command':command})
 (HERE/'comparison.json').write_text(json.dumps({'candidate_only':True,'accepted_translator':False,'script_sha256':sha(Path(__file__)),'rows':rows},indent=2)+'\n');print('Passed6translatorboundarycases')
if __name__=='__main__':main()
