#!/usr/bin/env python3
"""Compare pinned release / pristine local build / one-pass-order candidate."""
import hashlib,json,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2];KEY=HERE.parent/'KeyReferenceWork'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 label=sys.argv[1];assert label in ('release','baseline','candidate')
 binary=ROOT/'.deps/aeneas-2026-08-27/aeneas' if label=='release' else HERE/'Bin'/label
 inputs={'key':KEY/'Artifacts/key-step/selected.llbc','skip':KEY/'Artifacts/skip-step/selected.llbc','regressions':HERE/'Regressions/regressions.llbc','negative':HERE/'Regressions/negative.llbc'}
 root=HERE/'Trees'/label;root.mkdir(parents=True,exist_ok=True);results={}
 for profile,llbc in inputs.items():
  subdir='/SkipTranslatorWork/Generated/'+profile
  directory=root/subdir[1:]
  for old in directory.glob('*.lean'):old.unlink()
  command=[str(binary),'-backend','lean',str(llbc),'-dest',str(root),'-subdir',subdir,'-split-files','-namespace','LoopSupport'+profile.title(),'-warnings-as-errors','-no-progress-bar']
  run=subprocess.run(command,cwd=ROOT,capture_output=True,text=True)
  log=HERE/(label+'-'+profile+'.log');log.write_text(run.stdout+run.stderr)
  directory=root/subdir[1:];files={str(p.relative_to(root)):digest(p) for p in directory.glob('*.lean')}
  results[profile]={'input_sha256':digest(llbc),'exit_code':run.returncode,'generated_files':files,'log_sha256':digest(log),'diagnostics':[s for s in (run.stdout+run.stderr).splitlines() if 'Error' in s or 'Ignoring the body' in s]}
 report={'candidate_only':True,'label':label,'binary_sha256':digest(binary),'version':subprocess.check_output([str(binary),'-version'],text=True).strip(),'source_or_llbc_replacement':False,'profiles':results,'script_sha256':digest(Path(__file__))}
 (HERE/(label+'-comparison.json')).write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:{'exit_code':v['exit_code'],'generated_files':len(v['generated_files'])} for k,v in results.items()}),flush=True)
if __name__=='__main__':main()
