#!/usr/bin/env python3
"""Baseline exact-output regression and unchanged full primitive input trials."""
import hashlib,json,subprocess,tempfile
from pathlib import Path
HERE=Path(__file__).resolve().parent;WORK=HERE.parent;ROOT=HERE.parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 build=json.loads((HERE/'build-report.json').read_text());assert build['exit_code']==0
 binary=ROOT/build['binary_path'];assert sha(binary)==build['binary_sha256']
 baseline=ROOT/'SignalReference/SealedSenderReferenceWork';inventory=json.loads((baseline/'Artifacts/EncryptWrapper/inventory.json').read_text())
 with tempfile.TemporaryDirectory(prefix='ss-default-regression-') as tmp:
  command=[str(binary),'-backend','lean',str(baseline/'Artifacts/EncryptWrapper/ss_wrapper.llbc'),'-dest',tmp,'-subdir','/SealedSenderReferenceWork/Generated/EncryptWrapper','-split-files','-namespace','SealedSenderReference','-warnings-as-errors','-no-progress-bar']
  p=subprocess.run(command,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);assert p.returncode==0,p.stdout
  matches={name:sha(Path(tmp)/name)==digest for name,digest in inventory['generated_files'].items()};assert all(matches.values())
 trials={}
 for profile in ['ctr_scoped','hmac_scoped']:
  llbc=WORK/'Artifacts'/profile/'ss_wrapper.llbc';directory=HERE/profile;directory.mkdir(exist_ok=True)
  command=[str(binary),'-backend','lean',str(llbc),'-dest',str(directory),'-subdir','/Generated','-split-files','-namespace','SealedSenderPrimitive','-warnings-as-errors','-no-progress-bar']
  p=subprocess.run(command,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(directory/'aeneas.log').write_text(p.stdout)
  assert 'update_array_default.matches_default_array' not in p.stdout
  trials[profile]={'unchanged_llbc_sha256':sha(llbc),'exit_code':p.returncode,'log_sha256':sha(directory/'aeneas.log'),'original_missing_declaration_failure_removed':True,'command':command}
 report={'candidate_only':True,'accepted_reference':False,'baseline_generated_exact_hash_matches':matches,'binary_sha256':sha(binary),'trials':trials,'patch_sha256':sha(HERE/'patch.diff'),'script_sha256':sha(Path(__file__))}
 (HERE/'check-report.json').write_text(json.dumps(report,indent=2)+'\n');print('Exact baseline regression passed; actual primitive trials recorded',flush=True)
if __name__=='__main__':main()
