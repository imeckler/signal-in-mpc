#!/usr/bin/env python3
"""Compile joint-secret PQXDH + initial-ratchet field dependency, no openings."""
import hashlib,json,os,pathlib,shutil,subprocess,sys,time
ROOT=pathlib.Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ';stage=ROOT/'.deps/private-bootstrap-dh-native/v1-candidate-2';assert not stage.exists(),'preserve immutable candidate'
 stage.mkdir(parents=True)
 shutil.copytree(runtime/'Compiler',stage/'Compiler',ignore=shutil.ignore_patterns('__pycache__','*.pyc'));shutil.copy2(runtime/'compile.py',stage/'compile.py')
 for name in ['binary_io.py','field_dag.py','mixed.py']:
  target=stage/'handshake_backend'/name;target.parent.mkdir(exist_ok=True);shutil.copy2(ROOT/'handshake_backend'/name,target)
 source=stage/'Programs/Source/signal_bootstrap_dh.mpc';source.parent.mkdir(parents=True);shutil.copy2(ROOT/'programs/signal_bootstrap_dh.mpc',source)
 shutil.copyfile(ROOT/'.deps/relay-service-artifacts/x25519-field.json',stage/'field.json')
 pins={str(p.relative_to(stage)):sha(p)for p in stage.rglob('*')if p.is_file()}
 started=time.clock_gettime(time.CLOCK_MONOTONIC_RAW)
 with(stage/'compile.log').open('w')as log:
  cmd=[sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),'signal_bootstrap_dh',str(stage/'field.json')]
  child=subprocess.Popen(cmd,cwd=stage,env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1'),stdout=log,stderr=subprocess.STDOUT)
  print('bootstrap DH compiler pid='+str(child.pid),flush=True)
  try:code=child.wait(timeout=900)
  except subprocess.TimeoutExpired:child.kill();child.wait();raise
 report=dict(compiled=code==0,native_MPC=False,whole_bootstrap=False,parties_required=5,threshold_required=2,statistical_security=128,compiler_pid=child.pid,compile_exit_code=code,elapsed_seconds=time.clock_gettime(time.CLOCK_MONOTONIC_RAW)-started,source_integrity=all(sha(stage/n)==h for n,h in pins.items()),source_sha256=pins,stage=str(stage.relative_to(ROOT)))
 if code==0:
  manifest=stage/'dh.manifest';manifest.write_text(build(stage,['signal_private_bootstrap_dh_with_one_time-sbv:[1024x1]-sbv:[2304x1]']));report['manifest_sha256']=sha(manifest)
 (ROOT/'signal_backend/BootstrapWork/dh-compile-report.json').write_text(json.dumps(report,indent=2)+'\n')
 if code:raise SystemExit(code)
if __name__=='__main__':main()
