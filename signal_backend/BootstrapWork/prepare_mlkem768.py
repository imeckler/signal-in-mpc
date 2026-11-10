#!/usr/bin/env python3
"""Freeze/compile the explicit initial-SPQR ML-KEM768 keygen dependency, not a session."""
import argparse,collections,hashlib,json,os,pathlib,shutil,subprocess,sys,time
ROOT=pathlib.Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from SignalReference.MlKemWork.adapter import MlKem
from SignalReference.MlKemWork.artifacts import artifact_spec
from scripts.pin_tls_worker import build

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--compile',action='store_true');args=p.parse_args()
 runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ';stage=ROOT/'.deps/private-bootstrap-mlkem768-native/v1-candidate-1'
 assert not stage.exists(),'preserve immutable candidate; do not overwrite'
 registry=json.loads((ROOT/'SignalReference/MlKemWork/artifact-manifest.json').read_text())
 order=[];counts=collections.Counter();entries={};new_artifacts=[]
 def collect(key,bits):
  path,command,arguments=artifact_spec(key)
  registered=registry['artifacts'].get(str(path.relative_to(ROOT)))
  if registered is None:
   if not path.exists():
    assert command is not None,('missing component generator',key)
    print('generating public component',key,flush=True)
    with path.open('w')as out:
     subprocess.run([str(command),*arguments],stdout=out,check=True,timeout=600)
   from backend_adapter.boolean import load
   image=load(path);registered=dict(sha256=sha(path),input_bits=image['input_bits'],output_bits=len(image['outputs']));del image
   registry['artifacts'][str(path.relative_to(ROOT))]=registered
   new_artifacts.append(dict(key=list(key),artifact_sha256=registered['sha256'],generator_sha256=sha(command)if command else None))
  item=registered
  assert len(bits)==item['input_bits'];counts[key]+=1
  if key not in entries:
   assert path.is_file()and sha(path)==item['sha256'];order.append(key)
   entries[key]=(path,item)
  return [0]*item['output_bits']
 assert len(MlKem('mlkem768',collect,0,1).keygen([0]*512))==3585*8
 stage.mkdir(parents=True);(stage/'Artifacts').mkdir();pins={}
 for directory in ['Compiler']:
  shutil.copytree(runtime/directory,stage/directory,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
 for name in ['compile.py']:shutil.copy2(runtime/name,stage/name)
 for directory in ['backend_adapter']:
  shutil.copytree(ROOT/directory,stage/directory,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
 for name in ['handshake_backend/binary_io.py','SignalReference/MlKemWork/adapter.py','signal_backend/BootstrapWork/pinned_stages.py']:
  target=stage/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(ROOT/name,target)
 source=stage/'Programs/Source/signal_bootstrap_mlkem768_keygen.mpc';source.parent.mkdir(parents=True);shutil.copy2(ROOT/'programs/signal_bootstrap_mlkem768_keygen.mpc',source)
 rows=[]
 for index,key in enumerate(order):
  path,item=entries[key];name='Artifacts/'+item['sha256']+'.json';shutil.copyfile(path,stage/name)
  rows.append(dict(key=list(key),path=name,sha256=item['sha256'],input_bits=item['input_bits'],output_bits=item['output_bits'],function='signal_bootstrap_kem_component_'+str(index),calls=counts[key]))
 manifest=stage/'components.json';manifest.write_text(json.dumps(dict(format='signal-bootstrap-kem-stages-v1',variant='mlkem768',stages=rows),indent=2)+'\n')
 for path in stage.rglob('*'):
  if path.is_file():pins[str(path.relative_to(stage))]=sha(path)
 report=dict(prepared=True,compiled=False,native_MPC=False,fresh_session_initialized=False,stage=str(stage.relative_to(ROOT)),variant='initial SPQR ML-KEM768, raw standard keypair',statistical_security=128,component_calls=sum(counts.values()),unique_components=len(rows),input_bytes=1,output_bytes=3585,source_sha256=pins)
 report_path=ROOT/'signal_backend/BootstrapWork/mlkem768-compile-report.json';report['new_component_artifacts']=new_artifacts;report_path.write_text(json.dumps(report,indent=2)+'\n')
 print('prepared',len(rows),'component programs;',sum(counts.values()),'calls',flush=True)
 from signal_backend.BootstrapWork.check_mlkem768 import verify
 report['numeric_actual_libcrux']=verify(stage)
 report_path.write_text(json.dumps(report,indent=2)+'\n')
 if args.compile:
  started=time.monotonic()
  with(stage/'compile.log').open('w')as log:
   child=subprocess.Popen([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),'signal_bootstrap_mlkem768_keygen',str(manifest)],cwd=stage,env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1'),stdout=log,stderr=subprocess.STDOUT)
   print('ML-KEM768 compiler pid='+str(child.pid),flush=True)
   try:code=child.wait(timeout=1800)
   except subprocess.TimeoutExpired:child.kill();child.wait();raise
  report.update(compile_exit_code=code,compile_seconds=time.monotonic()-started)
  if code==0:
   output=stage/'kem.manifest';output.write_text(build(stage,['signal_private_bootstrap_mlkem768_keygen-sbv:[8x1]-sbv:[28680x1]']))
   report.update(compiled=True,manifest_sha256=sha(output))
  report['source_integrity']=all(sha(stage/name)==digest for name,digest in pins.items());report_path.write_text(json.dumps(report,indent=2)+'\n')
  if code:raise SystemExit(code)
if __name__=='__main__':main()
