#!/usr/bin/env python3
"""Explicit immutable throughput closure: gate-efficient single + bounded batch."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,time
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
from signal_backend.VariableServiceWork.shape import VariableShape
clock=lambda:time.clock_gettime(time.CLOCK_MONOTONIC_RAW)
def sha(path):
 h=hashlib.sha256()
 with path.open('rb')as f:
  for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()
def phase(command,cwd,log,timeout=2400):
 start=clock()
 with log.open('w')as output:
  child=subprocess.Popen(command,cwd=cwd,stdout=output,stderr=subprocess.STDOUT,env={k:v for k,v in dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1').items()if k not in ['PYTHONPATH','PYTHONHOME']})
  print('public phase '+log.name+' pid='+str(child.pid),flush=True)
  while True:
   pid,status,usage=os.wait4(child.pid,os.WNOHANG)
   if pid:break
   if clock()-start>timeout:
    child.kill();pid,status,usage=os.wait4(child.pid,0);child.returncode=os.waitstatus_to_exitcode(status);raise TimeoutError('public compile phase timeout')
   time.sleep(.2)
  child.returncode=os.waitstatus_to_exitcode(status)
 if child.returncode:raise subprocess.CalledProcessError(child.returncode,command)
 return {'command':list(map(str,command)),'pid':child.pid,'elapsed_seconds':clock()-start,'user_cpu_seconds':usage.ru_utime,'system_cpu_seconds':usage.ru_stime,'rusage_maxrss':usage.ru_maxrss,'rusage_scope':'phase child including waited descendants; maxrss platform units (bytes on Darwin)','log_sha256':sha(log)}
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('dimensions',nargs=4,type=int);ap.add_argument('--count',type=int,choices=[1,2,3,4],default=2);ap.add_argument('--sha-profile',choices=['reference','gate-efficient','latency'],default='gate-efficient');args=ap.parse_args()
 shape=VariableShape(*args.dimensions);label='-'.join(map(str,shape.values));single=ROOT/'.deps/private-variable-conversation-native'/label/('sha-'+args.sha_profile)
 stage=ROOT/'.deps/private-variable-conversation-native'/label/('batch-'+str(args.count)+'-sha-'+args.sha_profile)
 if stage.exists():raise SystemExit('preserve existing batch candidate, including failed build')
 stage.mkdir(parents=True);phases=[]
 if not(single/'service.manifest').exists():
  phases.append(phase([sys.executable,'-u',str(ROOT/'signal_backend/VariableServiceWork/prepare.py'),*map(str,shape.values),'--sha-profile',args.sha_profile],ROOT,stage/'single-prepare.log'))
 # Validate exact source-closure products, then copy public immutable compilation.
 for line in (single/'service.manifest').read_text().splitlines()[1:]:
  expected,name=line.split(' ',1);assert sha(single/name)==expected
 for directory in ['Compiler','backend_adapter','handshake_backend','signal_backend','Programs','Worker-Public']:
  shutil.copytree(single/directory,stage/directory,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
 shutil.copy2(single/'compile.py',stage/'compile.py')
 # This explicit candidate requires the tested batching adapter, never silently
 # substituting a newer mutable backend for an old copied closure.
 assert sha(stage/'backend_adapter/aig_batched.py')==sha(ROOT/'backend_adapter/aig_batched.py')
 shutil.copy2(ROOT/'programs/signal_variable_service_batch.mpc',stage/'Programs/Source/signal_variable_service_batch.mpc')
 sources={str(p.relative_to(stage)):sha(p)for folder in ['Compiler','backend_adapter','handshake_backend','signal_backend','Programs/Source']for p in (stage/folder).rglob('*')if p.is_file()and p.suffix in ['.py','.mpc']}
 command=[sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),'signal_variable_service_batch','Worker-Public/x25519-field.json','Worker-Public/service.json',*map(str,shape.values),args.sha_profile,str(args.count)]
 host_paths=[ROOT/'handshake_backend/NativeSession.h',ROOT/'handshake_backend/BatchThroughputWork/NativeBatchService.h',*[p for p in (ROOT/'handshake_backend/WebSocketWork').glob('*.h')],*[p for p in (ROOT/'signal_backend/VariableServiceWork').glob('*.h')]]
 host_identity={str(p.relative_to(ROOT)):sha(p)for p in host_paths}
 phases.append(phase(command,stage,stage/'batch-compile.log'))
 assert all(sha(ROOT/name)==value for name,value in host_identity.items()),'host batch interface changed during compile'
 assert all(sha(stage/name)==value for name,value in sources.items())
 name='signal_private_variable_batch_'+str(args.count)+'_'+shape.name
 descriptor=name+'-sbv:['+str(shape.input_bytes*8*args.count)+'x1]-sbv:['+str(shape.output_bytes*8*args.count)+'x1]'
 metadata={'sha_profile':args.sha_profile,'batch_count':args.count,'independent_same_shape_inputs':True,'single_manifest_sha256':sha(single/'service.manifest'),'source_sha256':sources,'expected_native_host_source_sha256':host_identity,'boolean_artifact_sha256':sha(stage/'Worker-Public/service.json'),'field_artifact_sha256':sha(stage/'Worker-Public/x25519-field.json')}
 (stage/'Worker-Public/batch-profile.json').write_text(json.dumps(metadata,sort_keys=True,separators=(',',':'))+'\n')
 manifest=stage/'service.manifest';manifest.write_text(build(stage,[shape.descriptor,descriptor],['Worker-Public/profile.json','Worker-Public/batch-profile.json']))
 receipt={'passed':True,'native_MPC_executed':False,'shape':shape.values,'batch_count':args.count,'sha_profile':args.sha_profile,'manifest_sha256':sha(manifest),'phases':phases,'source_sha256':sources,'expected_native_host_source_sha256':host_identity,'scope':'Single and batched same-profile mixed closure; scalar DH/conversion still serial; no private store/TLS/runtime proof or throughput claim.'}
 (stage/'build-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(manifest,flush=True)
if __name__=='__main__':main()
