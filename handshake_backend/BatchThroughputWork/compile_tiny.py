#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,sys,time,resource
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).parent;STAGE=ROOT/'.deps/throughput-batch-tiny-v1'
if STAGE.exists():raise SystemExit('preserve existing tiny batch candidate')
STAGE.mkdir(parents=True)
runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ'
shutil.copytree(runtime/'Compiler',STAGE/'Compiler',ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
shutil.copytree(ROOT/'backend_adapter',STAGE/'backend_adapter',ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
(STAGE/'handshake_backend').mkdir();shutil.copy2(ROOT/'handshake_backend/binary_io.py',STAGE/'handshake_backend/binary_io.py')
shutil.copy2(runtime/'compile.py',STAGE/'compile.py');(STAGE/'Programs/Source').mkdir(parents=True)
shutil.copy2(WORK/'batch_tiny.mpc',STAGE/'Programs/Source/batch_tiny.mpc')
clock=lambda:time.clock_gettime(time.CLOCK_MONOTONIC_RAW)
profiles={}
for count in [1,2,4,8]:
 for mode in ['sequential','batch']:
  name=mode+'-'+str(count);started=clock()
  with (STAGE/(name+'.log')).open('w')as log:
   child=subprocess.Popen([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),'batch_tiny',mode,str(count)],cwd=STAGE,stdout=log,stderr=subprocess.STDOUT,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0'))
   print('compile '+name+' pid='+str(child.pid),flush=True);code=child.wait(timeout=120)
  if code:raise RuntimeError('tiny compile failed '+name)
  text=(STAGE/(name+'.log')).read_text()
  triples=int(re.search(r'(\d+) bit triples',text).group(1));rounds=int(re.search(r'(\d+) virtual machine rounds',text).group(1))
  profiles[name]={'bit_triples':triples,'VM_rounds':rounds,'compiler_elapsed_seconds':clock()-started,'pid':child.pid,'children_maxrss':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'log_sha256':hashlib.sha256(text.encode()).hexdigest()}
 for key in ['bit_triples']:
  assert profiles['sequential-'+str(count)][key]==profiles['batch-'+str(count)][key]
 assert profiles['batch-'+str(count)]['VM_rounds']==profiles['batch-1']['VM_rounds']
report={'passed':True,'profiles':profiles,'native_MPC_executed':False,'scope':'same Boolean DAG, sequential vs independent-instance packing; no mixedfield, store, TLS, or throughput claim','source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in [WORK/'batch_tiny.mpc',Path(__file__),ROOT/'backend_adapter/aig_batched.py']}}
(WORK/'compile-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(profiles,indent=2))
