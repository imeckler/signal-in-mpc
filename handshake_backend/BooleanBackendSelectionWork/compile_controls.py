#!/usr/bin/env python3
import pathlib,shutil,subprocess,sys,os,re,json,hashlib,time
root=pathlib.Path(__file__).resolve().parents[2];work=pathlib.Path(__file__).parent
stage=root/'.deps/boolean-depth20-controls-v1'
if stage.exists():raise SystemExit('immutable stage already exists')
runtime=root/'.deps/sharing-refresh/MP-SPDZ';stage.mkdir()
for name in ['Compiler']:
 shutil.copytree(runtime/name,stage/name,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
shutil.copytree(root/'backend_adapter',stage/'backend_adapter',ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
(stage/'handshake_backend').mkdir();shutil.copy2(root/'handshake_backend/binary_io.py',stage/'handshake_backend/binary_io.py')
shutil.copy2(runtime/'compile.py',stage/'compile.py');(stage/'Programs/Source').mkdir(parents=True)
shutil.copy2(work/'depth20.mpc',stage/'Programs/Source/depth20.mpc')
profiles={};clock=lambda:time.clock_gettime(time.CLOCK_MONOTONIC_RAW)
for width in [8,64,1024]:
 for mode in ['field','boolean']:
  name=f'{mode}-{width}';start=clock()
  with (stage/(name+'.log')).open('w') as log:
   p=subprocess.Popen([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),'depth20',mode,str(width)],cwd=stage,stdout=log,stderr=subprocess.STDOUT,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0'))
   print(name+' pid='+str(p.pid),flush=True);rc=p.wait(timeout=120)
  if rc:raise RuntimeError('control compilation failed '+name)
  text=(stage/(name+'.log')).read_text();pattern=r'(\d+) '+('integer triples'if mode=='field'else'bit triples')
  count=int(re.search(pattern,text).group(1));assert count==width*20,(name,count)
  rounds=int(re.search(r'(\d+) virtual machine rounds',text).group(1));assert rounds==20,(name,rounds)
  profiles[name]={'multiplications':count,'VM_rounds':rounds,'elapsed_seconds':clock()-start,'log_sha256':hashlib.sha256(text.encode()).hexdigest()}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
report={'passed':True,'statistical_security':128,'arithmetic_prime':str(2**255-19),'native_MPC_executed':False,'scope':'depth20 same-count scalar field versus Boolean controls; no LN17 timing reproduction or throughput claim','profiles':profiles,'sources':{str(p.relative_to(root)):sha(p)for p in [pathlib.Path(__file__),work/'depth20.mpc',root/'backend_adapter/aig_packed.py']},'products':{str(p.relative_to(stage)):sha(p)for sub in ['Functions','Bytecode','Schedules']for p in sorted((stage/'Programs'/sub).glob('*'))if p.is_file()}}
(work/'control-compile-report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS six exact depth20/count controls')
