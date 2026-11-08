#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
WORK=Path(__file__).parent;STAGE=ROOT/'.deps/throughput-batch-tiny-v1';MANIFEST=STAGE/'mixed.manifest'
if MANIFEST.exists():raise SystemExit('preserve existing mixed candidate')
for name in ['mixed.py','field_dag.py']:shutil.copy2(ROOT/'handshake_backend'/name,STAGE/'handshake_backend'/name)
shutil.copy2(WORK/'batch_mixed.mpc',STAGE/'Programs/Source/batch_mixed.mpc')
functions=[];profiles={}
for count in [2,4,8]:
 for name in ['random','compare']:
  ins,outs=(8,8*count)if name=='random'else(74*count,8)
  functions.append(f'tls_batch_{name}_{count}-sbv:[{ins}x1]-sbv:[{outs}x1]')
 for mode in ['sequential','batch']:
  label=mode+'-'+str(count)
  with (STAGE/('mixed-'+label+'.log')).open('w')as log:
   subprocess.run([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),'batch_mixed',mode,str(count)],cwd=STAGE,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=120,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
  import re
  text=(STAGE/('mixed-'+label+'.log')).read_text();profiles[label]={}
  for metric in ['bit triples','virtual machine rounds','integer dabits','integer triples']:
   found=re.search(r'(\d+) '+metric,text);profiles[label][metric]=int(found.group(1))if found else 0
  functions.append(f'tls_batch_mixed_{mode}_{count}-sbv:[{8*count}x1]-sbv:[{37*count}x1]')
 for metric in ['bit triples','integer dabits','integer triples']:assert profiles['sequential-'+str(count)][metric]==profiles['batch-'+str(count)][metric]
MANIFEST.write_text(build(STAGE,functions));(WORK/'mixed-compile-report.json').write_text(json.dumps({'passed':True,'native_MPC_executed':False,'profiles':profiles,'scope':'same checked scalar Fp square+17/conversion per instance then Boolean sequential/batch; fieldstage still serial; NOT full X25519/service cost','source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in [Path(__file__),WORK/'batch_mixed.mpc',ROOT/'handshake_backend/mixed.py']}},indent=2)+'\n');print(json.dumps(profiles,indent=2))
