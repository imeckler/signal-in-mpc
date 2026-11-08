#!/usr/bin/env python3
from pathlib import Path
import os,shutil,subprocess,sys
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
WORK=Path(__file__).parent;STAGE=ROOT/'.deps/throughput-batch-tiny-v1'
manifest=STAGE/'batch.manifest'
if manifest.exists():raise SystemExit('preserve existing native batch closure')
shutil.copy2(WORK/'batch_helpers.mpc',STAGE/'Programs/Source/batch_helpers.mpc')
functions=[]
for count in [2,4,8]:
 with (STAGE/('helpers-'+str(count)+'.log')).open('w')as log:
  subprocess.run([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),'batch_helpers',str(count)],cwd=STAGE,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=120,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
 functions += [f'tls_batch_random_{count}-sbv:[8x1]-sbv:[{8*count}x1]',f'tls_batch_compare_{count}-sbv:[{74*count}x1]-sbv:[8x1]']
 for mode in ['sequential','batch']:functions.append(f'tls_batch_tiny_{mode}_{count}-sbv:[{8*count}x1]-sbv:[{37*count}x1]')
manifest.write_text(build(STAGE,functions));print(manifest)
