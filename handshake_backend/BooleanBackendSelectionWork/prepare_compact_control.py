#!/usr/bin/env python3
from pathlib import Path
import shutil,subprocess,sys,json,hashlib,os
root=Path(__file__).resolve().parents[2];work=Path(__file__).parent
stage=root/'.deps/compact-boolean-control-v1'
if stage.exists():raise SystemExit('preserve immutable control stage')
source=root/'.deps/sharing-refresh/MP-SPDZ';stage.mkdir()
shutil.copytree(source/'Compiler',stage/'Compiler',ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
shutil.copy2(source/'compile.py',stage/'compile.py');(stage/'Programs/Source').mkdir(parents=True)
shutil.copy2(work/'compact_control.mpc',stage/'Programs/Source/compact_control.mpc')
with (stage/'compile.log').open('w')as log:
 subprocess.run([sys.executable,'-B','compile.py','-M','-B','64','compact_control'],cwd=stage,stdout=log,stderr=subprocess.STDOUT,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0'),check=True,timeout=120)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
report={'native_executed':False,'compiler_security':40,'scope':'same synthetic binary bytecode; optional weaker n3/t1/S40 benchmark vs n5/t2/S128, not production replacement','sources':{str(p.relative_to(root)):sha(p)for p in [Path(__file__),work/'compact_control.mpc']},'products':{str(p.relative_to(stage)):sha(p)for p in stage.rglob('*')if p.is_file()and'Compiler'not in p.parts}}
(work/'compact-compile-report.json').write_text(json.dumps(report,indent=2)+'\n');print((stage/'compile.log').read_text()[-1000:])
