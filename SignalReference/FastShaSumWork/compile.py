#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,sys
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).parent;BASE=ROOT/'.deps/tls-backend-diagnostic-programs';ARTIFACTS=ROOT/'.deps/sha-carry-save'
suffix='-singleton' if '--singleton' in sys.argv else ''
reports={}
for kind,profile in [(k,p) for k in ['legacy','carry'] for p in ['sum5','block-state']]:
 stage=ARTIFACTS/f'compile-{kind}-{profile}{suffix}'
 if stage.exists():raise SystemExit('preserve existing compiler closure')
 stage.mkdir();shutil.copytree(BASE/'Compiler',stage/'Compiler',ignore=shutil.ignore_patterns('__pycache__','*.pyc'));shutil.copy2(BASE/'compile.py',stage/'compile.py')
 shutil.copytree(ROOT/'backend_adapter',stage/'backend_adapter',ignore=shutil.ignore_patterns('__pycache__','*.pyc'));(stage/'handshake_backend').mkdir();shutil.copy2(ROOT/'handshake_backend/binary_io.py',stage/'handshake_backend/binary_io.py')
 for folder in ['Programs/Source','Programs/Bytecode','Programs/Schedules','Player-Data']:(stage/folder).mkdir(parents=True,exist_ok=True)
 shutil.copy2(WORK/'component.mpc',stage/'Programs/Source/count.mpc');artifact=ARTIFACTS/f'{kind}-{profile}.json';shutil.copy2(artifact,stage/'counter.json')
 command=[sys.executable,'-B','compile.py','-M','-B','64','count','counter.json',kind,profile]
 env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0');env.pop('PYTHONPATH',None);env.pop('PYTHONHOME',None)
 run=subprocess.run(command,cwd=stage,env=env,capture_output=True,text=True,check=True,timeout=120);(stage/'compile.log').write_text(run.stdout+run.stderr)
 triples=re.findall(r'(\d+) bit triples',run.stdout);rounds=re.findall(r'(\d+) virtual machine rounds',run.stdout)
 assert triples and rounds,run.stdout[-1500:]
 reports[kind+'-'+profile]=dict(command=command,bit_triples=int(triples[-1]),virtual_machine_rounds=int(rounds[-1]),source_product_sha256={str(p.relative_to(stage)):hashlib.sha256(p.read_bytes()).hexdigest() for p in stage.rglob('*') if p.is_file()},native_MPC_executed=False)
(WORK/('compile-report'+suffix+'.json')).write_text(json.dumps(reports,indent=2)+'\n');print(json.dumps({k:{a:v[a] for a in ['bit_triples','virtual_machine_rounds']} for k,v in reports.items()}))
