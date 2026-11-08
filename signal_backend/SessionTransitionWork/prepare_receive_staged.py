#!/usr/bin/env python3
"""Compile bounded independent receive stages; never repeat the monolithic build."""
import hashlib,json,os,shutil,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
HERE=Path(__file__).resolve().parent
runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ';stage=ROOT/'.deps/private-new-dh-staged-native';stage.mkdir(exist_ok=True)
for name,target in [('Compiler',runtime/'Compiler'),('handshake_backend',ROOT/'handshake_backend'),('backend_adapter',ROOT/'backend_adapter')]:
 link=stage/name
 if not link.exists():link.symlink_to(target,target_is_directory=True)
 else:assert link.resolve()==target.resolve()
shutil.copy2(runtime/'compile.py',stage/'compile.py');source=stage/'Programs/Source';source.mkdir(parents=True,exist_ok=True)
shutil.copy2(ROOT/'programs/signal_new_dh_stage.mpc',source/'signal_new_dh_stage.mpc')
sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
artifacts=[];descriptors=[]
shutil.copy2(HERE/'compile_diagnostic.py',stage/'compile_diagnostic.py')
for mode,n,m in [('summary',259,75),('crypto',1051,608)]:
 artifact=ROOT/f'.deps/private-hash-artifacts/private-new-dh-{mode}-256{("-5" if mode=="crypto" else "")}.json';artifacts.append(artifact)
 descriptor=f'signal_private_new_dh_{mode}_256_5-sbv:[{n*8}x1]-sbv:[{m*8}x1]';descriptors.append(descriptor)
 log=stage/f'{mode}-compile.log';pin=stage/f'{mode}.manifest';receipt=stage/f'{mode}-compile-receipt.json'
 expected=dict(source_sha256=sha(ROOT/'programs/signal_new_dh_stage.mpc'),artifact_sha256=sha(artifact))
 if receipt.exists():
  saved=json.loads(receipt.read_text());assert saved.get('completed') and all(saved[k]==v for k,v in expected.items())
  assert saved['manifest_sha256']==sha(pin) and pin.read_text()==build(stage,[descriptor])
  print(mode+' reused exact pinned completed stage',flush=True);continue
 with log.open('w')as out:
  subprocess.run([sys.executable,'-u','-B','compile_diagnostic.py','-M','-X','-P',str(2**255-19),'signal_new_dh_stage',mode,str(artifact)],cwd=stage,env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1'),stdout=out,stderr=subprocess.STDOUT,check=True,timeout=1800)
 pin.write_text(build(stage,[descriptor]));receipt.write_text(json.dumps(dict(expected,completed=True,manifest_sha256=sha(pin),log_sha256=sha(log)),indent=2)+'\n')
 print(mode+' compiled',flush=True)
 # Reuse exact already-compiled private computed-DH closure, not a new source build.
dh=ROOT/'.deps/private-dh-receive-native'
for folder in ['Bytecode','Schedules']:
 dest=stage/'Programs'/folder;dest.mkdir(exist_ok=True)
 for p in(dh/'Programs'/folder).iterdir():
  if p.is_file():
   target=dest/p.name
   if target.exists():assert target.read_bytes()==p.read_bytes()
   else:shutil.copy2(p,target)
descriptors.append('signal_private_dh_receive_candidate-sbv:[512x1]-sbv:[1024x1]')
manifest=stage/'receive.manifest';manifest.write_text(build(stage,descriptors))
sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
files=[Path(__file__),ROOT/'programs/signal_new_dh_stage.mpc',HERE/'NativeNewDhReceive.h',HERE/'NativeComputedDh.h',HERE/'compile_diagnostic.py']
report=dict(compile_passed=True,staged=True,parser_calls=1,crypto_calls=1,native_MPC_executed=False,full_actual_source_refinement=False,descriptors=descriptors,manifest_sha256=sha(manifest),artifact_sha256={p.name:sha(p)for p in artifacts},source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files})
(HERE/'staged-compile-report.json').write_text(json.dumps(report,indent=2)+'\n');print(manifest,flush=True)
