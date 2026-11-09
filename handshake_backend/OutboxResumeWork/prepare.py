#!/usr/bin/env python3
import hashlib,json,pathlib,shutil,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT));from scripts.pin_tls_worker import build
HERE=pathlib.Path(__file__).resolve().parent;stage=ROOT/'.deps/tls-outbox-remask-native/v1-candidate-1'
assert not stage.exists(),'preserve existing closure';stage.mkdir(parents=True)
base=ROOT/'.deps/private-record-binding-native/v1-candidate-1'
shutil.copytree(base/'Compiler',stage/'Compiler',ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
shutil.copytree(ROOT/'backend_adapter',stage/'backend_adapter',ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
(stage/'handshake_backend').mkdir();(stage/'handshake_backend/__init__.py').write_text('')
shutil.copyfile(ROOT/'handshake_backend/binary_io.py',stage/'handshake_backend/binary_io.py');shutil.copyfile(base/'compile.py',stage/'compile.py')
for d in ['Programs/Source','Worker-Public']:(stage/d).mkdir(parents=True)
shutil.copyfile(ROOT/'programs/tls_websocket_remask.mpc',stage/'Programs/Source/tls_websocket_remask.mpc')
image=stage/'Worker-Public/remask-1290.json';shutil.copyfile('/tmp/tls-remask-1290.json',image)
with (stage/'compile.log').open('w')as log:subprocess.run([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),'tls_websocket_remask','Worker-Public/remask-1290.json','1290'],cwd=stage,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=180)
manifest=stage/'remask.manifest';manifest.write_text(build(stage,['tls_binary_tls_websocket_remask_1290-sbv:[10352x1]-sbv:[10344x1]']))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r={'compiled':True,'native_mpc':False,'statistical_parameter':128,'fresh_joint_random_bits':32,'capacity':1290,'manifest_sha256':sha(manifest),'artifact_sha256':sha(image),'source_sha256':{str(p.relative_to(ROOT)):sha(p)for p in [ROOT/'TlsMpc/TlsWebSocketRemask.lean',HERE/'EmitRemask.lean',ROOT/'programs/tls_websocket_remask.mpc',ROOT/'backend_adapter/aig_packed.py',pathlib.Path(__file__)]}}
(HERE/'compile-report.json').write_text(json.dumps(r,indent=2)+'\n');print(manifest)
