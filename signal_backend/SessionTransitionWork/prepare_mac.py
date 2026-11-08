#!/usr/bin/env python3
"""Build private-prefix Signal MAC kernel; no openings or acceptance claim."""
import hashlib,json,os,shutil,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
stage=ROOT/'.deps/private-message-mac-native';stage.mkdir(exist_ok=True)
runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ'
for name,target in [('Compiler',runtime/'Compiler'),('backend_adapter',ROOT/'backend_adapter'),('handshake_backend',ROOT/'handshake_backend')]:
 link=stage/name
 if not link.exists():link.symlink_to(target,target_is_directory=True)
 else:assert link.resolve()==target.resolve()
shutil.copy2(runtime/'compile.py',stage/'compile.py');source=stage/'Programs/Source';source.mkdir(parents=True,exist_ok=True)
shutil.copy2(ROOT/'programs/signal_private_message_mac.mpc',source/'signal_private_message_mac.mpc')
artifact=ROOT/'.deps/private-hash-artifacts/private-message-mac-256.json'
subprocess.run([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),'signal_private_message_mac',str(artifact)],cwd=stage,env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1'),check=True,timeout=300)
manifest=stage/'mac.manifest';manifest.write_text(build(stage,['signal_private_message_mac_256-sbv:[2840x1]-sbv:[8x1]']))
files=[Path(__file__),ROOT/'programs/signal_private_message_mac.mpc',ROOT/'SignalReference/PrivateMessageMacWork/Export.lean',ROOT/'TlsMpc/Signal/PrivateMessageMac.lean']
receipt={'artifact_sha256':hashlib.sha256(artifact.read_bytes()).hexdigest(),'manifest_sha256':hashlib.sha256(manifest.read_bytes()).hexdigest(),'native_executed':False,
 'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files}}
(stage/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
(Path(__file__).resolve().parent/'mac-compile-report.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(manifest,flush=True)
