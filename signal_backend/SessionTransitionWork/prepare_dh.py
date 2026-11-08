#!/usr/bin/env python3
"""Compile same-worker joint private DH candidate; no state acceptance claim."""
import hashlib,json,os,shutil,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ';stage=ROOT/'.deps/private-dh-receive-native';stage.mkdir(exist_ok=True)
for name,target in [('Compiler',runtime/'Compiler'),('handshake_backend',ROOT/'handshake_backend')]:
 link=stage/name
 if not link.exists():link.symlink_to(target,target_is_directory=True)
 else:assert link.resolve()==target.resolve()
shutil.copy2(runtime/'compile.py',stage/'compile.py');source=stage/'Programs/Source';source.mkdir(parents=True,exist_ok=True)
shutil.copy2(ROOT/'programs/signal_dh_receive_candidate.mpc',source/'signal_dh_receive_candidate.mpc')
artifact=ROOT/'.deps/relay-service-artifacts/x25519-field.json'
subprocess.run([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),'signal_dh_receive_candidate',str(artifact)],cwd=stage,env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1'),check=True,timeout=900)
manifest=stage/'dh.manifest';manifest.write_text(build(stage,['signal_private_dh_receive_candidate-sbv:[512x1]-sbv:[1024x1]']))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files=[Path(__file__),ROOT/'programs/signal_dh_receive_candidate.mpc',ROOT/'handshake_backend/mixed.py']
report=dict(candidate_only=True,actual_Signal_authentication_and_commit=False,native_MPC_executed=False,artifact_sha256=sha(artifact),manifest_sha256=sha(manifest),
 trust_boundary='Existing mixed-domain conversion/runtime and joint randomness. Actual parsed-point binding and cryptographic receive/commit composition pending.',source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files})
(Path(__file__).resolve().parent/'dh-compile-report.json').write_text(json.dumps(report,indent=2)+'\n');print(manifest,flush=True)
