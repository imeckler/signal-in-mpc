#!/usr/bin/env python3
"""Compile bounded parse-once receive with privately computed DH; no native execution claim."""
import hashlib,json,os,shutil,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ';stage=ROOT/'.deps/private-new-dh-receive-native';stage.mkdir(exist_ok=True)
for name,target in [('Compiler',runtime/'Compiler'),('handshake_backend',ROOT/'handshake_backend'),('backend_adapter',ROOT/'backend_adapter')]:
 link=stage/name
 if not link.exists():link.symlink_to(target,target_is_directory=True)
 else:assert link.resolve()==target.resolve()
shutil.copy2(runtime/'compile.py',stage/'compile.py');source=stage/'Programs/Source';source.mkdir(parents=True,exist_ok=True)
shutil.copy2(ROOT/'programs/signal_private_new_dh_receive.mpc',source/'signal_private_new_dh_receive.mpc')
artifact=ROOT/'.deps/relay-service-artifacts/x25519-field.json'
summary=ROOT/'.deps/private-hash-artifacts/private-new-dh-summary-256.json'
crypto=ROOT/'.deps/private-hash-artifacts/private-new-dh-crypto-256-5.json'
subprocess.run([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),'signal_private_new_dh_receive',str(artifact),str(summary),str(crypto)],cwd=stage,env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1'),check=True,timeout=900)
manifest=stage/'receive.manifest';manifest.write_text(build(stage,['signal_private_new_dh_receive_256_5-sbv:[6784x1]-sbv:[4864x1]']))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files=[Path(__file__),ROOT/'programs/signal_private_new_dh_receive.mpc',ROOT/'handshake_backend/mixed.py',ROOT/'signal_backend/SessionTransitionWork/NativeNewDhReceive.h']
report=dict(candidate_only=True,computed_model_authentication_and_state_selection=True,native_MPC_executed=False,artifact_sha256={p.name:sha(p)for p in [artifact,summary,crypto]},manifest_sha256=sha(manifest),
 trust_boundary='Existing mixed-domain conversion/runtime and joint randomness. Same parsed-point DH binding and computed MAC/PQ/CBC selector are wired; native interoperability and actual whole-source refinement remain pending.',source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files})
(Path(__file__).resolve().parent/'receive-compile-report.json').write_text(json.dumps(report,indent=2)+'\n');print(manifest,flush=True)
