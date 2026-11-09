#!/usr/bin/env python3
import hashlib,json,os,pathlib,shutil,subprocess,sys,time
ROOT=pathlib.Path(__file__).resolve().parents[3];HERE=pathlib.Path(__file__).resolve().parent;sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build

def main():
 stage=ROOT/'.deps/private-reusable-outbox-native/v1-candidate-1';assert not stage.exists();stage.mkdir(parents=True);runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ';sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 for name,path in [('Compiler',runtime/'Compiler'),('backend_adapter',ROOT/'backend_adapter')]:shutil.copytree(path,stage/name,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
 (stage/'handshake_backend').mkdir();shutil.copy2(ROOT/'handshake_backend/binary_io.py',stage/'handshake_backend/binary_io.py');shutil.copy2(runtime/'compile.py',stage/'compile.py');source=stage/'Programs/Source';source.mkdir(parents=True);shutil.copy2(HERE/'reusable_outbox.mpc',source/'reusable_outbox.mpc')
 descriptors=[];receipts=[];files=[ROOT/'TlsMpc/Signal/PrivateReusableOutboxV1.lean',ROOT/'signal_backend/RecoveryWork/ShardedAccountWork/ExportOutbox.lean',HERE/'reusable_outbox.mpc',pathlib.Path(__file__)];before={str(p.relative_to(ROOT)):sha(p)for p in files}
 for ordinal in range(4):
  artifact=stage/f'outbox-{ordinal}.json';start=time.monotonic()
  with artifact.open('w')as out,(stage/f'export-{ordinal}.log').open('w')as err:subprocess.run(['lake','env','lean','--run','signal_backend/RecoveryWork/ShardedAccountWork/ExportOutbox.lean',str(ordinal)],cwd=ROOT,stdout=out,stderr=err,check=True,timeout=120)
  with(stage/f'compile-{ordinal}.log').open('w')as out:subprocess.run([sys.executable,'-u','-B','compile.py','-M','-X','-P',str(2**255-19),'reusable_outbox',str(artifact)],cwd=stage,env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1'),stdout=out,stderr=subprocess.STDOUT,check=True,timeout=120)
  descriptor=f'signal_private_reusable_outbox_v1_o{ordinal}-sbv:[52504x1]-sbv:[41960x1]';descriptors.append(descriptor);receipts.append(dict(ordinal=ordinal,descriptor=descriptor,seconds=time.monotonic()-start,artifact_sha256=sha(artifact)))
 manifest=stage/'outbox.manifest';manifest.write_text(build(stage,descriptors));assert before=={str(p.relative_to(ROOT)):sha(p)for p in files}
 (HERE/'outbox-compile-report.json').write_text(json.dumps(dict(compiled=True,candidate_only=True,stages=receipts,manifest_sha256=sha(manifest),source_sha256=before,native_MPC=False,whole_account_activation=False),indent=2)+'\n');print('PASS: four pinned account outbox policy profiles')
if __name__=='__main__':main()
