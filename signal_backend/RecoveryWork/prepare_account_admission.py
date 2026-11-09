#!/usr/bin/env python3
"""Continue exact isolated account export once; never overwrite compiled closure."""
import hashlib,json,os,pathlib,shutil,subprocess,sys,time
ROOT=pathlib.Path(__file__).resolve().parents[2];HERE=pathlib.Path(__file__).resolve().parent;sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build

def main():
 stage=ROOT/'.deps/private-account-admission-native/v2-candidate-1';runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ';artifact=stage/'admit.json';assert artifact.is_file() and not(stage/'account.manifest').exists()
 image=json.loads(artifact.read_text());assert image['conversations']==1 and image['input_bits']==20885*8;del image
 sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 def identity():
  pending=[ROOT/'SignalReference/PrivateRecordWork/ExportAccount.lean'];seen={}
  while pending:
   path=pending.pop();key=str(path.relative_to(ROOT))
   if key in seen:continue
   seen[key]=sha(path)
   for line in path.read_text().splitlines():
    if line.startswith('import '):
     for module in line[7:].split():
      target=ROOT/(module.replace('.','/')+'.lean')
      if target.is_file():pending.append(target)
  return seen
 lean=identity();artifact_hash=sha(artifact)
 for name,path in [('Compiler',runtime/'Compiler'),('backend_adapter',ROOT/'backend_adapter')]:
  assert not(stage/name).exists();shutil.copytree(path,stage/name,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
 (stage/'handshake_backend').mkdir();shutil.copy2(ROOT/'handshake_backend/binary_io.py',stage/'handshake_backend/binary_io.py');shutil.copy2(runtime/'compile.py',stage/'compile.py');source=stage/'Programs/Source';source.mkdir(parents=True);shutil.copy2(ROOT/'programs/signal_account_admission_v2.mpc',source/'signal_account_admission_v2.mpc');shutil.copy2(ROOT/'signal_backend/SessionTransitionWork/compile_diagnostic.py',stage/'compile_diagnostic.py')
 start=time.monotonic()
 with(stage/'admit-compile.log').open('w')as out:subprocess.run([sys.executable,'-u','-B','compile_diagnostic.py','-M','-X','-P',str(2**255-19),'signal_account_admission_v2',str(artifact)],cwd=stage,env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1'),stdout=out,stderr=subprocess.STDOUT,check=True,timeout=600)
 assert lean==identity()and artifact_hash==sha(artifact)
 descriptor='signal_private_account_admit_v2_c1-sbv:[167080x1]-sbv:[8x1]';manifest=stage/'account.manifest';manifest.write_text(build(stage,[descriptor]))
 files=[pathlib.Path(__file__),ROOT/'programs/signal_account_admission_v2.mpc',HERE/'NativeAccountAdmission.h',ROOT/'backend_adapter/aig_packed.py',ROOT/'signal_backend/SessionTransitionWork/compile_diagnostic.py']
 report=dict(compiled=True,candidate_only=True,structural_coherence_only=True,conversations=1,logical_bytes=20885,descriptor=descriptor,seconds=time.monotonic()-start,artifact_sha256=artifact_hash,manifest_sha256=sha(manifest),lean_source_sha256=lean,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files},native_MPC=False,whole_account_activation=False)
 (HERE/'account-admission-compile-report.json').write_text(json.dumps(report,indent=2)+'\n');print('PASS: isolated account validator compiled')
if __name__=='__main__':main()
