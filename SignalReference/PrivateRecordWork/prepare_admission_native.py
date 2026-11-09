#!/usr/bin/env python3
"""Immutable candidate record-binding artifacts/closures, separate from service crypto."""
import argparse,hashlib,json,os,re,shutil,subprocess,sys,time
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];sys.path.insert(0,str(ROOT))
from scripts.pin_tls_worker import build
sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
def identity():
 pending=[HERE/'ExportAdmission.lean'];seen={}
 while pending:
  p=pending.pop();key=str(p.relative_to(ROOT))
  if key in seen:continue
  seen[key]=sha(p)
  for line in p.read_text().splitlines():
   if line.startswith('import '):
    for module in line[7:].split():
     target=ROOT/(module.replace('.','/')+'.lean')
     if target.is_file():pending.append(target)
 return seen
def main():
 parser=argparse.ArgumentParser();parser.add_argument('--candidate',default='v1-candidate-1');args=parser.parse_args();assert re.fullmatch(r'v1-candidate-[1-9][0-9]*',args.candidate)
 stage=ROOT/'.deps/private-record-admission-native'/args.candidate;runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ'
 if stage.exists():raise RuntimeError('preserve candidate stage; inspect exact receipts before any continuation')
 stage.mkdir(parents=True)
 for name,path in [('Compiler',runtime/'Compiler'),('backend_adapter',ROOT/'backend_adapter')]:shutil.copytree(path,stage/name,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
 (stage/'handshake_backend').mkdir();shutil.copy2(ROOT/'handshake_backend/binary_io.py',stage/'handshake_backend/binary_io.py')
 shutil.copy2(runtime/'compile.py',stage/'compile.py');source=stage/'Programs/Source';source.mkdir(parents=True);shutil.copy2(ROOT/'programs/signal_record_admission_v1.mpc',source/'signal_record_admission_v1.mpc')
 shutil.copy2(ROOT/'signal_backend/SessionTransitionWork/compile_diagnostic.py',stage/'compile_diagnostic.py')
 descriptors=[];receipts=[];lean=identity()
 for mode,n in [('admit',6686)]:
  artifact=stage/(mode+'.json');start=time.monotonic()
  with artifact.open('w')as out,(stage/(mode+'-export.log')).open('w')as err:subprocess.run(['lake','env','lean','--run',str(HERE/'ExportAdmission.lean')],cwd=ROOT,stdout=out,stderr=err,check=True,timeout=300)
  assert identity()==lean,'Lean source changed during export'
  export_seconds=time.monotonic()-start
  with (stage/(mode+'-compile.log')).open('w')as out:subprocess.run([sys.executable,'-u','-B','compile_diagnostic.py','-M','-X','-P',str(2**255-19),'signal_record_admission_v1',str(artifact)],cwd=stage,env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1'),stdout=out,stderr=subprocess.STDOUT,check=True,timeout=300)
  descriptor=f'signal_private_record_{mode}_v1-sbv:[{8*n}x1]-sbv:[8x1]';descriptors.append(descriptor)
  pin=stage/(mode+'.manifest');pin.write_text(build(stage,[descriptor]))
  item=dict(mode=mode,completed=True,export_seconds=export_seconds,artifact_sha256=sha(artifact),manifest_sha256=sha(pin),descriptor=descriptor)
  (stage/(mode+'-receipt.json')).write_text(json.dumps(item,indent=2)+'\n');receipts.append(item);print(mode+' record candidate compiled',flush=True)
 manifest=stage/'admission.manifest';manifest.write_text(build(stage,descriptors))
 files=[Path(__file__),ROOT/'programs/signal_record_admission_v1.mpc',ROOT/'signal_backend/SessionTransitionWork/compile_diagnostic.py',ROOT/'backend_adapter/aig_packed.py',ROOT/'handshake_backend/binary_io.py']
 report=dict(compiled=True,candidate_only=True,native_MPC=False,full_update_refinement=False,provider_admission=False,stage=str(stage.relative_to(ROOT)),manifest_sha256=sha(manifest),stages=receipts,lean_source_sha256=lean,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files})
 (HERE/'admission-native-compile-report.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
