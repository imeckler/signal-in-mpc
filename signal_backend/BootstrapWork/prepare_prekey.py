#!/usr/bin/env python3
"""Freeze actual-computed private trusted-identity + two-signature validation."""
import hashlib,json,os,pathlib,shutil,subprocess,sys,time
ROOT=pathlib.Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load as load_boolean
from scripts.pin_tls_worker import build

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 work=ROOT/'SignalReference/XEdDsaWork';frozen=json.loads((work/'completion.json').read_text())
 for name in ['adapter.py','report.json','binding-report.json','challenge-report.json']:
  path=work/name;assert sha(path)==frozen['files'][str(path.relative_to(ROOT))],'frozen XEdDSA dependency changed'
 hashes={}
 for name in ['report.json','binding-report.json','challenge-report.json']:
  for item in json.loads((work/name).read_text())['profiles']:hashes[item['profile']]=item['sha256']
 stage=ROOT/'.deps/private-bootstrap-prekey-native/v1-candidate-1';assert not stage.exists(),'preserve immutable candidate'
 stage.mkdir(parents=True);(stage/'Artifacts').mkdir();runtime=ROOT/'.deps/sharing-refresh/MP-SPDZ'
 shutil.copytree(runtime/'Compiler',stage/'Compiler',ignore=shutil.ignore_patterns('__pycache__','*.pyc'));shutil.copy2(runtime/'compile.py',stage/'compile.py')
 shutil.copytree(ROOT/'backend_adapter',stage/'backend_adapter',ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
 sources=['handshake_backend/'+name for name in ['binary_io.py','field_dag.py','mixed.py']]+['signal_backend/BootstrapWork/'+name for name in ['pinned_stages.py','pinned_xeddsa.py','prekey_profile.py']]+['SignalReference/XEdDsaWork/adapter.py']
 for name in sources:
  p=stage/name;p.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(ROOT/name,p)
 source=stage/'Programs/Source/signal_bootstrap_prekey_validation.mpc';source.parent.mkdir(parents=True);shutil.copy2(ROOT/'programs/signal_bootstrap_prekey_validation.mpc',source)
 fields=[];booleans=[]
 for mode,index in [('recover',i)for i in range(3)]+[('signed',i)for i in range(2)]:
  name=f'signal-xeddsa-field-{mode}-{index}';path=work/'Artifacts'/(name+'.json');assert sha(path)==hashes[name]
  relative='Artifacts/'+hashes[name]+'.json';shutil.copyfile(path,stage/relative);fields.append(dict(key=[mode,index],path=relative,sha256=hashes[name]))
 for index,(mode,size)in enumerate([('binding',128),('hash',97),('hash',1633),('reduce',64),('finish',160)]):
  name=f'signal-xeddsa-boolean-{mode}-{size}';path=work/'Artifacts'/(name+'.json');assert sha(path)==hashes[name]
  image=load_boolean(path);ni=image['input_bits'];no=len(image['outputs']);del image
  relative='Artifacts/'+hashes[name]+'.json';shutil.copyfile(path,stage/relative)
  booleans.append(dict(key=['xeddsa',mode,size],path=relative,sha256=hashes[name],input_bits=ni,output_bits=no,function='signal_bootstrap_xeddsa_component_'+str(index)))
 (stage/'boolean.json').write_text(json.dumps(dict(format='signal-bootstrap-stages-v1',variant='xeddsa-prekey',stages=booleans),indent=2)+'\n')
 manifest=stage/'components.json';manifest.write_text(json.dumps(dict(format='signal-bootstrap-xeddsa-v1',fields=fields,boolean_manifest='boolean.json'),indent=2)+'\n')
 pins={str(p.relative_to(stage)):sha(p)for p in stage.rglob('*')if p.is_file()};started=time.clock_gettime(time.CLOCK_MONOTONIC_RAW)
 with(stage/'compile.log').open('w')as log:
  child=subprocess.Popen([sys.executable,'-B','compile.py','-M','-X','-P',str(2**255-19),'signal_bootstrap_prekey_validation',str(manifest)],cwd=stage,env=dict(os.environ,PYTHONHASHSEED='0',PYTHONDONTWRITEBYTECODE='1'),stdout=log,stderr=subprocess.STDOUT)
  print('private prekey compiler pid='+str(child.pid),flush=True)
  try:code=child.wait(timeout=1800)
  except subprocess.TimeoutExpired:child.kill();child.wait();raise
 report=dict(compiled=code==0,native_MPC=False,whole_bootstrap=False,statistical_security=128,parties_required=5,threshold_required=2,caller_signature_validity_flags=False,trust_boundary='Actual private trusted identity for this recipient must come from authenticated account lookup; this module compares exact bytes, not TOFU.',supported_profile='All-present one-time prekey; canonical fixed-length EC/Kyber1024 encodings and canonical coefficient range.',actual_source_refinement=False,compile_exit_code=code,elapsed_seconds=time.clock_gettime(time.CLOCK_MONOTONIC_RAW)-started,source_integrity=all(sha(stage/n)==h for n,h in pins.items()),source_sha256=pins,stage=str(stage.relative_to(ROOT)))
 if code==0:
  output=stage/'prekey.manifest';output.write_text(build(stage,['signal_private_bootstrap_prekey_all_present-sbv:[14856x1]-sbv:[8x1]']));report['manifest_sha256']=sha(output)
 (ROOT/'signal_backend/BootstrapWork/validation-compile-report.json').write_text(json.dumps(report,indent=2)+'\n')
 if code:raise SystemExit(code)
if __name__=='__main__':main()
