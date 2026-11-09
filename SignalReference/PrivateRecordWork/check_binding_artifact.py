#!/usr/bin/env python3
"""Exact PUBLIC computed binding artifact checks against real record fixtures."""
import hashlib,json,sys,time
from check_binding import ROOT,HERE,cases
from check_send import flatten
sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load,execute

def main():
 stage=ROOT/'.deps/private-record-binding-native/v1-candidate-1'
 image=load(stage/'bind.json');report=json.loads((HERE/'binding-native-compile-report.json').read_text())
 sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 assert report['stage']==str(stage.relative_to(ROOT))
 for source,want in report['lean_source_sha256'].items():assert sha(ROOT/source)==want,source
 assert sha(stage/'bind.json')==report['stages'][0]['artifact_sha256']
 assert sha(stage/'binding.manifest')==report['manifest_sha256']
 requests,expected,oracle=cases();start=time.monotonic()
 for i,(request,want) in enumerate(zip(requests,expected,strict=True)):
  raw=bytes(flatten(request['nodes']))+bytes(request['service'])+bytes(request['result'])
  assert len(raw)==6242 and image['input_bits']==49936
  bits=[(b>>(7-i))&1 for b in raw for i in range(8)]
  output=execute(image,bits,0,1)
  actual=bytes(sum(output[i+j]<<(7-j)for j in range(8))for i in range(0,len(output),8))
  target=want[:81]+bytes(request['projection'])+want[81:]
  assert actual==target,(i,len(actual),len(target),[(n,x,y)for n,(x,y)in enumerate(zip(actual,target))if x!=y][:5])
 sources=[HERE/x for x in ['check_binding_artifact.py','check_binding.py','check.py','check_send.py','binding-native-compile-report.json']]
 (HERE/'binding-artifact-report.json').write_text(json.dumps(dict(passed=True,cases=len(requests),full_bound_prefix_selected_snapshot_equal=True,actual_Rust_record_fixtures=True,private_service_crypto_executed_here=False,public_dummy_certificate=True,native_MPC=False,full_actual_source_refinement=False,provider_admission=False,seconds=time.monotonic()-start,artifact_sha256=sha(stage/'bind.json'),oracle_binary_sha256=sha(oracle),source_sha256={str(p.relative_to(ROOT)):sha(p)for p in sources}),indent=2)+'\n')
 print(len(requests),'exact binding artifact cases passed')
if __name__=='__main__':main()
