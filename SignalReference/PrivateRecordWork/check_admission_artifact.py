#!/usr/bin/env python3
"""Public exact admission artifact evaluation; no native restore admission."""
import hashlib,json,pathlib,sys,time
from check_admission import ROOT,HERE,cases
sys.path.insert(0,str(ROOT));from backend_adapter.boolean import load,execute

def main():
 stage=ROOT/'.deps/private-record-admission-native/v1-candidate-1';image=load(stage/'admit.json');receipt=json.loads((HERE/'admission-native-compile-report.json').read_text())
 sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 assert receipt['stage']==str(stage.relative_to(ROOT))
 for source,want in receipt['lean_source_sha256'].items():assert sha(ROOT/source)==want,source
 assert sha(stage/'admit.json')==receipt['stages'][0]['artifact_sha256']
 assert sha(stage/'admission.manifest')==receipt['manifest_sha256']
 tests,oracle=cases();checks=0;start=time.monotonic()
 for raw,want in tests:
  if len(raw)!=6686:continue # Native adapter rejects non-profile dimensions.
  bits=[(b>>(7-i))&1 for b in raw for i in range(8)]
  output=execute(image,bits,0,1);actual=sum(output[i]<<(7-i)for i in range(8));assert actual==want,(checks,actual,want);checks+=1
 files=[pathlib.Path(__file__),HERE/'check_admission.py',HERE/'admission-native-compile-report.json']
 (HERE/'admission-artifact-report.json').write_text(json.dumps(dict(passed=True,cases=checks,actual_Rust_record_projection_fixtures=True,native_MPC=False,full_account_or_SPQR_validation=False,private_public_DH_agreement_not_checked_here=True,provider_admission=False,seconds=time.monotonic()-start,artifact_sha256=sha(stage/'admit.json'),oracle_binary_sha256=sha(oracle),source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files}),indent=2)+'\n');print(checks,'exact admission artifact cases passed')
if __name__=='__main__':main()
