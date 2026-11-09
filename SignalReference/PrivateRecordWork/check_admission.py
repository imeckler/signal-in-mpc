#!/usr/bin/env python3
"""Public bounded restore-coherence guard; not full account admission."""
import hashlib,json,pathlib,subprocess
from check import ROOT,HERE,make,record
from check_send import flatten
from check_binding import service

def cases():
 oracle=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-recovery-send-record-oracle'
 rows=json.loads(subprocess.check_output([str(oracle)],input=json.dumps(dict(seed=19,plaintext=(b'E'*79+b'\x80').hex()))+'\n',text=True))['rows']
 tests=[]
 for row in rows[:2]:
  raw=bytes(flatten(make(bytes.fromhex(row['sender_record_before']),record)))+bytes.fromhex(row['sender_selected_before'])+bytes(service(row))
  assert len(raw)==6686;tests.append((raw,255))
 initial=tests[0][0]
 # Private selected view and actual call are checked, not supplied flags.
 for offset in [0,7,8,3487,5550,5550+32,6075+293,6075+333,6075+365,6075+410,6075+442]:
  bad=bytearray(initial);bad[offset]^=1;tests.append((bytes(bad),0))
 # The final byte is a live Tahini u32 counter, not capacity padding.
 valid=bytearray(initial);valid[5549]^=1;tests.append((bytes(valid),255))
 for raw in [initial[:-1],initial+b'\0']:tests.append((raw,0))
 return tests,oracle

def main():
 tests,oracle=cases();run=subprocess.run(['lake','env','lean','--run',str(HERE/'EvaluateAdmission.lean')],cwd=ROOT,input=''.join(json.dumps(list(raw))+'\n'for raw,_ in tests),text=True,capture_output=True,check=True)
 assert [json.loads(line)for line in run.stdout.splitlines()]==[[want]for _,want in tests]
 sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 files=[pathlib.Path(__file__),HERE/'EvaluateAdmission.lean',ROOT/'TlsMpc/Signal/PrivateRecordAdmissionV1.lean']
 (HERE/'admission-report.json').write_text(json.dumps(dict(passed=True,cases=len(tests),actual_Rust_records_and_selected_state=True,computed_record_service_selected_consistency=True,private_public_DH_agreement_not_checked_here=True,full_account_or_SPQR_validation=False,native_MPC=False,provider_admission=False,oracle_binary_sha256=sha(oracle),source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files}),indent=2)+'\n');print(len(tests),'bounded private admission model cases passed')
if __name__=='__main__':main()
