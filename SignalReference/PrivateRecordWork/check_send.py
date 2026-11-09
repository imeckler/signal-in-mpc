#!/usr/bin/env python3
"""PUBLIC actual sender fixtures, private-ops canonical update/snapshot model."""
import json,subprocess,hashlib,time
from pathlib import Path
from check import make,record,ROOT,HERE
def flatten(nodes):
 out=[]
 for n in nodes:
  out.append(n['present'])
  if n['kind']==2:out+=flatten(n['children'])
  elif n['kind']==1:out+=n['data']
  else:out += [255,n['length']//256,n['length']%256]+n['data']
 return out
def main():
 binary=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-recovery-send-record-oracle'
 def oracle(inactive=False):return json.loads(subprocess.check_output([str(binary)],input=json.dumps(dict(seed=19,send_last_inactive=inactive,plaintext=(b'C'*79+b'\x80').hex()))+'\n',text=True))['rows']
 ordinary=oracle();inactive=oracle(True);requests=[];expected=[]
 for row in ordinary[:2]+inactive[:1]:
  before=make(bytes.fromhex(row['sender_record_before']),record);after=make(bytes.fromhex(row['sender_record_after']),record)
  requests.append(dict(nodes=before,result=list(bytes.fromhex(row['sender_result'])),projection=list(bytes.fromhex(row['sender_selected_after'])),capacity=1024));expected.append(flatten(after))
 row=ordinary[1];bad=bytearray.fromhex(row['sender_result']);bad[0]=0
 before=make(bytes.fromhex(row['sender_record_before']),record)
 # The first successful output is exactly the second input state.
 requests.append(dict(nodes=before,result=list(bad),projection=list(bytes.fromhex(ordinary[0]['sender_selected_after'])),capacity=1024));expected.append(flatten(before))
 start=time.monotonic();p=subprocess.run(['lake','env','lean','--run',str(HERE/'EvaluateSend.lean')],cwd=ROOT,input=''.join(json.dumps(r)+'\n'for r in requests),text=True,capture_output=True,timeout=180);assert p.returncode==0,p.stderr
 for want,line in zip(expected,p.stdout.splitlines(),strict=True):assert json.loads(line)==want,'whole private canonical sender snapshot mismatch'
 sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 files=[HERE/x for x in ['check_send.py','EvaluateSend.lean','check.py','README.md']]+[ROOT/'TlsMpc/Signal'/x for x in ['PrivateRecordSendV1.lean','PrivateRecordSnapshotV1.lean','PrivateRecordUpdateV1.lean','PrivateRecordEncodingV1.lean']]+[ROOT/'signal_backend/Oracle/src/bin/signal-recovery-send-record-oracle.rs',ROOT/'signal_backend/Oracle/src/session_send_projection.rs']
 report=dict(passed=True,cases=4,first_and_repeated_send=True,actual_whole_SessionRecord_equality_in_Rust=True,private_full_tree_snapshot_equal=True,private_restored_selected525_equal=True,Tahini_inactive_to_send_increment=True,rejected_exact_preserve=True,full_private_schema_validation=False,computed_profile_validity=False,send_update_Hom_proof=False,native_MPC=False,atomic_restart_and_retirement=False,scope='Bounded no-chunk active-epoch private-ops canonical sender model; no skipped keys/epoch transitions and inactive-direction counter excludes overflow',seconds=time.monotonic()-start,oracle_binary_sha256=sha(binary),source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files})
 (HERE/'send-report.json').write_text(json.dumps(report,indent=2)+'\n');print('4 private canonical sender snapshot fixtures passed',round(report['seconds'],3),'seconds')
if __name__=='__main__':main()
