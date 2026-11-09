#!/usr/bin/env python3
"""PUBLIC exact artifact evaluation; no private native execution/security claim."""
import hashlib,json,subprocess,sys,time
from pathlib import Path
from check import ROOT,HERE,make,record
from check_send import flatten
sys.path.insert(0,str(ROOT));from backend_adapter.boolean import load,execute

def main():
 stage=ROOT/'.deps/private-record-snapshot-native/v1-candidate-4';send_oracle=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-recovery-send-record-oracle';recv_oracle=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-session-inorder-oracle'
 def ask(binary,**args):return json.loads(subprocess.check_output([str(binary)],input=json.dumps(dict(seed=19,plaintext=(b'D'*79+b'\x80').hex(),**args))+'\n',text=True))['rows']
 send=ask(send_oracle);inactive=ask(send_oracle,send_last_inactive=True);recv=ask(recv_oracle);local_new=ask(recv_oracle,origin_local_new=True);kyber_only=ask(recv_oracle,keep_kyber_without_prekey=True);origin_only=ask(recv_oracle,origin_without_prekey=True)
 cases={'send':[],'receive':[]}
 for row in send[:2]+inactive[:1]:cases['send'].append((row['sender_record_before'],row['sender_result'],row['sender_record_after'],row['sender_selected_after']))
 bad=bytearray.fromhex(send[1]['sender_result']);bad[0]=0;cases['send'].append((send[1]['sender_record_before'],bad.hex(),send[1]['sender_record_before'],send[0]['sender_selected_after']))
 for row in recv[:2]+local_new[:1]+kyber_only[:1]+origin_only[:1]:cases['receive'].append((row['record_before'],row['expected'],row['record_after'],row['expected'][2:1052]))
 row=recv[0];bad=bytearray.fromhex(row['expected']);bad[0]=0;cases['receive'].append((row['record_before'],bad.hex(),row['record_before'],row['input'][:1050]))
 start=time.monotonic();checks=0;artifacts={}
 for mode,rows in cases.items():
  path=stage/(mode+'.json');image=load(path);assert image['snapshot_bytes']==5550 and image['schema_sha256']=='510bd678767ca3b7918486cdc1b872890d86b18e3a790d187f9361fadca28b0a'
  artifacts[mode]=hashlib.file_digest(path.open('rb'),'sha256').hexdigest()
  for before,result,after,projection in rows:
   raw=bytes(flatten(make(bytes.fromhex(before),record)))+bytes.fromhex(result);assert len(raw)*8==image['input_bits']
   bits=[(b>>(7-i))&1 for b in raw for i in range(8)]
   output=execute(image,bits,0,1);actual=bytes(sum(output[i+j]<<(7-j)for j in range(8))for i in range(0,len(output),8))
   expected=bytes([255 if bytes.fromhex(result)[0]==255 else 0])+bytes.fromhex(projection)+bytes(flatten(make(bytes.fromhex(after),record)))
   assert actual==expected,(mode,checks,len(actual),len(expected),[(i,x,y)for i,(x,y)in enumerate(zip(actual,expected))if x!=y][:4]);checks+=1
 sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 compile_report=json.loads((HERE/'native-compile-report.json').read_text())
 assert compile_report['stage']==str(stage.relative_to(ROOT))
 for source,want in compile_report['lean_source_sha256'].items():assert sha(ROOT/source)==want,('changed Lean source',source)
 for receipt in compile_report['stages']:assert artifacts[receipt['mode']]==receipt['artifact_sha256']
 files=[HERE/x for x in ['check_snapshot_artifact.py','check.py','check_send.py','ExportSnapshot.lean','native-compile-report.json']]+[ROOT/'TlsMpc/Signal'/x for x in ['PrivateRecordSchemaV1.lean','PrivateRecordUpdateV1.lean','PrivateRecordSnapshotV1.lean','PrivateRecordSendV1.lean','PrivateRecordEncodingV1.lean']]+[ROOT/'signal_backend/Oracle/src/bin/signal-session-inorder-oracle.rs',ROOT/'signal_backend/Oracle/src/bin/signal-recovery-send-record-oracle.rs',ROOT/'signal_backend/Oracle/src/session_projection.rs',ROOT/'signal_backend/Oracle/src/session_send_projection.rs']
 (HERE/'artifact-report.json').write_text(json.dumps(dict(passed=True,cases=checks,actual_pinned_records=True,full_flat_snapshot_and_selected_projection_equal=True,artifact_sha256=artifacts,native_MPC=False,full_source_refinement=False,provider_admission=False,seconds=time.monotonic()-start,oracle_binary_sha256={p.name:sha(p)for p in [send_oracle,recv_oracle]},source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files}),indent=2)+'\n');print(str(checks)+' exact record artifact cases passed')
if __name__=='__main__':main()
