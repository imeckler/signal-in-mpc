#!/usr/bin/env python3
"""PUBLIC canonical/service binding cases, no native crypto/kernel execution."""
import json,subprocess,hashlib,copy,time
from check import ROOT,HERE,make,record,fields
from check_send import flatten

def service(row,index=0):
 f=fields(fields(bytes.fromhex(row['sender_record_before']))[1][0]);sender=fields(f[6][0]);key=fields(sender[3][0]);pq=fields(f[15][0]);chain=fields(pq[2][0]);link=fields(chain[3][0]);send=fields(link[1][0])
 be=lambda n:n.to_bytes(4,'big')
 body=bytes([f[1][0]])+be(key.get(1,[0])[0])+be(f.get(5,[0])[0])+sender[1][0][1:]+key[2][0]+send[2][0]+be(send.get(1,[0])[0])+(chain.get(2,[0])[0]+1).to_bytes(8,'big')+b'\0'+f[2][0][1:]+f[3][0][1:]+bytes(80)
 raw=bytearray(bytes.fromhex(row['account_identity'])[:32]+bytes(260)+body+bytes(57));assert len(raw)==611
 raw[594:602]=(2**63+index).to_bytes(8,'big');return raw

def cases():
 oracle=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-recovery-send-record-oracle'
 def ask(**args):return json.loads(subprocess.check_output([str(oracle)],input=json.dumps(dict(seed=19,plaintext=(b'E'*79+b'\x80').hex(),**args))+'\n',text=True))['rows']
 rows=ask();requests=[];expected=[]
 def append(row,raw,produced,nodes,accept):
  before=make(bytes.fromhex(row['sender_record_before']),record);after=make(bytes.fromhex(row['sender_record_after']),record)
  if accept:state=bytes.fromhex(row['sender_selected_after']);want=bytes(produced)+bytes(flatten(after))
  else:
   state=bytes.fromhex(row['sender_selected_before']);old=raw[333:365]+raw[293:297]+raw[365:397]+raw[397:401]+raw[594:602]
   want=b'\0'+bytes(old)+bytes(flatten(nodes))
  requests.append(dict(nodes=nodes,result=list(produced),service=list(raw),projection=list(state),capacity=1024));expected.append(want)
 for index,row in enumerate(rows[:2]+ask(send_last_inactive=True)[:1]):
  raw=service(row,index);result=bytearray.fromhex(row['sender_result']);result[73:81]=(2**63+index+1).to_bytes(8,'big');append(row,raw,result,make(bytes.fromhex(row['sender_record_before']),record),True)
 row=rows[0];raw=service(row);result=bytearray.fromhex(row['sender_result']);result[73:81]=(2**63+1).to_bytes(8,'big')
 for offset in [292,293,297,301,333,365,397,401,409,410,442]:
  bad=bytearray(raw);bad[offset]^=1;append(row,bad,result,make(bytes.fromhex(row['sender_record_before']),record),False)
 bad=bytearray(result);bad[0]=0;append(row,raw,bad,make(bytes.fromhex(row['sender_record_before']),record),False)
 bad=bytearray(result);bad[0]=1;append(row,raw,bad,make(bytes.fromhex(row['sender_record_before']),record),False)
 # Hidden malformed presence cannot become an accepted record.
 nodes=make(bytes.fromhex(row['sender_record_before']),record);nodes[0]['present']=1;append(row,raw,result,nodes,False)
 # A canonical KeysUnsampled V1 tag is outside the computed no-chunk profile.
 nodes=make(bytes.fromhex(row['sender_record_before']),record);current=nodes[0]['children'];pq=next(n for n in current if n['tag']==15)['children'];next(n for n in pq if n['tag']==3)['data'][0]=10;append(row,raw,result,nodes,False)
 nodes=make(bytes.fromhex(row['sender_record_before']),record);management=next(n for n in nodes if n['tag']==3)['children'];next(n for n in management if n['tag']==1)['data']=[0,0,0,2];next(n for n in management if n['tag']==2)['data']=[255]*4;append(row,raw,result,nodes,False)
 nodes=make(bytes.fromhex(row['sender_record_before']),record);management=next(n for n in nodes if n['tag']==3)['children'];counter=next(n for n in management if n['tag']==2);counter['present']=0;counter['data']=[0,0,0,7];append(row,raw,result,nodes,False)
 return requests,expected,oracle

def main():
 requests,expected,oracle=cases()
 start=time.monotonic();p=subprocess.run(['lake','env','lean','--run',str(HERE/'EvaluateBinding.lean')],cwd=ROOT,input=''.join(json.dumps(r)+'\n'for r in requests),text=True,capture_output=True,timeout=120);assert p.returncode==0,p.stderr
 for i,(want,line)in enumerate(zip(expected,p.stdout.splitlines(),strict=True)):
  actual=bytes(json.loads(line));assert actual==want,(i,len(actual),len(want),[(n,x,y)for n,(x,y)in enumerate(zip(actual,want))if x!=y][:4])
 sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
 files=[HERE/x for x in ['check_binding.py','EvaluateBinding.lean','BINDING.md','check.py','check_send.py']]+[ROOT/'TlsMpc/Signal'/x for x in ['PrivateRecordBindingV1.lean','PrivateRecordSendV1.lean','PrivateRecordSnapshotV1.lean','PrivateRecordUpdateV1.lean']]
 report=dict(passed=True,cases=len(requests),actual_Rust_selected_state_prefix=True,actual_private_service_crypto_executed_here=False,public_fixture_dummy_certificate=True,computed_key_identity_counter_epoch_binding=True,computed_nochunk_NoHeaderReceived_selection=True,computed_Tahini_overflow_rejection=True,normalized_producer_status=True,rejected_private_snapshot_preserved=True,native_MPC=False,full_schema_validation=False,full_source_or_compiler_theorem=False,provider_admission=False,seconds=time.monotonic()-start,source_sha256={str(p.relative_to(ROOT)):sha(p)for p in files},oracle_binary_sha256=sha(oracle))
 (HERE/'binding-report.json').write_text(json.dumps(report,indent=2)+'\n');print(len(requests),'private record/service binding cases passed',round(report['seconds'],3),'seconds')
if __name__=='__main__':main()
