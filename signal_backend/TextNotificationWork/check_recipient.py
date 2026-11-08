#!/usr/bin/env python3
"""Public fixture oracle. Numeric circuit -> actual SS -> actual session receive.
No client-side secret reconstruction; this script handles PUBLIC disposable data.
Selected receiver state is supplied as a receiver-owned fixture, not final keys.
"""
import hashlib,json,subprocess,sys,uuid
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes
from SignalReference.RelayServiceWork.check import metadata,oracle
HERE=Path(__file__).resolve().parent
BIN=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-text-recipient-oracle'
def main():
 text_image=load(ROOT/'.deps/private-hash-artifacts/private-text-48-80.json')
 service_image=load(ROOT/'.deps/private-hash-artifacts/private-conversation-260-80-none-none.json')
 receiver=subprocess.Popen([str(BIN)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True)
 def receive(row):
  receiver.stdin.write(json.dumps(row)+'\n');receiver.stdin.flush();return json.loads(receiver.stdout.readline())
 fixtures=[];states=[];prefixes=[];first_inputs=[]
 for slot in range(2):
  f=oracle([dict(mode='sealed',seed=slot,inner='')])[0];raw=bytes.fromhex(f['input']);assert f['certificate_size']==260
  digest=lambda label:hashlib.sha256(('public-text-fixture-'+str(slot)+'-'+label).encode()).digest()
  i=bytearray(182);i[0]=4;i[1:5]=(127).to_bytes(4,'big');i[5:9]=(127).to_bytes(4,'big')
  i[9:41]=digest('ratchet');i[41:73]=digest('chain');i[73:105]=digest('pqchain')
  i[105:109]=(126).to_bytes(4,'big');i[109:117]=(127).to_bytes(8,'big');i[117]=0
  i[118:150]=raw[64:96];i[150:182]=raw[:32]
  assert receive(dict(mode='init',slot=slot,receiving_state=bytes(i).hex(),recipient_secret=f['recipient_secret']))=={'initialized':True}
  meta=bytearray(metadata(slot,2**63+slot));meta[:16]=uuid.UUID(f'ffeeddcc-bbaa-9988-7766-55443322110{slot}').bytes
  meta[16:32]=digest('access')[:16]
  initial=bytes.fromhex(f['sender_secret'])+raw[160:420]+bytes(i)+bytes(80)+bytes(meta)
  first_inputs.append(initial);states.append((i,meta));prefixes.append(raw[32:420])
  fixtures.append(dict(public_disposable_fixture_only=True,recipient_secret=f['recipient_secret'],root_public=f['root_public'],
   receiving_state=bytes(i).hex(),recipient_uuid=str(uuid.UUID(bytes=bytes(meta[:16]))),access_key=bytes(meta[16:32]).hex(),device_id=1,registration_id=16383,
   initial=initial.hex(),expected_inner=[],expected_text=[],timestamps=[],request_ids=[]))
 assert states[0][0][41:105]!=states[1][0][41:105] and states[0][0][150:182]!=states[1][0][150:182]
 texts=[['Hello, Signal! ☕','Second private notification'],['你好，世界','Delivery ready 😀']]
 records=[]
 for round in range(2):
  inputs=[];expected=[]
  for slot in range(2):
   text=texts[slot][round];body=text.encode();timestamp=1900000000000+2*round+slot;request_id=2**63+2*round+slot
   text_input=b'\xff'+len(body).to_bytes(2,'big')+body+bytes(48-len(body))+timestamp.to_bytes(8,'big')
   output=evaluate_lanes(text_image,[text_input])[0];assert output[0]==255 and output[1]==0 and len(output)==90
   actual=receive(dict(mode='text',body=body.hex(),timestamp=timestamp));assert actual==dict(accepted=True,padded=output[2:82].hex())
   i,meta=states[slot];meta[32:40]=output[82:90];meta[40:48]=request_id.to_bytes(8,'big')
   inputs.append(prefixes[slot]+bytes(i)+output[2:82]+bytes(meta));expected.append((text,timestamp,request_id))
  outputs=evaluate_lanes(service_image,inputs)
  for slot,output in enumerate(outputs):
   text,timestamp,request_id=expected[slot];assert output[0]==255
   n=int.from_bytes(output[81:83],'big');wire=output[83:83+n];assert output[83+n:]==bytes(len(output)-83-n)
   decoded=oracle([dict(mode='relay',wire=wire.hex())])[0];assert decoded['id']==request_id and decoded['body']['timestamp']==timestamp
   f=fixtures[slot];assert decoded['path']=='/v1/messages/'+f['recipient_uuid']+'?story=false'
   plain=oracle([dict(mode='sealed_decrypt',wire=decoded['ciphertext'],recipient_secret=f['recipient_secret'],root_public=f['root_public'])])[0]
   assert plain['certificate_valid'];inner=plain['inner']
   # Reject modified authenticated ciphertext WITHOUT advancing actual session.
   bad=bytearray.fromhex(inner);bad[-1]^=1
   assert receive(dict(slot=slot,wire=bad.hex()))==dict(accepted=False,stage='session_decrypt')
   recovered=receive(dict(slot=slot,wire=inner));assert recovered==dict(accepted=True,body=text,timestamp=timestamp,padded_bytes=80),recovered
   assert receive(dict(slot=slot,wire=inner))==dict(accepted=False,stage='session_decrypt')
   i,meta=states[slot];i[41:73]=output[1:33];i[1:5]=output[33:37];i[73:105]=output[37:69];i[105:109]=output[69:73];meta[40:48]=output[73:81]
   f['expected_inner'].append(inner);f['expected_text'].append(text);f['timestamps'].append(timestamp);f['request_ids'].append(request_id)
   records.append(dict(slot=slot,round=round,signal_counter=127+round,pq_counter=127+round,actual_recipient_text_matches=True,app_plaintext_bytes=80,websocket_bytes=n))
  print(f'round{round}: two distinct conversations actual SS/session/Content text recovered',flush=True)
 receiver.stdin.close();assert receiver.wait(timeout=10)==0
 # Client inputs and receiver-only fixture state are explicitly disposable;
 # runtime server uses receiver fields only, never sender initial or final keys.
 fixture=dict(public_disposable_fixture_only=True,upgrade_username='00112233-4455-6677-8899-aabbccddeeff',upgrade_password='x'*22,conversations=fixtures)
 (HERE/'text-fixtures.json').write_text(json.dumps(fixture,indent=2)+'\n')
 files=[Path(__file__),ROOT/'signal_backend/Oracle/src/bin/signal-text-recipient-oracle.rs',ROOT/'signal_backend/Oracle/build.rs',ROOT/'TlsMpc/Signal/PrivateTextNotification.lean']
 report=dict(artifact_sha256={name:hashlib.sha256((ROOT/'.deps/private-hash-artifacts'/name).read_bytes()).hexdigest()for name in ['private-text-48-80.json','private-conversation-260-80-none-none.json']},records=records,actual_session_receive=True,actual_prost_outer_Content=True,minimal_DataMessage_schema='exact relay messaging.rs derive fields1,6,7',tamper_and_replay_rejections=8,
  independent_recipient_and_chain_states=True,selected_established_state_fixture=True,fresh_session_initialization=False,native_MPC_executed=False,
  pinned_libsignal_commit='904c8dc8216073b078a5f2f5090e3da8382e6a92',
  source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files})
 (HERE/'recipient-report.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
