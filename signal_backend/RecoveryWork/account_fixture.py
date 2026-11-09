"""PUBLIC disposable complete bounded account data; never a production import."""
import json,subprocess,sys,uuid
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT));sys.path.insert(0,str(ROOT/'SignalReference/PrivateRecordWork'))
from SignalReference.RelayServiceWork.check import oracle,metadata
from check import make,record
from check_send import flatten
from check_binding import service
GLOBAL=[38,65,8195,8];CONVERSATION=[69,5550,611,525,612,5208,4]

def buffer(capacity,data):
 assert len(data)<=capacity
 return b'\xff'+len(data).to_bytes(2,'big')+data+bytes(capacity-len(data))
def fixture():
 first,second=oracle([dict(mode='sealed',seed=seed,inner='')for seed in [19,23]])
 target=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-account-snapshot-oracle'
 credentials=uuid.UUID('00112233-4455-6677-8899-aabbccddeeff').bytes+b'0123456789abcdefghijkl';assert len(credentials)==38
 peers=['ffeeddcc-bbaa-9988-7766-554433221100','01234567-89ab-cdef-0123-456789abcdef'];states=[];global_data=None
 for slot,(seed,recipient)in enumerate(zip([19,23],[first,second])):
  query=dict(seed=seed,steps=3,alice_secret=first['sender_secret'],bob_secret=recipient['recipient_secret'],recipient_uuid=peers[slot],plaintext=(b'E'*79+b'\x80').hex())
  result=json.loads(subprocess.check_output([str(target)],input=json.dumps(query)+'\n',text=True));global_data=global_data or result['global_stores'];rows=result['rows'];raw=service(rows[0],slot);f=bytes.fromhex(first['input']);raw[32:292]=f[160:420];raw[474:554]=bytes.fromhex(query['plaintext']);meta=bytearray(metadata(seed,2**63+slot));meta[:16]=uuid.UUID(peers[slot]).bytes;meta[49:53]=(2).to_bytes(4,'big');raw[554:611]=meta
  binding=bytes(meta[:16])+bytes(meta[49:53])+b'\x05'+bytes(raw[442:474])+bytes(meta[16:32]);assert len(binding)==69
  def conv(row,after=False,raw=raw,binding=binding,slot=slot):
   selected=bytes.fromhex(row['sender_selected_after'if after else'sender_selected_before']);native=bytes.fromhex(row['sender_record_after'if after else'sender_record_before']);call=bytearray(raw)
   if after:
    prefix=bytes.fromhex(row['sender_result']);call[333:365]=prefix[1:33];call[293:297]=prefix[33:37];call[365:397]=prefix[37:69];call[397:401]=prefix[69:73];call[594:602]=(2**63+slot+1).to_bytes(8,'big')
   return[binding,bytes(flatten(make(native,record))),bytes(call),selected,bytes(612),bytes(5208),bytes(4)]
  states.append(dict(rows=rows,raw=bytes(raw),binding=binding,before=conv(rows[0]),after=conv(rows[0],True),second=conv(rows[1],True),query=query,recipient=recipient))
 g=[credentials,bytes.fromhex(global_data['identity_private_public65']),buffer(8192,bytes.fromhex(global_data['global_store_v1'])),(2**63).to_bytes(8,'big')]
 initial=g+[part for state in states for part in state['before']]
 reserve=[bytes(x)for x in initial];reserve[3]=(2**63+2).to_bytes(8,'big')
 for slot,state in enumerate(states):reserve[4+7*slot+4]=b'\xff'+state['raw']
 committed=[bytes(x)for x in reserve]
 for slot,state in enumerate(states):
  for tag in [1,2,3]:committed[4+7*slot+tag]=state['after'][tag]
 # Public parser/serialization fixture outboxes: valid16-bit maskedframe. The
 # actual service cryptographic/outbox test is a distinct integration step.
 frame=b'\x82\xfe\x00\x7e'+bytes([17,29,53,71])+bytes(126)
 for slot in range(2):
  entry=b'\xff'+buffer(1290,frame)+(2**63+slot).to_bytes(8,'big');assert len(entry)==1302
  committed[4+7*slot+5]=entry+bytes(3*1302);committed[4+7*slot+6]=bytes([1,0,0,0])
 assert all([len(x)for x in snapshot]==GLOBAL+2*CONVERSATION for snapshot in [initial,reserve,committed])
 second_reserve=[bytes(x)for x in committed];second_reserve[3]=(2**63+3).to_bytes(8,'big')
 state=states[1];raw=service(state['rows'][1],2);raw[32:292]=bytes.fromhex(first['input'])[160:420];raw[474:554]=bytes.fromhex(state['query']['plaintext']);raw[554:611]=state['raw'][554:611];raw[594:602]=(2**63+2).to_bytes(8,'big')
 second_reserve[4+7+2]=bytes(raw);second_reserve[4+7+4]=b'\xff'+bytes(raw)
 second_commit=[bytes(x)for x in second_reserve]
 for tag in [1,2,3]:second_commit[4+7+tag]=state['second'][tag]
 # Per-conversation cached ID is selectedID+1; global cursor remainsauthoritative.
 changed=bytearray(second_commit[4+7+2]);changed[594:602]=(2**63+3).to_bytes(8,'big');second_commit[4+7+2]=bytes(changed)
 new_entry=b'\xff'+buffer(1290,frame)+(2**63+2).to_bytes(8,'big')
 second_commit[4+7+5]=second_commit[4+7+5][:1302]+new_entry+bytes(2*1302);second_commit[4+7+6]=bytes([1,1,0,0])
 assert second_commit[4:11]==committed[4:11] # old unrelated pendingoutboxkept
 return dict(initial=initial,reserve=reserve,committed=committed,second_reserve=second_reserve,second_commit=second_commit,states=states,global_data=global_data)
