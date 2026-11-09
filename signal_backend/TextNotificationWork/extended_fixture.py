"""PUBLIC expectation generation only; never called by a client/MPC producer.
Receiving-side fixture seeds derive test message material; unchanged pinned
SignalMessage/AES APIs construct fixture wire, actual stateful recipient verifies
it. This is not source refinement or a replacement cryptographic implementation.
"""
import copy,hashlib,hmac,json,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
ORACLE=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-established-send-oracle'
def mac(key,data):return hmac.digest(key,data,'sha256')
def expand(prk,info,n):
 out=b'';last=b''
 for counter in range(1,(n+31)//32+1):last=mac(prk,last+info+bytes([counter]));out+=last
 return out[:n]
def varint(n):
 out=bytearray()
 while n>=128:out.append((n&127)|128);n>>=7
 out.append(n);return bytes(out)
def field(tag,value):return bytes([tag])+varint(len(value))+value
def derive(fixture,rounds):
 assert rounds in [2,4];result=copy.deepcopy(fixture)
 if rounds==2:return result
 for slot,c in enumerate(result['conversations']):
  old_text=list(c['expected_text']);old_time=list(c['timestamps']);assert len(old_text)==len(old_time)==2
  c['expected_text']=old_text*2;c['timestamps']=old_time+[t+4 for t in old_time]
  c['request_ids']=[2**63+2*r+slot for r in range(4)]
  state=bytes.fromhex(c['receiving_state']);chain=state[41:73];pq=state[73:105];pq_counter=int.from_bytes(state[105:109],'big');epoch=int.from_bytes(state[109:117],'big');counter=int.from_bytes(state[1:5],'big')
  rows=[]
  for r in range(4):
   body=c['expected_text'][r].encode();timestamp=c['timestamps'][r];assert len(body)<=48
   content=field(10,field(10,body)+b'\x38'+varint(timestamp));assert len(content)<80
   padded=(content+b'\x80').ljust(80,b'\0');pq_counter+=1
   material=expand(mac(bytes(32),pq),pq_counter.to_bytes(4,'big')+b'Signal PQ Ratchet V1 Chain Next',64);pq=material[:32]
   seed=mac(chain,b'\x01');chain=mac(chain,b'\x02');keys=expand(mac(material[32:],seed),b'WhisperMessageKeys',80)
   rows.append(dict(plain=padded.hex(),cipher_key=keys[:32].hex(),mac_key=keys[32:64].hex(),iv=keys[64:].hex(),sender=state[118:150].hex(),receiver=state[150:182].hex(),ratchet=state[9:41].hex(),addresses='',pq=(b'\x01'+varint(epoch)+varint(pq_counter)+b'\0').hex(),version=state[0],counter=counter+r,previous=int.from_bytes(state[5:9],'big')))
  answer=subprocess.check_output([str(ORACLE)],input=''.join(json.dumps(row)+'\n'for row in rows),text=True)
  wires=[json.loads(line)['wire']for line in answer.splitlines()];assert wires[:2]==c['expected_inner'],'public extension must reproduce frozen first2'
  c['expected_inner']=wires
 return result
