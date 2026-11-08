#!/usr/bin/env python3
"""Private JSON/protobuf/WS lengths against actual generated Signal schema."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes
from SignalReference.RelayServiceWork.check import metadata,oracle
HERE=Path(__file__).resolve().parent;ART=ROOT/'.deps/private-hash-artifacts'
def main():
 cap=16;path=ART/'private-relay-16.json'
 subprocess.run(['lake','build','TlsMpc.Signal.PrivateRelay'],cwd=ROOT,check=True)
 audit=subprocess.check_output(['lake','env','lean',str(HERE/'Checks.lean')],cwd=ROOT,text=True)
 for group in re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S):assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx' not in audit;(HERE/'axioms.txt').write_text(audit)
 with path.open('w') as stream:subprocess.run(['lake','env','lean','--run',str(HERE/'Export.lean'),str(cap)],cwd=ROOT,stdout=stream,check=True)
 raw=[];descriptions=[]
 for i,(n,timestamp,ident,device,reg) in enumerate([(0,0,0,1,0),(1,9,127,9,9),(2,10,128,10,10),(3,99,16383,99,16383),(4,100,16384,100,16384),(15,10**19,2**63,127,2**32-1),(16,2**64-1,2**64-1,255,2**32-1)]):
  m=bytearray(metadata(i,ident));m[32:40]=timestamp.to_bytes(8,'big');m[48]=device;m[49:53]=reg.to_bytes(4,'big')
  cipher=bytes(range(n));raw.append(bytes(m)+b'\xff'+n.to_bytes(2,'big')+cipher+bytes(cap-n));descriptions.append((bytes(m),cipher,timestamp,ident,device,reg))
 for status,n in [(0,0),(254,0),(255,cap+1)]:raw.append(metadata()+bytes([status])+n.to_bytes(2,'big')+bytes(cap))
 output=evaluate_lanes(load(path),raw)
 rows=[]
 for b in output[:len(descriptions)]:
  assert b[0]==255
  n=int.from_bytes(b[1:3],'big');assert b[3+n:]==bytes(len(b)-3-n)
  rows.append(dict(mode='relay',wire=b[3:3+n].hex()))
 decoded=oracle(rows)
 for answer,(m,cipher,timestamp,ident,device,reg) in zip(decoded,descriptions):
  assert answer['ciphertext']==cipher.hex() and answer['access_key']==m[16:32].hex() and answer['id']==ident
  body=answer['body'];assert body['timestamp']==timestamp and body['online']==False and body['urgent']==True
  message=body['messages'][0];assert message['destinationDeviceId']==device and message['destinationRegistrationId']==reg and message['type']==6
 assert all(x==bytes(len(x)) for x in output[len(descriptions):])
 files=[Path(__file__),HERE/'Export.lean',HERE/'Checks.lean']+[ROOT/f'TlsMpc/Signal/{x}.lean' for x in ['PrivateRelay','PrivateDecimal','PrivateBase64','PrivateProtobuf','PrivateBuffer']]
 report={'actual_schema_cases':len(descriptions),'rejection_cases':3,'shared_numeric_and_ciphertext_lengths':True,
  'output_capacity':len(output[0])-3,'artifact_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
  'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
  'compiler_theorem_established':True,'standard_axioms_only':True,'integer_semantic_refinement_proved':False,'native_mpc_executed':False,
  'device_registration_values':'Encodes bounded integer domain; authenticated device-store membership/range remains a separate boundary.'}
 (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n');print('7 actual schema variable-width relay matches;3 canonical rejections passed',flush=True)
if __name__=='__main__':main()
