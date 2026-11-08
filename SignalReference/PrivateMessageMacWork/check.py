#!/usr/bin/env python3
"""PUBLIC actual pinned Signal MAC differential with a secret actual wire end."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes
from SignalReference.RelayServiceWork.check import oracle
HERE=Path(__file__).resolve().parent
ART=ROOT/'.deps/private-hash-artifacts/private-message-mac-256.json'
BIN=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-private-message-mac-oracle'
def main():
 audit=subprocess.check_output(['lake','env','lean',str(HERE/'Checks.lean')],cwd=ROOT,text=True)
 groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S);assert len(groups)==4
 for g in groups:assert set(re.findall(r'[\w.]+',g))<={'propext','Classical.choice','Quot.sound'}
 digest=lambda text:hashlib.sha256(text.encode()).digest()
 requests=[]
 for n in [0,1,15,16,31,48,80,96]:
  for counter in [0,127,128,2**32-1]:
   requests.append(dict(plain=(digest('text')*4)[:n].hex(),cipher_key=digest('cipher').hex(),iv=digest('iv')[:16].hex(),mac_key=digest('mac').hex(),sender=digest('sender').hex(),receiver=digest('receiver').hex(),ratchet=digest('ratchet').hex(),addresses='',pq='017f7f00',version=4,counter=counter,previous=counter))
 wires=[bytes.fromhex(answer['wire'])for answer in oracle(requests)]
 rows=[];expected=[];actual_rows=[];actual_expected=[]
 def add(req,wire,status=255,length=None,want=True,pad=0):
  assert len(wire)<=256
  row=bytes.fromhex(req['mac_key']+req['sender']+req['receiver'])+bytes([status])+(len(wire)if length is None else length).to_bytes(2,'big')+wire+bytes([pad])*(256-len(wire))
  rows.append(row);expected.append(bytes([255 if want else 0]))
 for req,wire in zip(requests,wires):
  add(req,wire);actual_rows.append(dict(req,wire=wire.hex()));actual_expected.append(True)
  add(req,wire,pad=255) # Capacity tail is not authenticated data.
  for index in [len(wire)-1,45]:
   bad=bytearray(wire);bad[index]^=1;add(req,bytes(bad),want=False)
   actual_rows.append(dict(req,wire=bad.hex()));actual_expected.append(False)
  for key in ['mac_key','sender','receiver']:
   bad=dict(req);b=bytearray.fromhex(bad[key]);b[0]^=1;bad[key]=b.hex();add(bad,wire,want=False)
   actual_rows.append(dict(bad,wire=wire.hex()));actual_expected.append(False)
  add(req,wire,length=len(wire)-1,want=False)
  add(req,wire,length=len(wire)+1,want=False)
 for status in [0,1,127,254]:add(requests[0],wires[0],status=status,want=False)
 for length in [0,1,8,9,257,65535]:add(requests[0],wires[0],length=length,want=False)
 actual=subprocess.run([str(BIN)],input=''.join(json.dumps(r)+'\n'for r in actual_rows),text=True,capture_output=True,check=True)
 answers=list(map(json.loads,actual.stdout.splitlines()));assert len(answers)==len(actual_expected)
 assert [r['accepted']for r in answers]==actual_expected
 image=load(ART);outputs=evaluate_lanes(image,rows)
 for index,(got,want)in enumerate(zip(outputs,expected)):assert got==want,(index,got.hex(),want.hex())
 files=[Path(__file__),HERE/'Export.lean',HERE/'Checks.lean',ROOT/'TlsMpc/Signal/PrivateMessageMac.lean',ROOT/'signal_backend/Oracle/src/bin/signal-private-message-mac-oracle.rs']
 report=dict(numeric_cases=len(rows),actual_pinned_SignalMessage_parse_verify_MAC_cases=len(actual_rows),kernel_endpoints=4,foundation_axioms_only=True,
  domain='Publiccapacity256, sharedvalidity/BE16actualwirelength; actualSignalMessagev4 noaddresses; identities/MACkey32B. Original contentprefix andlast8tag selected privately, capacitytail ignored.',
  full_protobuf_validation=False,full_DH_or_session_transition=False,actual_RustCrypto_source_refinement_proved=False,native_MPC_executed=False,
  pending='Use actual privateparser.valid and original-wireMAC result jointly withCBC/PQ/DH computed acceptance before committing fullsession state.',
  numeric_nodes=len(image['nodes']),artifact_sha256=hashlib.sha256(ART.read_bytes()).hexdigest(),oracle_sha256=hashlib.sha256(BIN.read_bytes()).hexdigest(),
  source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files})
 (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(f'{len(rows)} private-prefix cases/{len(actual_rows)} actual Rust MAC cases/4kernel endpoints passed')
if __name__=='__main__':main()
