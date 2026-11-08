#!/usr/bin/env python3
"""PUBLIC selected-established-phase fixtures, actual pinned spqr::recv oracle."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes
HERE=Path(__file__).resolve().parent;WORK=ROOT/'SignalReference/ActiveSpqrReceiveWork'
ART=ROOT/'.deps/private-hash-artifacts/active-spqr-receive-next.json'
BIN=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-active-spqr-receive-oracle'
def varint(n):
 out=bytearray()
 while n>=128:out.append((n&127)|128);n>>=7
 return bytes(out)+bytes([n])
def long(n):
 b=varint(n)
 while len(b)<10:b=b[:-1]+bytes([b[-1]|128,0])
 return b

def main():
 audit=subprocess.check_output(['lake','env','lean',str(WORK/'Checks.lean')],cwd=ROOT,text=True)
 groups=re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S);assert len(groups)==6
 for g in groups:assert set(re.findall(r'[\w.]+',g))<={'propext','Classical.choice','Quot.sound'}
 rows=[];expected=[];oracle_rows=[]
 def raw(epoch,key,counter,wire,status=255,length=None):
  assert len(wire)<=32
  return epoch.to_bytes(8,'big')+key+counter.to_bytes(4,'big')+bytes([status])+(len(wire)if length is None else length).to_bytes(2,'big')+wire+bytes(32-len(wire))
 for epoch in [1,127,128,2**32,2**63,2**64-1]:
  for counter in [0,126,127,16382,16383,2**31-2]:
   key=hashlib.sha256(f'public-active-pqr-{epoch}-{counter}'.encode()).digest()
   wire=b'\1'+varint(epoch)+varint(counter+1)+b'\0';rows.append(raw(epoch,key,counter,wire))
   oracle_rows.append(dict(epoch=epoch,counter=counter,chain=key.hex(),wire=wire.hex()))
 key=bytes(range(32))
 for wire in [b'\1'+long(127)+varint(128)+b'\0',b'\1'+long(127)+long(128)+b'\0',b'\1'+varint(127)+varint(128)+b'\0junk']:
  rows.append(raw(127,key,127,wire));oracle_rows.append(dict(epoch=127,counter=127,chain=key.hex(),wire=wire.hex()))
 actual=subprocess.run([str(BIN)],input=''.join(json.dumps(x)+'\n'for x in oracle_rows),text=True,capture_output=True,check=True)
 answers=list(map(json.loads,actual.stdout.splitlines()));assert len(answers)==len(rows)
 for req,answer in zip(oracle_rows,answers):
  assert answer['accepted']
  expected.append(b'\xff'+req['epoch'].to_bytes(8,'big')+bytes.fromhex(answer['chain'])+answer['counter'].to_bytes(4,'big')+bytes.fromhex(answer['key']))
 valid=len(rows);wire=b'\1'+varint(127)+varint(128)+b'\0'
 bad=[]
 # Truncation must never use capacity padding as a missing kind/varint byte.
 for length in range(len(wire)):bad.append(raw(127,key,127,wire[:length]))
 for status in [0,1,127,254]:bad.append(raw(127,key,127,wire,status=status))
 bad.append(raw(127,key,127,wire,length=33))
 for wrong in [b'\0'+wire[1:],wire[:-1]+b'\4',wire[:-1]+b'\1',b'\1'+varint(128)+varint(128)+b'\0',b'\1'+varint(127)+varint(127)+b'\0',b'\1'+varint(127)+varint(129)+b'\0',b'\1'+varint(127)+varint(2**32)+b'\0']:
  bad.append(raw(127,key,127,wrong))
 bad.append(raw(127,key,2**32-1,wire))
 bad.append(raw(127,key,2**32-2,wire))
 bad.append(raw(127,key,2**31-1,wire))
 for row in bad:rows.append(row);expected.append(b'\0'+row[:44]+bytes(32))
 image=load(ART);out=evaluate_lanes(image,rows)
 for index,(actual,want)in enumerate(zip(out,expected)):assert actual==want,(index,actual.hex(),want.hex())
 files=[Path(__file__),WORK/'Checks.lean',WORK/'Export.lean',ROOT/'TlsMpc/Signal/ActiveSpqrReceive.lean',ROOT/'signal_backend/Oracle/src/bin/signal-active-spqr-receive-oracle.rs',ROOT/'signal_backend/Oracle/Cargo.toml',ROOT/'signal_backend/Oracle/Cargo.lock']
 report=dict(actual_pinned_spqr_receive_matches=valid,failclosed_rejections=len(bad),kernel_endpoints=6,foundation_axioms_only=True,
  actual_source='SparsePostQuantumRatchetv1.6.0 commit06959b4708f9b7b1e94d0f8cc835f3958c077e94, same locked git dependency aslibsignal904c8dc',
  domain='Selected established V1 KeysUnsampled active epoch; kind0, retained counter<2^31-1, exact next receiving index, capacity32, private actual length. Candidate only: outer Signal authentication required before commit.',
  repeated_state_roundtrip_tested=False,full_KEM_epoch_transition=False,full_DH_transition=False,native_MPC_executed=False,actual_source_refinement_proved=False,
  numeric_nodes=len(image['nodes']),artifact_sha256=hashlib.sha256(ART.read_bytes()).hexdigest(),
  source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in files})
 (HERE/'active-spqr-report.json').write_text(json.dumps(report,indent=2)+'\n');print(f'{valid} actual spqr::recv matches;{len(bad)} private-wire/state rejections;6kernel endpoints passed')
if __name__=='__main__':main()
