#!/usr/bin/env python3
"""Variable inner prefixes against actual pinned SSv1 (public DH fixtures)."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from backend_adapter.boolean import load
from scripts.check_lean_crypto import evaluate_lanes
HERE=Path(__file__).resolve().parent;ART=ROOT/'.deps/private-hash-artifacts'
ORACLE=ROOT/'.deps/signal-established-send-oracle-target/debug/signal-established-send-oracle'
def oracle(rows):
 r=subprocess.run([str(ORACLE)],input=''.join(json.dumps(x)+'\n' for x in rows),text=True,capture_output=True,check=True)
 return [json.loads(x) for x in r.stdout.splitlines()]
def main():
 cap=80;path=ART/'private-sealed-260-80.json';values=[0,1,63,64,71,72,73,80]
 subprocess.run(['lake','build','TlsMpc.Signal.PrivateSealedSender'],cwd=ROOT,check=True)
 audit=subprocess.check_output(['lake','env','lean',str(HERE/'Checks.lean')],cwd=ROOT,text=True)
 for group in re.findall(r'depends on axioms: \[(.*?)\]',audit,re.S):assert set(re.findall(r'[\w.]+',group))<={'propext','Classical.choice','Quot.sound'}
 assert 'sorryAx' not in audit;(HERE/'axioms.txt').write_text(audit)
 with path.open('w') as stream:subprocess.run(['lake','env','lean','--run',str(HERE/'Export.lean'),'260',str(cap)],cwd=ROOT,stdout=stream,check=True)

 fixtures=oracle([dict(mode='sealed',seed=0,inner=bytes(i%256 for i in range(n)).hex()) for n in values])
 raw=[];wire=[]
 for n,f in zip(values,fixtures):
  b=bytes.fromhex(f['input']);assert f['certificate_size']==260
  raw.append(b[:420]+b[64:96]+b'\xff'+n.to_bytes(2,'big')+b[420:]+bytes(cap-n));wire.append(bytes.fromhex(f['wire']))
 for kind in ['invalid-status','overflow','zero-dh','wrong-sender']:
  b=bytearray(raw[-1])
  if kind=='invalid-status':b[452]=0
  if kind=='overflow':b[453:455]=(cap+1).to_bytes(2,'big')
  if kind=='zero-dh':b[96:128]=bytes(32)
  if kind=='wrong-sender':b[420]^=1
  raw.append(bytes(b));wire.append(None)
 image=load(path);observed=evaluate_lanes(image,raw);outcap=len(observed[0])-3
 for i,(b,w) in enumerate(zip(observed,wire)):
  expected=b'\xff'+len(w).to_bytes(2,'big')+w+bytes(outcap-len(w)) if w is not None else bytes(outcap+3)
  assert b==expected,(i,b[:4].hex(),expected[:4].hex())
 del image
 files=[Path(__file__),HERE/'Export.lean',HERE/'Checks.lean',ROOT/'TlsMpc/Signal/PrivateSealedSender.lean',ROOT/'TlsMpc/Signal/PrivateProtobuf.lean',ROOT/'TlsMpc/Signal/PrivateHash.lean',ROOT/'TlsMpc/Signal/PrivateBuffer.lean']
 report={'actual_ssv1_prefix_cases':len(values),'rejection_cases':4,'input_inner_capacity':cap,'output_capacity':outcap,
  'same_artifact_variable_lengths':True,'supplied_dh_fixture_only':True,'native_computed_dh_executed':False,
  'compiler_theorem_established':True,'standard_axioms_only':True,'integer_semantic_refinement_proved':False,'service_integrated':False,
  'artifact_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'artifact_bytes':path.stat().st_size,
  'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},'oracle_sha256':hashlib.sha256(ORACLE.read_bytes()).hexdigest()}
 (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(f'{len(values)} variable SSv1 prefixes and4 rejection cases passed; capacity{outcap}',flush=True)
if __name__=='__main__':main()
