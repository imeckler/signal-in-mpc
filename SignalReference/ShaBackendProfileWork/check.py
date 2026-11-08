#!/usr/bin/env python3
"""Public profile propagation/equivalence checks; no native MPC claim."""
from pathlib import Path
import hashlib,hmac,json,random,subprocess,sys
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).parent
sys.path.insert(0,str(ROOT))
from backend_adapter.aig import execute,statistics
from backend_adapter.aig_packed import plan
STAGE=ROOT/'.deps/sha-backend-profiles';STAGE.mkdir(exist_ok=True)
def evaluate(image,values):
 one=(1<<len(values))-1
 bits=[sum(((v[k//8]>>(7-k%8))&1)<<i for i,v in enumerate(values)) for k in range(image['input_bits'])]
 out=execute(image,bits,0,one);results=[]
 for i in range(len(values)):
  raw=bytearray(len(out)//8)
  for k,b in enumerate(out):raw[k//8]|=((b>>i)&1)<<(7-k%8)
  results.append(bytes(raw))
 return results
rng=random.Random(9812);reports={};cases=0
iv=bytes.fromhex('6a09e667bb67ae853c6ef372a54ff53a510e527f9b05688c1f83d9ab5be0cd19')
for operation in ['block','hmac','hkdf','private-hmac']:
 values=[rng.randbytes(96 if operation=='block' else 48) for _ in range(8)]
 expected=None
 if operation=='block':
  messages=[b'',b'abc'];values=[iv+m+b'\x80'+bytes(55-len(m))+(8*len(m)).to_bytes(8,'big') for m in messages]+values
 elif operation=='private-hmac':
  values=[v[:32]+b'\xff'+n.to_bytes(2,'big')+v[32:] for v,n in zip(values,[0,1,2,7,8,15,16,16])]
 for profile in ['reference','gate-efficient','latency']:
  path=STAGE/f'{profile}-{operation}.json'
  if not path.exists():
   with path.open('w') as output:subprocess.run(['lake','env','lean','--run',str(WORK/'Export.lean'),profile,operation],cwd=ROOT,stdout=output,check=True,timeout=180)
  image=json.loads(path.read_text());assert image['sha_profile']==profile
  result=evaluate(image,values)
  if expected is None:expected=result
  assert result==expected,(profile,operation)
  if operation=='block':
   assert result[:2]==[hashlib.sha256(m).digest() for m in messages]
  for v,out in zip(values,result):
   if operation=='hmac':assert out==hmac.digest(v[:32],v[32:],'sha256')
   elif operation=='hkdf':assert out==hmac.digest(v[:32],v[32:]+b'\x01','sha256')
   elif operation=='private-hmac':assert out==b'\xff\x00\x20'+hmac.digest(v[:32],v[35:35+int.from_bytes(v[33:35],'big')],'sha256')
  _,groups=plan(image);metric=statistics(image);metric.update(and_depth=max(k[0] for k,g in groups),artifact_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
  reports[f'{profile}/{operation}']=metric;cases+=len(values)
axioms=(WORK/'axioms.txt').read_text();assert 'sorryAx'not in axioms and 'ofReduce'not in axioms
sources=[ROOT/'TlsMpc/Sha256.lean',ROOT/'TlsMpc/Sha256Backend.lean',ROOT/'TlsMpc/Signal/ShaCompact.lean',ROOT/'TlsMpc/Signal/PrivateConversationBackend.lean',ROOT/'SignalReference/PrivateConversationWork/Export.lean',ROOT/'programs/signal_variable_service.mpc',ROOT/'signal_backend/VariableServiceWork/prepare.py',WORK/'Export.lean',Path(__file__)]
report=dict(passed=True,public_numeric_cases=cases,profiles=reports,native_MPC_executed=False,full_service_rebuilt=False,source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in sources})
(WORK/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'passed':True,'cases':cases,'profiles':len(reports)}))
