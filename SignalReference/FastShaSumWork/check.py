#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,hashlib as oracle,random,subprocess,sys
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).parent;STAGE=ROOT/'.deps/sha-carry-save';STAGE.mkdir(exist_ok=True)
sys.path.insert(0,str(ROOT));from backend_adapter.aig import execute,statistics
from backend_adapter.aig_packed import plan
rng=random.Random(31891);reports={};total=0
iv=bytes.fromhex('6a09e667bb67ae853c6ef372a54ff53a510e527f9b05688c1f83d9ab5be0cd19')
def packed(image,values):
 assert all(len(v)*8==image['input_bits'] for v in values)
 results=[]
 for start in range(0,len(values),64):
  chunk=values[start:start+64];one=(1<<len(chunk))-1
  bits=[sum(((v[k//8]>>(7-k%8))&1)<<i for i,v in enumerate(chunk)) for k in range(image['input_bits'])]
  out=execute(image,bits,0,one)
  for i in range(len(chunk)):
   result=bytearray(len(out)//8)
   for k,b in enumerate(out):result[k//8]|=((b>>i)&1)<<(7-k%8)
   results.append(bytes(result))
 return results
for profile,count in [('double',4),('pair3',12),('sum5',20),('block-state',96)]:
 values=[bytes(count),b'\xff'*count]+[rng.randbytes(count) for _ in range(128)]
 if profile=='block-state':
  for message in [b'',b'abc',b'known public SHA fixture']:
   block=message+b'\x80'+bytes(55-len(message))+(8*len(message)).to_bytes(8,'big');values.append(iv+block)
 versions={};metrics={}
 for version in ['legacy','carry']:
  p=STAGE/f'{version}-{profile}.json'
  if not p.exists():
   run=subprocess.run(['lake','env','lean','--run',str(WORK/'Export.lean'),version,profile],cwd=ROOT,capture_output=True,text=True,check=True,timeout=120);p.write_text(run.stdout)
  image=json.load(p.open());versions[version]=packed(image,values);_,groups=plan(image);s=statistics(image);s.update(and_depth=max((k[0]for k,g in groups),default=0),local_xor_depth=max((k[1]for k,g in groups),default=0),artifact_sha256=hashlib.sha256(p.read_bytes()).hexdigest());metrics[version]=s
 assert versions['legacy']==versions['carry'],profile
 for raw,out in zip(values,versions['carry']):
  words=[int.from_bytes(raw[i:i+4],'big') for i in range(0,len(raw),4)]
  if profile=='double':assert int.from_bytes(out,'big')==(2*words[0])&0xffffffff
  elif profile=='sum5':assert int.from_bytes(out,'big')==sum(words)&0xffffffff
  elif profile=='pair3':
   a,b,c=words;assert out==((a^b^c).to_bytes(4,'big')+((((a&b)^((a^b)&c))*2)&0xffffffff).to_bytes(4,'big'))
 if profile=='block-state':
  for message,out in zip([b'',b'abc',b'known public SHA fixture'],versions['carry'][-3:]):assert out==oracle.sha256(message).digest()
 total+=2*len(values);reports[profile]=metrics
axioms=(WORK/'axioms.txt').read_text();assert 'sorryAx' not in axioms and 'ofReduce' not in axioms
report=dict(passed=True,public_numeric_cases=total,actual_hashlib_vectors=3,profiles=reports,native_MPC_executed=False,source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [ROOT/'TlsMpc/Sha256CarrySave.lean',ROOT/'TlsMpc/Sha256.lean',WORK/'Export.lean',Path(__file__)]},scope='carry-save pairs/full final CPA and arbitrary-state compression compared to old kernel; no production integration or latency claim')
(WORK/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'passed':True,'cases':total,'profiles':reports},indent=2))
