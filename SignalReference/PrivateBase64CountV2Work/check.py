#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,subprocess,sys,time
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).parent;STAGE=ROOT/'.deps/private-base64-count-v2'
sys.path.insert(0,str(ROOT));from backend_adapter.aig import execute,statistics
from backend_adapter.aig_packed import plan
rng=random.Random(598131);STAGE.mkdir(exist_ok=True);receipt={};cases=0

def test(image,values,groups,state):
 global cases
 for start in range(0,len(values),64):
  chunk=values[start:start+64];ones=(1<<len(chunk))-1;raw=[n.to_bytes(2,'big')+(total.to_bytes(2,'big') if state else b'') for n,total in chunk]
  bits=[sum(((r[k//8]>>(7-k%8))&1)<<i for i,r in enumerate(raw)) for k in range(image['input_bits'])]
  output=execute(image,bits,0,ones)
  expected=[(total+4*min(groups,(n+2)//3))&65535 for n,total in chunk]
  wanted=[sum(((n>>(15-k))&1)<<i for i,n in enumerate(expected)) for k in range(16)]
  assert output==wanted,(image['name'],start)
  cases+=len(chunk)

for groups in [0,1,2,3,64,192,256,1024]:
 for state in [False,True]:
  mode='state' if state else 'fixed';key=f'{groups}-{mode}';receipt[key]={}
  values=[(n,0 if not state else total) for n in [0,1,2,3,4,3*groups-1,3*groups,3*groups+1,65533,65534,65535] if 0<=n<65536 for total in ([0,1,65534,65535] if state else [0])]
  values += [(rng.randrange(65536),rng.randrange(65536) if state else 0) for _ in range(64)]
  if groups==192 and not state:values=[(n,0) for n in range(65536)]
  for version in ['legacy','balanced']:
   p=STAGE/f'{version}-{key}.json';completed=subprocess.run(['lake','env','lean','--run',str(WORK/'Export.lean'),version,str(groups),mode],cwd=ROOT,capture_output=True,text=True,check=True,timeout=120);p.write_text(completed.stdout);image=json.loads(completed.stdout)
   test(image,values,groups,state);_,grouped=plan(image);metrics=statistics(image);metrics.update(and_depth=max((k[0]for k,g in grouped),default=0),local_xor_depth=max((k[1]for k,g in grouped),default=0),sha256=hashlib.sha256(p.read_bytes()).hexdigest());receipt[key][version]=metrics
axioms=Path('/tmp/tls-base64-count-v2-axioms.log').read_text();assert 'sorryAx' not in axioms and 'Lean.ofReduceBool' not in axioms and 'error' not in axioms
report=dict(passed=True,native_MPC_executed=False,public_numeric_cases=cases,exhaustive_16bit_length_profile='192-fixed, both kernels',proof_scope='Complete concrete encode equivalence for arbitrary malformed/internal Buffer values after normalization; arbitrary canonical length bits, arbitrary public index lists, arbitrary16bit initial total; exact modulo65536 including overflow and wrapped public comparisons',producer_integrated=False,normalized_buffer_composition_proof=True,profiles=receipt,axioms=axioms.splitlines(),source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [ROOT/'TlsMpc/Signal/PrivateBase64CountV2.lean',WORK/'Export.lean',WORK/'Checks.lean',Path(__file__)]})
(WORK/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'passed':True,'cases':cases,'profile192':receipt['192-fixed']},indent=2))
