#!/usr/bin/env python3
"""Check shared SHA512/reduction and staged XEdDSA numeric composition.
No h/digest native boundary in composed numeric cases. Canonical conversions
and stage orchestration remain unverified clear tests, not native MPC.
"""
import hashlib,json,re,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from SignalReference.XEdDsaWork.check import WORK,ART,ELL,P,EXPORT,ORACLE,sha,oracle,le,compress,sample,export
from backend_adapter.boolean import load as load_bool
from backend_adapter.aig import statistics
from scripts.check_lean_crypto import evaluate_lanes
from handshake_backend.field_dag import load as load_field,evaluate_clear

def concrete(mode,size,inputs):
 p=subprocess.run([str(EXPORT),'evaluate',mode,str(size)],input=''.join(json.dumps(list(v))+'\n' for v in inputs),text=True,capture_output=True,check=True,timeout=600)
 return [bytes(json.loads(x)) for x in p.stdout.splitlines()]
def main():
 check=ROOT/'SignalReference/XEdDsaChallengeChecks.lean'
 p=subprocess.run(['lake','env','lean',str(check)],cwd=ROOT,text=True,capture_output=True,check=True)
 names=re.findall(r'^#print axioms (\S+)',check.read_text(),re.M)
 found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",p.stdout)
 assert [n for n,_ in found]==names
 for n,a in found:assert not({x.strip() for x in a.split(',') if x.strip()}-{'propext','Quot.sound','Classical.choice'}),(n,a)
 (WORK/'challenge-axioms.txt').write_text(p.stdout)
 rows=[];hashes={}
 # Padding edges, ordinary signed-prekey domain, actual Kyber1024 signed-key domain.
 sizes=sorted({0,1,3,64,65,78,95,97,111,112,127,128,192,239,240,1633})
 all_hash_inputs=[];hash_cases=[]
 for n in sizes:
  data=[sample(f'sha512-{n}-{i}',n) for i in range(4)]
  if n==3:data[0]=b'abc'
  expected=[hashlib.sha512(x).digest() for x in data]
  assert [bytes.fromhex(x.split()[0]) for x in oracle(['hash '+(v.hex() or '-') for v in data])]==expected
  assert concrete('hash',n,data)==expected
  path=export(['boolean','hash',n]);im=load_bool(path)
  assert evaluate_lanes(im,data)==expected,n
  hashes[n]=path
  row={'profile':path.stem,'sha256':sha(path),'numeric_lanes':len(data),'statistics':statistics(im)};rows.append(row)
  print(json.dumps(row),flush=True)
  hash_cases.extend({'input':v.hex(),'sha512':out.hex()} for v,out in zip(data,expected))
 inputs=[bytes(64),b'\xff'*64]+[(ELL+d).to_bytes(64,'little') for d in (-1,0,1)]+[(2**511+d).to_bytes(64,'little') for d in (-1,0,1)]+[sample(f'reduce{i}',64) for i in range(48)]
 expected=[le(int.from_bytes(v,'little')%ELL) for v in inputs]
 assert [bytes.fromhex(x) for x in oracle(['reduce '+v.hex() for v in inputs])]==expected
 assert concrete('reduce',64,inputs)==expected
 path=export(['boolean','reduce',64]);reduce=load_bool(path)
 assert evaluate_lanes(reduce,inputs)==expected
 rows.append({'profile':path.stem,'sha256':sha(path),'numeric_lanes':len(inputs),'statistics':statistics(reduce)})
 fields={mode:[load_field(ART/f'signal-xeddsa-field-{mode}-{i}.json') for i in range(count)] for mode,count in [('recover',3),('double',2)]}
 def field(mode,inp):return [evaluate_clear(im,inp)[0] for im in fields[mode]]
 fixtures=json.loads((WORK/'fixtures.json').read_text())['composed_native_hash_boundary']
 groups={};states={};composed=[]
 for idx,row in enumerate(fixtures):
  key=bytes.fromhex(row['key']);sig=bytes.fromhex(row['signature']);msg=bytes.fromhex(row['message'])
  if len(sig)!=64 or sig[-1]&96:
   assert not row['accepted'];composed.append({'label':row['label'],'accepted':False,'path':'byte_rejection'});continue
  valid,x,y=field('recover',[(int.from_bytes(key[1:],'little')%(2**255))%P])
  if not valid:
   assert not row['accepted'];composed.append({'label':row['label'],'accepted':False,'path':'recovery_rejection'});continue
  if (x&1)!=(sig[-1]>>7):x=(-x)%P
  data=sig[:32]+compress(x,y)+msg
  groups.setdefault(len(data),[]).append((idx,data));states[idx]=(sig,msg,x,y)
 for n,items in groups.items():
  digests=evaluate_lanes(load_bool(hashes[n]),[v for _,v in items])
  hh=evaluate_lanes(reduce,digests)
  for (idx,data),hbytes in zip(items,hh):
   row=fixtures[idx];sig,msg,x,y=states[idx]
   assert hbytes.hex()==row['native_h']
   h=int.from_bytes(hbytes,'little');s=int.from_bytes(sig[32:],'little')%(2**255)
   rx,ry=field('double',[x,y]+[(h>>i)&1 for i in range(256)]+[(s>>i)&1 for i in range(253)])
   result=evaluate_lanes(load_bool(ART/'signal-xeddsa-match.json'),[sig+le(rx)+le(ry)])[0]==b'\xff'
   assert result==row['accepted'],row['label']
   composed.append({'label':row['label'],'accepted':result,'path':'all_numeric_crypto','h':hbytes.hex()})
 # A monolithic challenge profile checks hash/remainder serialization composition.
 path=export(['boolean','challenge',33]);challenge=load_bool(path)
 selected=[(idx,v) for idx,v in states.items() if len(v[1])==33]
 selected=selected[:4]
 raw=[sig+le(x)+le(y)+msg for _,(sig,msg,x,y) in selected]
 expected=[bytes.fromhex(fixtures[idx]['native_h']) for idx,_ in selected]
 assert concrete('challenge',33,raw)==expected
 assert evaluate_lanes(challenge,raw)==expected
 rows.append({'profile':path.stem,'sha256':sha(path),'numeric_lanes':len(raw),'statistics':statistics(challenge)})
 (WORK/'challenge-fixtures.json').write_text(json.dumps({'hash':hash_cases,'reduction':[{'input':v.hex(),'output':o.hex()} for v,o in zip(inputs,[le(int.from_bytes(v,'little')%ELL) for v in inputs])],'composition':composed},indent=2)+'\n')
 sources=set()
 def visit(mod):
  if not mod.startswith('TlsMpc'):return
  p=ROOT/(mod.replace('.','/')+'.lean')
  if p in sources:return
  sources.add(p)
  for m in re.findall(r'^import ([\w.]+)',p.read_text(),re.M):visit(m)
 visit('TlsMpc.Signal.XEdDsaChallenge');visit('TlsMpc.Signal.XEdDsaField')
 sources|={Path(__file__),WORK/'check.py',check,WORK/'Export.lean',ROOT/'SignalReference/XEdDsaExport.lean',WORK/'Oracle/src/main.rs',WORK/'Oracle/Cargo.lock',WORK/'fixtures.json',WORK/'report.json',ROOT/'handshake_backend/field_dag.py',ROOT/'scripts/check_lean_crypto.py',ROOT/'backend_adapter/aig.py',ROOT/'backend_adapter/boolean.py'}
 report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'proof_endpoints':len(names),'custom_axioms':[],'source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in sorted(sources)},
  'oracle_binary_sha256':sha(ORACLE),'export_binary_sha256':sha(EXPORT),'fixtures_sha256':sha(WORK/'challenge-fixtures.json'),'profiles':rows,
  'sha512_numeric_lanes':len(hash_cases),'scalar_reduction_numeric_lanes':len(inputs),'complete_staged_numeric_cases':len(composed),
  'full_numeric_crypto_paths':sum(r['path']=='all_numeric_crypto' for r in composed),'native_hash_input_boundary':False,
  'native_mpc_executed':False,'actual_aeneas_refinement':False,'pqxdh_validation_status_produced':False,
  'scope':'Numeric SHA512/remainder/recovery/double-scalar/compressed-R checks agree with actual unchanged libsignal/dalek on public fixtures. Per-stage compiler proofs; exact 512-bit little-endian modulo-ell input and output byte specification. Stage conversion/binding remains clear Python, not an MPC runtime proof.',
  'remaining':['proved and shared canonical field/byte conversion plus sign binding composition','actual libsignal/dalek/RustCrypto Aeneas refinement','prekey trust policy','native five-party malicious statistical128 runtime']}
 (WORK/'challenge-report.json').write_text(json.dumps(report,indent=2)+'\n')
 print('all challenge and staged checks passed',flush=True)
if __name__=='__main__':main()
