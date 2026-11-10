#!/usr/bin/env python3
"""Public all-numeric execution of branch-free shared-stage XEdDSA adapter."""
import json,re,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from SignalReference.XEdDsaWork.check import WORK,ART,sha,le,export,P
from SignalReference.XEdDsaWork.adapter import verify
from backend_adapter.boolean import load as load_bool
from backend_adapter.aig import statistics
from scripts.check_lean_crypto import evaluate_lanes
from handshake_backend.field_dag import load as load_field,evaluate_clear

class PublicConversions:
 def decode_u(self,raw):return (int.from_bytes(raw,'little')%(2**255))%P
 def encode_field(self,x):return le(x)
 def bits_to_field(self,raw,count):return [(raw[i//8]>>(i%8))&1 for i in range(count)]
class Stages:
 def __init__(self):self.calls=0;self.fields={};self.booleans={};self.max_live_hashes=0
 def field(self,mode,index,inputs):
  key=(mode,index)
  if key not in self.fields:self.fields[key]=load_field(ART/f'signal-xeddsa-field-{mode}-{index}.json')
  self.calls+=1
  return evaluate_clear(self.fields[key],inputs)
 def boolean(self,mode,size,inputs):
  key=(mode,size)
  if key not in self.booleans:
   # Keep one public hash-size image at a time; these artifacts can be large.
   for old in list(self.booleans):
    if old[0]=='hash':del self.booleans[old]
   self.booleans[key]=load_bool(ART/f'signal-xeddsa-boolean-{mode}-{size}.json')
  self.calls+=1
  return evaluate_lanes(self.booleans[key],[inputs])[0]
def main():
 check=ROOT/'SignalReference/XEdDsaBindingChecks.lean'
 p=subprocess.run(['lake','env','lean',str(check)],cwd=ROOT,text=True,capture_output=True,check=True)
 names=re.findall(r'^#print axioms (\S+)',check.read_text(),re.M)
 found=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",p.stdout)
 assert [n for n,_ in found]==names
 for n,a in found:assert not({x.strip() for x in a.split(',') if x.strip()}-{'propext','Quot.sound','Classical.choice'}),(n,a)
 (WORK/'binding-axioms.txt').write_text(p.stdout)
 profiles=[]
 for mode,index in [('signed',0),('signed',1)]:
  path=export(['field',mode,index]);im=load_field(path)
  profiles.append({'profile':path.stem,'sha256':sha(path),'nodes':len(im['nodes']),'field_multiplications':sum(n['op']=='mul' for n in im['nodes'])})
 for mode,size in [('binding',128),('finish',160)]:
  path=export(['boolean',mode,size]);im=load_bool(path)
  profiles.append({'profile':path.stem,'sha256':sha(path),'statistics':statistics(im)})
 fixtures=json.loads((WORK/'fixtures.json').read_text())['composed_native_hash_boundary']
 # Whole adapter intentionally performs every stage even on secret rejection.
 # Select representative valid, tampered, scalar-envelope, malformed-u and x=0 cases.
 labels={'pinned','pinned-S-plus-ell','mutated-0','mutated-63','generated-0','generated-1','generated-2','generated-3','generated-4','generated-5','generated-6','generated-7'}
 selected=[f for f in fixtures if f['label'] in labels or f['label'].startswith(('low-order-','special-u-','high-bits-'))]
 selected.sort(key=lambda f:len(bytes.fromhex(f['message'])))
 stages=Stages();conversion=PublicConversions();rows=[]
 for row in selected:
  key=bytes.fromhex(row['key'])[1:];sig=bytes.fromhex(row['signature']);msg=bytes.fromhex(row['message'])
  out=verify(stages,conversion,key,sig,msg)
  assert out==bytes([255 if row['accepted'] else 0]),row['label']
  rows.append({'label':row['label'],'accepted':row['accepted'],'output':out.hex()})
  print(row['label'],out.hex(),flush=True)
 sources={Path(__file__),WORK/'adapter.py',check,WORK/'Export.lean',ROOT/'SignalReference/XEdDsaExport.lean',ROOT/'TlsMpc/Signal/XEdDsaBinding.lean',ROOT/'TlsMpc/Signal/XEdDsaField.lean',WORK/'fixtures.json',WORK/'challenge-report.json',WORK/'report.json'}
 report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'proof_endpoints':len(names),'custom_axioms':[],
  'source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in sorted(sources)},'profiles':profiles,'full_adapter_cases':len(rows),'numeric_stage_calls':stages.calls,'cases':rows,
  'native_hash_boundary':False,'trusted_validation_boolean_input':False,'secret_dependent_host_branches':False,
  'native_mpc_executed':False,'actual_aeneas_refinement':False,'pqxdh_wired':False,
  'conversion_boundary':'Abstract shared conversion interface, instantiated only with public canonical arithmetic in tests. Private conversion fidelity/security and composed compiler theorem are not established.',
  'scope':'All cryptographic computation, sign binding and final conjunction executed by numeric Lean artifacts; adapter routes only shared registers and public lengths. Exact pinned libsignal fixture outcomes including small-order and noncanonical acceptance.',
  'security_required':{'parties':5,'malicious':2,'statistical_security':128,'abort_allowed':True,'runtime_validated':False}}
 (WORK/'binding-report.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
