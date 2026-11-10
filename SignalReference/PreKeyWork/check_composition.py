#!/usr/bin/env python3
"""Full public numeric two-signature bundle prefix via frozen XEdDSA adapter."""
import json,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT))
from SignalReference.PreKeyWork.check import WORK,ART,XWORK,sha,artifact,metadata,expected_result,frozen_check
from SignalReference.PreKeyWork.adapter import validate
from backend_adapter.boolean import load as load_bool
from backend_adapter.aig import statistics
from scripts.check_lean_crypto import evaluate_lanes
from handshake_backend.field_dag import load as load_field,evaluate_clear,MODULUS

class PublicConversions:
 def zero_bytes(self,n):return bytes(n)
 def decode_u(self,raw):return (int.from_bytes(raw,'little')%(2**255))%MODULUS
 def encode_field(self,n):return n.to_bytes(32,'little')
 def bits_to_field(self,raw,count):return [(raw[i//8]>>(i%8))&1 for i in range(count)]
class PrefixStages:
 def __init__(self):self.cache={};self.paths={};self.calls=0
 def run(self,mode,raw,features):
  key=(mode,len(raw),features)
  if key not in self.cache:
   path=ART/f'signal-prekey-{mode}-{len(raw)}-{features}.json'
   if not path.exists():path=artifact(*key)
   self.paths[key]=path;self.cache[key]=load_bool(path)
  self.calls+=1;return evaluate_lanes(self.cache[key],[raw])[0]
class XStages:
 def __init__(self):self.booleans={};self.fields={};self.paths=set();self.calls=0
 def field(self,mode,index,inputs):
  key=(mode,index);path=XWORK/'Artifacts'/f'signal-xeddsa-field-{mode}-{index}.json'
  if key not in self.fields:self.fields[key]=load_field(path)
  self.paths.add(path);self.calls+=1;return evaluate_clear(self.fields[key],inputs)
 def boolean(self,mode,size,raw):
  args=['boolean',mode,size];stem=f'signal-xeddsa-boolean-{mode}-{size}'
  return self.run_bool(stem,args,raw)
 def decode(self,raw):return self.run_bool(f'signal-xeddsa-decode-{len(raw)}',['decode',len(raw)],raw)
 def run_bool(self,stem,args,raw):
  path=XWORK/'Artifacts'/(stem+'.json')
  if not path.exists():
   path=ART/(stem+'.json')
   if not path.exists():
    with path.open('w') as f:subprocess.run([str(XWORK/'.lake/build/bin/emit_xeddsa'),*map(str,args)],stdout=f,check=True,timeout=600)
  if stem not in self.booleans:
   if '-hash-' in stem:
    for key in list(self.booleans):
     if '-hash-' in key:del self.booleans[key]
   self.booleans[stem]=load_bool(path)
  self.paths.add(path);self.calls+=1;return evaluate_lanes(self.booleans[stem],[raw])[0]

def main():
 frozen=frozen_check();data=json.loads((WORK/'fixtures.json').read_text())['prefix']
 labels={'valid-tag7','valid-tag8','valid-tag10','trust0-ecTrue-pqFalse','trust0-ecFalse-pqTrue','trust1-ecTrue-pqTrue','trust2-ecTrue-pqTrue',
  'ec-trailing','identity-trailing','untagged-ec-signature','untagged-pq-signature','zero-ids','empty-ec-signature','short-pq-signature',
  'changed-pq-tag','absent-identity-garbage','absent-optional-garbage','absent-6'}
 selected=[x for x in data if x['input']['label'] in labels]
 prefix=PrefixStages();xs=XStages();conversion=PublicConversions();rows=[]
 for row in selected:
  v=row['input'];b=lambda k:bytes.fromhex(v[k]);meta=metadata(v)
  result=validate(prefix,xs,conversion,bytes(v['flags']),meta,b('identity'),b('ec'),b('pq'),bytes.fromhex(v.get('optional_key',v['ec'])),
    b('ec_sig'),b('pq_sig'),bytes([v['trust']]),'all')
  assert result['prefix_result']==expected_result(row['actual']),v['label']
  if v['flags'][7]:assert result['canonical_identity'].hex()==v['identity'][:66]
  if v['flags'][5]:assert result['canonical_signed_key'].hex()==v['ec'][:66]
  if v['flags'][9]:assert result['canonical_pq_key'].hex()==v['pq']
  rows.append({'label':v['label'],'prefix_code':result['prefix_result'][1],'result':result['prefix_result'].hex(),'actual_trace':row['actual']['trace']})
  print(v['label'],result['prefix_result'][:3].hex(),flush=True)
 # Local typed-input boundary: a present malformed EC key rejects with code32,
 # independent decoder result preserved. This is intentionally NOT a Rust prefix error.
 base=next(x['input'] for x in data if x['input']['label']=='valid-tag8')
 result=validate(prefix,xs,conversion,bytes(base['flags']),metadata(base),bytes.fromhex(base['identity']),b'\x04'+bytes(32),bytes.fromhex(base['pq']),
  bytes.fromhex(base['ec']),bytes.fromhex(base['ec_sig']),bytes.fromhex(base['pq_sig']),b'\x00','all')
 assert result['prefix_result']==b'\x00\x20'+bytes(18)
 assert result['wire_results'][1]==b'\x00\x02'
 profiles=[]
 for key,path in sorted(prefix.paths.items()):profiles.append({'profile':path.stem,'sha256':sha(path),'statistics':statistics(prefix.cache[key])})
 sources={Path(__file__),WORK/'adapter.py',WORK/'report.json',WORK/'fixtures.json',WORK/'Export.lean',XWORK/'completion.json',XWORK/'adapter.py',ROOT/'handshake_backend/field_dag.py',ROOT/'backend_adapter/boolean.py',ROOT/'scripts/check_lean_crypto.py'}
 report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in sorted(sources)},
  'profiles':profiles,'xeddsa_artifact_sha256':{str(p.relative_to(ROOT)):sha(p) for p in sorted(xs.paths)},'cases':rows,'actual_prefix_composition_cases':len(rows),
  'additional_typed_boundary_cases':1,'prekey_numeric_stage_calls':prefix.calls,'xeddsa_numeric_stage_calls':xs.calls,
  'signature_validity_is_computed':True,'independent_trust_result_boundary':True,'trust_policy_implemented':False,
  'frozen_xeddsa_completion_sha256':frozen,'native_mpc_executed':False,'actual_aeneas_refinement':False,'pqxdh_production_wired':False,
  'scope':'Both signatures execute through frozen shared verifier. Canonical typed bytes from same supplied keys form both signature messages. Constructor/identity Sending trust/signature error precedence matches actual protocol prefix. External trust decision and private conversions remain explicit boundaries; no callbacks or stores invoked by adapter.',
  'security_required':{'parties':5,'malicious':2,'statistical_security':128,'abort_allowed':True,'runtime_validated':False}}
 assert frozen_check()==frozen
 (WORK/'composition-report.json').write_text(json.dumps(report,indent=2)+'\n')
 print('all two-signature bundle compositions passed',flush=True)
if __name__=='__main__':main()
