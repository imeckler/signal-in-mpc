#!/usr/bin/env python3
"""Freeze prekey work after source/artifact and frozen-dependency checks."""
import hashlib,json,re
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).resolve().parent

def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def main():
 reports=[]
 for name in ['report.json','composition-report.json']:
  r=json.loads((WORK/name).read_text());reports.append(r)
  for path,digest in r['source_sha256'].items():assert sha(ROOT/path)==digest,(name,path)
  for row in r['profiles']:assert sha(WORK/'Artifacts'/(row['profile']+'.json'))==row['sha256'],row['profile']
  for path,digest in r.get('xeddsa_artifact_sha256',{}).items():assert sha(ROOT/path)==digest,path
 r=reports[0]
 for name,digest in r['oracle_binary_sha256'].items():assert sha(WORK/'Bin'/('oracle-'+name))==digest,name
 assert sha(WORK/'.lake/build/bin/emit_prekey')==r['export_binary_sha256']
 frozen=ROOT/'SignalReference/XEdDsaWork/completion.json';assert sha(frozen)==r['frozen_xeddsa_completion_sha256']==reports[1]['frozen_xeddsa_completion_sha256']
 for path,digest in json.loads(frozen.read_text())['files'].items():assert sha(ROOT/path)==digest,path
 provenance=json.loads((WORK/'source-provenance.json').read_text())
 for path,digest in provenance['actual_source_sha256'].items():assert sha(ROOT/'.deps/libsignal-v0.106.1'/path)==digest,path
 assert sha(WORK/'Oracle/src/main.rs')==provenance['oracle_source_sha256']
 assert sha(WORK/'Oracle/Cargo.lock')==provenance['oracle_lock_sha256']
 endpoints=re.findall(r'^#print axioms (\S+)',(WORK/'Checks.lean').read_text(),re.M)
 assert len(endpoints)==len(set(endpoints))==r['proof_endpoints']==28
 paths=set((ROOT/'TlsMpc/Signal').glob('PreKey*.lean'))
 for p in WORK.rglob('*'):
  if not p.is_file() or any(x in p.parts for x in ['.lake','Build','Bin','Artifacts','__pycache__']):continue
  if p.name=='completion.json':continue
  paths.add(p)
 result={'frozen_at_utc':datetime.now(timezone.utc).isoformat(),'files':{str(p.relative_to(ROOT)):sha(p) for p in sorted(paths)},
  'all_recorded_source_artifact_and_binary_hashes_match':True,'frozen_xeddsa_unchanged':True,'frozen_xeddsa_completion_sha256':sha(frozen),
  'kernel_endpoints':endpoints,'distinct_kernel_endpoints':len(endpoints),'source_dependency_packages':provenance['oracle_dependency_count_matching_actual_lock'],
  'numeric_lanes':r['lanes'],'actual_protocol_prefix_cases':r['actual_process_validation_prefix_cases'],
  'full_two_signature_compositions':reports[1]['actual_prefix_composition_cases'],'additional_typed_boundary_cases':reports[1]['additional_typed_boundary_cases'],
  'actual_aeneas_refinement':False,'native_mpc_executed':False,'production_pqxdh_wired':False,'trust_policy_implemented':False,
  'scope':'Typed key/device leaves, exact pure constructor semantics and ordered validation-prefix result; both signatures computed through frozen shared verifier. Trust-store decision binding and private conversion remain external. Actual native function stops at post-validation store sentinel; no full session creation claim.',
  'next_independent_candidate':'Actual Aeneas extraction of pure PreKeyBundleContent::try_from/PreKeyBundle::new and Option::zip/error order, before async process/store/cryptographic call-graph refinement. Not attempted here.'}
 (WORK/'completion.json').write_text(json.dumps(result,indent=2)+'\n')
 print(f'Frozen {len(paths)} files, {len(endpoints)} kernel endpoints, 18 full compositions; frozen XEdDSA unchanged.')
if __name__=='__main__':main()
