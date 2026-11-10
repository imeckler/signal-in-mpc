#!/usr/bin/env python3
"""Freeze the completed XEdDSA work only after every recorded hash matches."""
import hashlib,json,re
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[2];WORK=Path(__file__).resolve().parent

def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
 return h.hexdigest()
def main():
 reports=[];endpoints=[]
 for name,checks in [('report.json','XEdDsaChecks.lean'),('challenge-report.json','XEdDsaChallengeChecks.lean'),('binding-report.json','XEdDsaBindingChecks.lean')]:
  report=json.loads((WORK/name).read_text());reports.append(report)
  for file,digest in report['source_sha256'].items():assert sha(ROOT/file)==digest,(name,file)
  for row in report['profiles']:assert sha(WORK/'Artifacts'/(row['profile']+'.json'))==row['sha256'],(name,row['profile'])
  if 'oracle_binary_sha256' in report:assert sha(ROOT/'.deps/signal-xeddsa-oracle-target/debug/signal-xeddsa-oracle')==report['oracle_binary_sha256']
  if 'export_binary_sha256' in report:assert sha(WORK/'.lake/build/bin/emit_xeddsa')==report['export_binary_sha256']
  ns=re.findall(r'^#print axioms (\S+)',(ROOT/'SignalReference'/checks).read_text(),re.M)
  assert len(ns)==report['proof_endpoints'];endpoints+=ns
 assert len(set(endpoints))==len(endpoints)==62
 provenance=json.loads((WORK/'source-provenance.json').read_text())
 for file,digest in provenance['checked_existing_pin_files'].items():assert sha(ROOT/file)==digest,file
 paths=set((ROOT/'TlsMpc/Signal').glob('XEdDsa*.lean'))|set((ROOT/'SignalReference').glob('XEdDsa*.lean'))
 for p in WORK.rglob('*'):
  if not p.is_file() or any(x in p.parts for x in ('.lake','__pycache__','Artifacts','target')):continue
  if p.name=='completion.json':continue
  paths.add(p)
 result={'frozen_at_utc':datetime.now(timezone.utc).isoformat(),'files':{str(p.relative_to(ROOT)):sha(p) for p in sorted(paths)},
  'distinct_kernel_endpoints':len(endpoints),'endpoints':endpoints,'all_recorded_source_and_artifact_hashes_match':True,
  'scope':'Six Lean computational XEdDSA modules, per-stage compiler agreement, actual pinned native differential, shared-stage abstract adapter; no PQXDH integration/native MPC/actual Aeneas reference acceptance.',
  'native_mpc_executed':False,'actual_aeneas_refinement':False,'pqxdh_wired':False,'production_conversion_instantiated':False,
  'fixtures':{k:reports[0][k] for k in ['decode_lanes','recovery_cases','double_scalar_cases','composed_cases','noncanonical_S_plus_ell_accepted']},
  'challenge_fixtures':{k:reports[1][k] for k in ['sha512_numeric_lanes','scalar_reduction_numeric_lanes','complete_staged_numeric_cases','full_numeric_crypto_paths']},
  'adapter_fixtures':reports[2]['full_adapter_cases'],
  'no_git_or_shared_root_changes':True}
 (WORK/'completion.json').write_text(json.dumps(result,indent=2)+'\n')
 print(f'Frozen {len(paths)} files and {len(endpoints)} distinct kernel endpoints; all source/artifact hashes match.')
if __name__=='__main__':main()
