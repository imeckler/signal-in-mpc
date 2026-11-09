#!/usr/bin/env python3
"""Small isolated reachability/negative-regression checks, no export/native run."""
from pathlib import Path
import os,json,hashlib,subprocess
H=Path(__file__).resolve().parent;CHAT=H.parent;ROOT=H.parents[2];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
parent=H/'narrow-audit.json';old=json.loads(parent.read_text());basePath=H/'proof-audit.json';base=json.loads(basePath.read_text())
assert old['inherited_receipt_sha256'][str(basePath.relative_to(ROOT))]==sha(basePath)
for receipt in [base,old]:
 for name,digest in receipt['source_sha256'].items():assert sha(ROOT/name)==digest,name
for name,digest in base['core_source_sha256'].items():assert sha(ROOT/name)==digest,name
for name,digest in base['core_object_sha256'].items():assert sha(Path(name))==digest,name
out=H/'Build/process-v1-final'
for receipt in [base,old]:
 for name,digest in receipt['objects_sha256'].items():
  p=Path(name);assert sha(p)==digest,name;module=name.rsplit('/ChatResponseReferenceWork/',1)[1];target=out/'ChatResponseReferenceWork'/module
  if not target.exists():target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(p.resolve())
modules=['ProcessMasks','SelectStackSafe','ProcessStackSafe','MuxStackSafe'];files=[H/(m+'.lean')for m in modules]+[H/n for n in ['check_process.py','PROCESS.md']];before={str(p.relative_to(ROOT)):sha(p)for p in files}
token=hashlib.sha256(json.dumps(before,sort_keys=True).encode()).hexdigest()[:12];logPath=H/f'process-{token}-{os.getpid()}.log';env=os.environ.copy();env['CHAT_RESPONSE_OUTPUT_ROOT']=str(out)
with logPath.open('x')as log:
 subprocess.run(['python3',str(CHAT/'check.py'),*['ParserCircuitCandidateV1.'+m for m in modules]],env=env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=90)
log=logPath.read_text();assert 'sorryAx'not in log and '_native.'not in log
for name in ['process_control_masks','select_safe_stack','guard_safe_stack','process_safe_stack','process_reachable_stack','coreRun_reachable','fresh_coreRun_reachable','mux_process_reachable','mux_admit_reachable','muxRun_reachable','fresh_muxRun_reachable']:assert name in log,name
assert before=={str(p.relative_to(ROOT)):sha(p)for p in files}
for name,digest in base['core_source_sha256'].items():assert sha(ROOT/name)==digest,name
for name,digest in base['core_object_sha256'].items():assert sha(Path(name))==digest,name
receipt={'candidate_only':True,'aggregate_exit_code':0,'scope':'Actual Core process and Mux process/admit sequences preserve reachable canonical controls and valid0-or-narrow stack for all private inputs, including malformed high-tag keys and resets. Codec roundtrip/rejected-state bisimulation/full compact streaming equivalence remains OPEN; no runtime/profile/native jobs.','source_sha256':before,'inherited_receipt_sha256':{str(parent.relative_to(ROOT)):sha(parent)},'kernel_log_path':str(logPath),'kernel_log_sha256':sha(logPath),'kernel_log':log,'objects_sha256':{str(out/'ChatResponseReferenceWork/ParserCircuitCandidateV1'/(m+'.olean')):sha(out/'ChatResponseReferenceWork/ParserCircuitCandidateV1'/(m+'.olean'))for m in modules}}
(H/'process-audit.json').write_text(json.dumps(receipt,indent=2)+'\n');print('Four Core/Mux reachability modules PASS aggregate0; '+logPath.name)
