#!/usr/bin/env python3
"""Small isolated reachability/negative-regression checks, no export/native run."""
from pathlib import Path
import os,json,hashlib,subprocess
H=Path(__file__).resolve().parent;CHAT=H.parent;ROOT=H.parents[2];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
parent=H/'proof-audit.json';old=json.loads(parent.read_text())
for name,digest in old['source_sha256'].items():assert sha(ROOT/name)==digest,name
for name,digest in old['core_source_sha256'].items():assert sha(ROOT/name)==digest,name
for name,digest in old['core_object_sha256'].items():assert sha(Path(name))==digest,name
out=H/'Build/narrow-v1-final'
for name,digest in old['objects_sha256'].items():
 p=Path(name);assert sha(p)==digest,name;module=name.rsplit('/ChatResponseReferenceWork/',1)[1];target=out/'ChatResponseReferenceWork'/module
 if not target.exists():target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(p.resolve())
modules=['StackMath','CanonicalMasks','ControlMasks','KeyRange','StepStackSafe','RejectedHighTag'];files=[H/(m+'.lean')for m in modules]+[H/n for n in ['check_narrow.py','NARROW.md']];before={str(p.relative_to(ROOT)):sha(p)for p in files}
token=hashlib.sha256(json.dumps(before,sort_keys=True).encode()).hexdigest()[:12];logPath=H/f'narrow-{token}-{os.getpid()}.log';env=os.environ.copy();env['CHAT_RESPONSE_OUTPUT_ROOT']=str(out)
with logPath.open('x')as log:
 subprocess.run(['python3',str(CHAT/'check.py'),*['ParserCircuitCandidateV1.'+m for m in modules]],env=env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=90)
log=logPath.read_text();assert 'sorryAx'not in log and '_native.'not in log
for name in ['narrow_of_bound','narrow_select','narrow_write_stack','write_stack_zero','canonical_zeroMask','canonical_terminal','step_control_masks','initial_control_masks','key_range_reject','nonrejected_key_tag_narrow','step_safe_stack','initial_narrow_stack','malformed_key_high_tag']:assert name in log,name
assert before=={str(p.relative_to(ROOT)):sha(p)for p in files}
for name,digest in old['core_source_sha256'].items():assert sha(ROOT/name)==digest,name
for name,digest in old['core_object_sha256'].items():assert sha(Path(name))==digest,name
receipt={'candidate_only':True,'aggregate_exit_code':0,'scope':'Step-level control-mask reachability and conditional narrow-stack invariant: high tags allowed in rejected scratch, actual invalid-key-range rejection and malformed2^63+3 key negative regression. Process/codec/full streaming/private length/error-carry equivalence remains OPEN; no runtime/profile/native jobs.','source_sha256':before,'inherited_receipt_sha256':{str(parent.relative_to(ROOT)):sha(parent)},'kernel_log_path':str(logPath),'kernel_log_sha256':sha(logPath),'kernel_log':log,'objects_sha256':{str(out/'ChatResponseReferenceWork/ParserCircuitCandidateV1'/(m+'.olean')):sha(out/'ChatResponseReferenceWork/ParserCircuitCandidateV1'/(m+'.olean'))for m in modules}}
(H/'narrow-audit.json').write_text(json.dumps(receipt,indent=2)+'\n');print('Six stack reachability modules PASS aggregate0; '+logPath.name)
