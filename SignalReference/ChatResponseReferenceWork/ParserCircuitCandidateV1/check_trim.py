#!/usr/bin/env python3
"""Small isolated reachability/negative-regression checks, no export/native run."""
from pathlib import Path
import os,json,hashlib,subprocess
H=Path(__file__).resolve().parent;CHAT=H.parent;ROOT=H.parents[2];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
parent=H/'process-audit.json';old=json.loads(parent.read_text());basePath=H/'proof-audit.json';base=json.loads(basePath.read_text())
narrowPath=H/'narrow-audit.json';narrow=json.loads(narrowPath.read_text())
assert old['inherited_receipt_sha256'][str(narrowPath.relative_to(ROOT))]==sha(narrowPath)
assert narrow['inherited_receipt_sha256'][str(basePath.relative_to(ROOT))]==sha(basePath)
for receipt in [base,narrow,old]:
 for name,digest in receipt['source_sha256'].items():assert sha(ROOT/name)==digest,name
for name,digest in base['core_source_sha256'].items():assert sha(ROOT/name)==digest,name
for name,digest in base['core_object_sha256'].items():assert sha(Path(name))==digest,name
out=H/'Build/trim-v1-final'
for receipt in [base,narrow,old]:
 for name,digest in receipt['objects_sha256'].items():
  p=Path(name);assert sha(p)==digest,name;module=name.rsplit('/ChatResponseReferenceWork/',1)[1];target=out/'ChatResponseReferenceWork'/module
  if not target.exists():target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(p.resolve())
modules=['TrimStack','TrimProcess'];files=[H/(m+'.lean')for m in modules]+[H/n for n in ['check_trim.py','TRIM.md']];before={str(p.relative_to(ROOT)):sha(p)for p in files}
token=hashlib.sha256(json.dumps(before,sort_keys=True).encode()).hexdigest()[:12];logPath=H/f'trim-{token}-{os.getpid()}.log';env=os.environ.copy();env['CHAT_RESPONSE_OUTPUT_ROOT']=str(out)
with logPath.open('x')as log:
 subprocess.run(['python3',str(CHAT/'check.py'),*['ParserCircuitCandidateV1.'+m for m in modules]],env=env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=90)
log=logPath.read_text();assert 'sorryAx'not in log and '_native.'not in log
for name in ['trim_lookup','trim_word_identity','trim_state_select','trim_rejected_step','trim_step','trim_process_tail','trim_process','trimmed_trace_eq','fresh_trimmed_trace_eq']:assert name in log,name
assert before=={str(p.relative_to(ROOT)):sha(p)for p in files}
for name,digest in base['core_source_sha256'].items():assert sha(ROOT/name)==digest,name
for name,digest in base['core_object_sha256'].items():assert sha(Path(name))==digest,name
receipt={'candidate_only':True,'aggregate_exit_code':0,'scope':'Actual Core process/event trace agrees under stack-high-half erasure for all private byte/control sequences from initial state, including sticky rejected high tags. Mux trace and byte codec bridge remain OPEN. No runtime promotion or native jobs.','source_sha256':before,'inherited_receipt_sha256':{str(parent.relative_to(ROOT)):sha(parent)},'kernel_log_path':str(logPath),'kernel_log_sha256':sha(logPath),'kernel_log':log,'objects_sha256':{str(out/'ChatResponseReferenceWork/ParserCircuitCandidateV1'/(m+'.olean')):sha(out/'ChatResponseReferenceWork/ParserCircuitCandidateV1'/(m+'.olean'))for m in modules}}
(H/'trim-audit.json').write_text(json.dumps(receipt,indent=2)+'\n');print('Two Core trim/trace modules PASS aggregate0; '+logPath.name)
