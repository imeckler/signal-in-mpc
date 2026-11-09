#!/usr/bin/env python3
"""Kernel-only codec indices/word lemmas; no circuit export or native job."""
from pathlib import Path
import os,json,hashlib,subprocess
H=Path(__file__).resolve().parent;ROOT=H.parents[2];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
parent=H/'codec-audit.json';receipts=[];seen=set()
def visit(path):
 if path in seen:return
 seen.add(path);r=json.loads(path.read_text())
 for name,digest in r.get('inherited_receipt_sha256',{}).items():
  p=ROOT/name;assert sha(p)==digest,name;visit(p)
 for name,digest in r['source_sha256'].items():assert sha(ROOT/name)==digest,name
 for key in ['core_source_sha256','core_object_sha256']:
  for name,digest in r.get(key,{}).items():assert sha(Path(name)if Path(name).is_absolute()else ROOT/name)==digest,name
 receipts.append(r)
visit(parent)
out=H/'Build/state-codec-v1-final'
for r in receipts:
 for name,digest in r['objects_sha256'].items():
  p=Path(name);assert sha(p)==digest,name
  target=out/'ChatResponseReferenceWork'/name.rsplit('/ChatResponseReferenceWork/',1)[1]
  if not target.exists():target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(p.resolve())
modules=['StateCodec'];files=[H/(m+'.lean')for m in modules]+[H/n for n in ['check_state_codec.py','STATE_CODEC.md']]
before={str(p.relative_to(ROOT)):sha(p)for p in files};token=hashlib.sha256(json.dumps(before,sort_keys=True).encode()).hexdigest()[:12]
logPath=H/f'state-codec-{token}-{os.getpid()}.log';env=os.environ.copy();env['CHAT_RESPONSE_OUTPUT_ROOT']=str(out)
with logPath.open('x')as log:
 subprocess.run(['python3',str(H.parent/'check.py'),*['ParserCircuitCandidateV1.'+m for m in modules]],env=env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=90)
log=logPath.read_text();assert 'sorryAx'not in log and '_native.'not in log
for name in ['word_chunk_prefix_suffix','decode_word_table','decoded_state_stack','state_bytes_length','read_encoded_state']:assert name in log,name
assert before=={str(p.relative_to(ROOT)):sha(p)for p in files}
r={'candidate_only':True,'aggregate_exit_code':0,'scope':'Actual Core readState(stateBytes(state)) equals state under explicit list-shape lengths; complete 100-word stack table is derived from actual slices/pack. Mux wrapper and compact projected state serialization/export recurrence OPEN.','source_sha256':before,'inherited_receipt_sha256':{str(parent.relative_to(ROOT)):sha(parent)},'kernel_log_path':str(logPath),'kernel_log_sha256':sha(logPath),'kernel_log':log,'objects_sha256':{str(out/'ChatResponseReferenceWork/ParserCircuitCandidateV1'/(m+'.olean')):sha(out/'ChatResponseReferenceWork/ParserCircuitCandidateV1'/(m+'.olean'))for m in modules}}
(H/'state-codec-audit.json').write_text(json.dumps(r,indent=2)+'\n');print('Core state codec PASS aggregate0; '+logPath.name)
