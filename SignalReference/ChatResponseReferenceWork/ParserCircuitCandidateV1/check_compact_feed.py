#!/usr/bin/env python3
"""Kernel-only codec indices/word lemmas; no circuit export or native job."""
from pathlib import Path
import os,json,hashlib,subprocess
H=Path(__file__).resolve().parent;ROOT=H.parents[2];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
parent=H/'serialized-trim-audit.json';receipts=[];seen=set()
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
out=H/'Build/compact-feed-v1-final'
for r in receipts:
 for name,digest in r['objects_sha256'].items():
  p=Path(name);assert sha(p)==digest,name
  target=out/'ChatResponseReferenceWork'/name.rsplit('/ChatResponseReferenceWork/',1)[1]
  if not target.exists():target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(p.resolve())
modules=['CompactInput','EncodedByteStep','CompiledEncodedByte','CompactCarry','CompactFeed'];files=[H/(m+'.lean')for m in modules]+[H/n for n in ['check_compact_feed.py','COMPACT_FEED.md']]
before={str(p.relative_to(ROOT)):sha(p)for p in files};token=hashlib.sha256(json.dumps(before,sort_keys=True).encode()).hexdigest()[:12]
logPath=H/f'compact-feed-{token}-{os.getpid()}.log';env=os.environ.copy();env['CHAT_RESPONSE_OUTPUT_ROOT']=str(out)
with logPath.open('x')as log:
 subprocess.run(['python3',str(H.parent/'check.py'),*['ParserCircuitCandidateV1.'+m for m in modules]],env=env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=90)
log=logPath.read_text();assert 'sorryAx'not in log and '_native.'not in log
for name in ['expanded_input_test','expand_encoded_input','encoded_byte_step','compiled_encoded_byte','encode_after_event','event_state_carry','compact_feed_trace_eq','admitted_compact_feed_trace_eq']:assert name in log,name
assert before=={str(p.relative_to(ROOT)):sha(p)for p in files}
r={'candidate_only':True,'aggregate_exit_code':0,'scope':'Measured compact byte endpoint feedback recurrence equals every585-byte compact original Mux event output for arbitrary private byte/control sequences following arbitrary actual Mux operation prefixes; exact582-byte state carry+4 new controls, malformed/rejected states included. Exported AIG bits agree per endpoint under the same encoding. No exported compact admission circuit/runtime promotion or complete actual Rust-response refinement claimed.','source_sha256':before,'inherited_receipt_sha256':{str(parent.relative_to(ROOT)):sha(parent)},'kernel_log_path':str(logPath),'kernel_log_sha256':sha(logPath),'kernel_log':log,'objects_sha256':{str(out/'ChatResponseReferenceWork/ParserCircuitCandidateV1'/(m+'.olean')):sha(out/'ChatResponseReferenceWork/ParserCircuitCandidateV1'/(m+'.olean'))for m in modules}}
(H/'compact-feed-audit.json').write_text(json.dumps(r,indent=2)+'\n');print('Five compact byte/feed/compiler modules PASS aggregate0; '+logPath.name)
