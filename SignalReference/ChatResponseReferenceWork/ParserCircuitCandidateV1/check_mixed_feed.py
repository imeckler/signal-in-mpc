#!/usr/bin/env python3
"""Kernel-only codec indices/word lemmas; no circuit export or native job."""
from pathlib import Path
import os,json,hashlib,subprocess
H=Path(__file__).resolve().parent;ROOT=H.parents[2];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
parent=H/'compact-feed-audit.json';receipts=[];seen=set()
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
out=H/'Build/mixed-feed-v1-final'
for r in receipts:
 for name,digest in r['objects_sha256'].items():
  p=Path(name);assert sha(p)==digest,name
  target=out/'ChatResponseReferenceWork'/name.rsplit('/ChatResponseReferenceWork/',1)[1]
  if not target.exists():target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(p.resolve())
modules=['AdmissionCodec','AdmissionStep','CompiledAdmission','AdmissionCarry','MixedFeed','CompiledMixedFeed'];files=[H/(m+'.lean')for m in modules]+[H/n for n in ['check_mixed_feed.py','MIXED_FEED.md']]
before={str(p.relative_to(ROOT)):sha(p)for p in files};token=hashlib.sha256(json.dumps(before,sort_keys=True).encode()).hexdigest()[:12]
logPath=H/f'mixed-feed-{token}-{os.getpid()}.log';env=os.environ.copy();env['CHAT_RESPONSE_OUTPUT_ROOT']=str(out)
with logPath.open('x')as log:
 subprocess.run(['python3',str(H.parent/'check.py'),*['ParserCircuitCandidateV1.'+m for m in modules]],env=env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=90)
log=logPath.read_text();assert 'sorryAx'not in log and '_native.'not in log
for name in ['expanded_admit_test','expand_encoded_admit','encoded_admit_step','compiled_admit_correct','compiled_encoded_admit','encode_admit_feedback','mixed_trace_eq','fresh_mixed_trace_eq','compiled_mixed_step','compiled_mixed_after_prefix']:assert name in log,name
assert before=={str(p.relative_to(ROOT)):sha(p)for p in files}
r={'candidate_only':True,'aggregate_exit_code':0,'scope':'New compact admission endpoint592B→582B exactly implements original Mux.admit; mixed compact admit/feed feedback traces and every exported AIG bit after arbitrary mixed operation prefixes agree with original Mux, all private payload/control values including rejection. Public endpoint schedule. No runtime promotion/native benchmark or complete actual Rust-response claim. Admission gate/depth measurement pending separately.','source_sha256':before,'inherited_receipt_sha256':{str(parent.relative_to(ROOT)):sha(parent)},'kernel_log_path':str(logPath),'kernel_log_sha256':sha(logPath),'kernel_log':log,'objects_sha256':{str(out/'ChatResponseReferenceWork/ParserCircuitCandidateV1'/(m+'.olean')):sha(out/'ChatResponseReferenceWork/ParserCircuitCandidateV1'/(m+'.olean'))for m in modules}}
(H/'mixed-feed-audit.json').write_text(json.dumps(r,indent=2)+'\n');print('Six compact admission/mixed/compiler modules PASS aggregate0; '+logPath.name)
