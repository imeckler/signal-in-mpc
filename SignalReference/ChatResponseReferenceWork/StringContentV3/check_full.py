#!/usr/bin/env python3
"""Full contiguous String primitive composition under explicit content models."""
from pathlib import Path
import os,subprocess,json,hashlib
H=Path(__file__).resolve().parent;ROOT=H.parents[2];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inherited=json.loads((H/'audit.json').read_text())
for name,digest in inherited['source_sha256'].items():assert sha(ROOT/name)==digest,name
modules=[name.rsplit('ChatResponseReferenceWork/',1)[1].removesuffix('.olean').replace('/','.') for name in inherited['objects_sha256']]
modules+=['StringContentV3.BytesReference','StringContentV3.FullStringReference']
output=H/'Build/string-full-final';env=os.environ.copy();env['CHAT_RESPONSE_OUTPUT_ROOT']=str(output)
files=[H/p for p in ['BytesReference.lean','FullStringReference.lean','check_full.py','FULL_STRING.md']];before={str(p.relative_to(ROOT)):sha(p) for p in files}
with (H/'full-audit.log').open('w') as f:subprocess.run(['python3',str(H.parent/'check.py'),*modules],env=env,stdout=f,stderr=subprocess.STDOUT,check=True,timeout=300)
log=(H/'full-audit.log').read_text();assert 'sorryAx' not in log
for name in ['payload_length','bytes_full_reference','string_wire_error','string_full_reference','string_owned_cleanup']:assert name+"' depends on axioms:" in log
for name,digest in {**inherited['source_sha256'],**before}.items():assert sha(ROOT/name)==digest,name
(H/'full-audit.json').write_text(json.dumps({'candidate_only':True,'scope':'All-outcomes contiguous actual generated Prost Vec-backed String primitive with executable UTF8/content models. Wrong wire, malformed varint/overflow, length underflow, exact successful replacement, InvalidString, exact suffix and owned-error clear observation. No primitive correctness/termination premise. Not actual Bytes response schema or streaming theorem.','source_sha256':before,'inherited_string_receipt_sha256':sha(H/'audit.json'),'kernel_log':log,'objects_sha256':{str(output/('ChatResponseReferenceWork/'+m.replace('.','/')+'.olean')):sha(output/('ChatResponseReferenceWork/'+m.replace('.','/')+'.olean')) for m in modules},'boundaries':inherited['model_boundaries'],'remaining':['Bridge executable UTF8 grammar to optimized unsafe std implementation (explicit trust obligation).','Actual Bytes/default/submessage/repeated-header response dispatcher, validation and streaming/correlation/compiler composition.']},indent=2)+'\n');print('18-module all-outcomes String/owned-error composition PASS; schema remains open')
