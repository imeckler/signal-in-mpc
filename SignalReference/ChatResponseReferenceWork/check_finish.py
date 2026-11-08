#!/usr/bin/env python3
"""Focused actual HTTP conversion -> Core finish flag composition audit."""
from pathlib import Path
import os,json,hashlib,subprocess,re
H=Path(__file__).resolve().parent;ROOT=H.parents[1];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inherited=json.loads((H/'component-audit.json').read_text());sources={k:v for k,v in inherited['source_sha256'].items() if '/GeneratedStatus/' in k or k.endswith('/StatusReference.lean')}
assert len(sources)>=5
for p,digest in sources.items():assert sha(ROOT/p)==digest,p
output=Path(os.environ.get('CHAT_RESPONSE_OUTPUT_ROOT',str(H/'Revisions/finish-final'))).resolve();env=os.environ.copy();env['CHAT_RESPONSE_OUTPUT_ROOT']=str(output)
mods=['GeneratedStatus.TypesExternal','GeneratedStatus.Types','GeneratedStatus.FunsExternal','GeneratedStatus.Funs','StatusReference','FinishReference','HttpStatusBridge']
with (H/'finish-audit.log').open('w') as f:subprocess.run(['python3',str(H/'check.py'),*mods],env=env,stdout=f,stderr=subprocess.STDOUT,check=True,timeout=180)
log=(H/'finish-audit.log').read_text();assert 'sorryAx' not in log
for name in ['core_status_range','core_success_range','http_error_is_valid','native_status_flags','core_native_status']:
 assert re.search(r"\."+name+r"' depends on axioms: \[propext, Classical.choice, Quot.sound\]",log),name
for p,digest in sources.items():assert sha(ROOT/p)==digest,p
files=[H/'check_finish.py',H/'FinishReference.lean',H/'HttpStatusBridge.lean',ROOT/'TlsMpc/TlsChatResponse.lean',ROOT/'TlsMpc/Signal/Word64.lean']
(H/'finish-audit.json').write_text(json.dumps({'scope':'Actual native checked status conversion equals both Core flags under explicit structurally-complete and exact-ID premises. Does not prove schema scan or Mux/source scheduling equivalence.','source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in files},'inherited_status_sources_verified':sources,'object_sha256':{str(output/('ChatResponseReferenceWork/'+m.replace('.','/')+'.olean')):sha(output/('ChatResponseReferenceWork/'+m.replace('.','/')+'.olean')) for m in mods},'lean_log':log,'non2xx_valid_response_example':400,'complete_response_refinement':False},indent=2)+'\n');print('actual HTTP/Core completion flags PASS')
