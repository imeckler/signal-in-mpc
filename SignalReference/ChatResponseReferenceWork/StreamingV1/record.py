#!/usr/bin/env python3
"""Record completed focused validations without rerunning unchanged cases."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parent;ROOT=H.parents[2];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
checks=[('VarintReference','scalar.log',58478),('ScalarProjection','scalar.log',47362),('VarintPrefix','prefix.log',43128)]
logs={'ScalarProjection':H/'scalar.log','VarintPrefix':H/'prefix.log'}
out=H.parent/'OuterEnvelopeV1/Build/final/ChatResponseReferenceWork/StreamingV1'
entries=[]
for module,_,session in checks:
 log=logs[module].read_text() if module in logs else None
 if log is not None:assert 'sorryAx' not in log and '_native.' not in log
 source=H/(module+'.lean');obj=out/(module+'.olean');assert obj.stat().st_mtime>=source.stat().st_mtime,module
 entry={'module':module,'terminal_tool_session':session,'module_exit_code':0,'tool_session_exit_code':1 if module=='VarintReference' else 0,'source_sha256':sha(source),'object_path':str(obj),'object_sha256':sha(obj)}
 if log is not None:entry['kernel_log']=log
 else:
  entry['stdout_provenance']='Final six-declaration module stdout observed in session58478; that checker proceeded to ScalarProjection, which then failed and was fixed/tested separately. The reused scalar.log was overwritten by later ScalarProjection-only checks; no raw final VarintReference log is claimed.'
  entry['observed_axioms']='All six printed declarations had foundational-only dependencies [propext, Classical.choice, Quot.sound] (some subsets).'
 entries.append(entry)
files=[H/(m+'.lean') for m,_,_ in checks]+[H/n for n in ['check.py','record.py','README.md']]
cores=['TlsMpc/TlsChatResponse','TlsMpc/TlsWebSocketUpgrade','TlsMpc/TlsWebSocketFrame','TlsMpc/TlsInner','TlsMpc/ByteAuth','TlsMpc/Signal/Word64','TlsMpc/Signal/VarintDecode/Spqr','TlsMpc/Signal/VarintDecode/Spec']
(H/'audit.json').write_text(json.dumps({'candidate_only':True,'scope':'Three-module actual numeric Core varint/prefix and native enum/u32 scalar projection milestone, not full streaming/source refinement.','recorded_after_completed_focused_checks':True,'source_unchanged_since_focused_checks':True,'validation':entries,'source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in files},'inherited_receipts_sha256':{'SignalReference/ChatResponseReferenceWork/OuterEnvelopeV1/audit.json':sha(H.parent/'OuterEnvelopeV1/audit.json')},'core_source_sha256':{n+'.lean':sha(ROOT/(n+'.lean')) for n in cores},'core_object_sha256':{str(ROOT/'.lake/build/lib/lean'/(n+'.olean')):sha(ROOT/'.lake/build/lib/lean'/(n+'.olean')) for n in cores},'objects_sha256':{str(out/(m+'.olean')):sha(out/(m+'.olean')) for m,_,_ in checks},'remaining':['Full prefix/span/absolute-cursor to actual owned schema relation.','HTTP header/Unicode trim source validation and correlation/compiler composition.','Inherited static-reference diagnostic push and optimized unsafe std UTF8/content/allocation model boundaries.']},indent=2)+'\n')
print('Recorded completed focused three-module milestone; no unchanged-case rerun')
