#!/usr/bin/env python3
"""Focused kernel receipt; explicit content/ABI model, not full String refinement."""
from pathlib import Path
import os,subprocess,json,hashlib
H=Path(__file__).resolve().parent;CHAT=H.parents[1];ROOT=H.parents[3]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
output=H/'Build/generated-final';env=os.environ.copy();env['CHAT_RESPONSE_OUTPUT_ROOT']=str(output)
modules=['PartialMonoCandidate.GeneratedForwardActual.Types','PartialMonoCandidate.GeneratedForwardActual.Funs','PartialMonoCandidate.ActualForwardReference','TypedLoanProjection','StringContentV3.ContiguousPut.GeneratedOneStep.Types','StringContentV3.ContiguousPut.GeneratedOneStep.FunsExternal','StringContentV3.ContiguousPut.GeneratedOneStep.Funs','StringContentV3.ContiguousPut.LoopLowering','StringContentV3.ContiguousPut.CanonicalTake','StringContentV3.ContiguousPut.GeneratedReference']
with (H/'generated-audit.log').open('w') as f:
 subprocess.run(['python3',str(CHAT/'check.py'),*modules],env=env,stdout=f,stderr=subprocess.STDOUT,check=True,timeout=240)
log=(H/'generated-audit.log').read_text();assert 'sorryAx' not in log
assert "GeneratedReference.put_reference' depends on axioms:" in log
files=[H/p for p in ['GeneratedReference.lean','GeneratedOneStep/Types.lean','GeneratedOneStep/Funs.lean','GeneratedOneStep/FunsExternal.lean','GeneratedOneStep/FunsExternal_Template.lean','extract.py','extraction.json','check_generated.py','translate.py','translation.json','CanonicalTake.lean','LoopLowering.lean','replay.py','replay.json','Rust/src/lib.rs']]
inherited=[CHAT/'TypedLoanProjection.lean',CHAT/'typed-loan-audit.json',H/'loop-audit.json']
report={'candidate_only':True,'scope':'Kernel all-model-outcomes generated guarded copier: exact append and suffix, including modeled capacity failure, for canonical contiguous slices and every Usize limit. Actual loop lowering is separately proved. Not full String/response refinement.','source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in files},'inherited_sha256':{str(p.relative_to(ROOT)):sha(p) for p in inherited},'kernel_log':log,'objects_sha256':{str(output/('ChatResponseReferenceWork/'+m.replace('.','/')+'.olean')):sha(output/('ChatResponseReferenceWork/'+m.replace('.','/')+'.olean')) for m in modules},'boundaries':['Successful bounded Vec allocation/content model; modeled oversized reservation returns panic. No allocator/pointer proof.','Executable Take content/raw loan restoration models; actual mutable inner forwarding is grounded by TypedLoanProjection, but arbitrary Buf/unsafe memory is not claimed.','String UTF8/owned-error and response schema/streaming composition remain open.']}
(H/'generated-audit.json').write_text(json.dumps(report,indent=2)+'\n');print('generated copier exact contents/suffix/all-model-outcomes kernel PASS')
