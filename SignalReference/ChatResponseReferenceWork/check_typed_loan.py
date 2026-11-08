#!/usr/bin/env python3
"""Scoped typed ABI bridge audit over the grounded actual forwarding receipt."""
from pathlib import Path
import hashlib,json,os,subprocess
H=Path(__file__).resolve().parent;ROOT=H.parents[1];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipt=H/'PartialMonoCandidate/forward-audit.json';inherited=json.loads(receipt.read_text())
for name,digest in inherited['source_sha256'].items():assert sha(ROOT/name)==digest,name
output=H/'PartialMonoCandidate/Build/typed-loan-final';env=os.environ.copy();env['CHAT_RESPONSE_OUTPUT_ROOT']=str(output)
modules=['PartialMonoCandidate.GeneratedForwardActual.Types','PartialMonoCandidate.GeneratedForwardActual.Funs','PartialMonoCandidate.ActualForwardReference','TypedLoanProjection']
with (H/'typed-loan-audit.log').open('w') as f:subprocess.run(['python3',str(H/'check.py'),*modules],env=env,stdout=f,stderr=subprocess.STDOUT,check=True,timeout=120)
log=(H/'typed-loan-audit.log').read_text();assert 'sorryAx' not in log
for theorem in ['field_view','failure_exact','actual_field_exact']:assert theorem+"' does not depend on any axioms" in log
for name,digest in inherited['source_sha256'].items():assert sha(ROOT/name)==digest,name
(H/'typed-loan-audit.json').write_text(json.dumps({'scope':'Explicit tagged raw/trait ABI projection, executing auxiliary backward map; actual native forwarding instantiation. No general function coercion and no new primitive correctness premise.','source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in [H/'TypedLoanProjection.lean',H/'check_typed_loan.py']},'grounded_forward_receipt_sha256':sha(receipt),'inherited_source_count':len(inherited['source_sha256']),'object_sha256':{str(output/('ChatResponseReferenceWork/'+m.replace('.','/')+'.olean')):sha(output/('ChatResponseReferenceWork/'+m.replace('.','/')+'.olean')) for m in modules},'kernel_log':log,'full_string_or_response_refinement':False},indent=2)+'\n');print('typed loan projection: four modules PASS, no axioms')
