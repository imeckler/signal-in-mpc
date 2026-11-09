#!/usr/bin/env python3
"""Focused immutable proof receipt for unpromoted one-step stack32 candidate."""
from pathlib import Path
import os,json,hashlib,subprocess
H=Path(__file__).resolve().parent;CHAT=H.parent;ROOT=H.parents[2];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
profile=H/'profile-audit.json';data=json.loads(profile.read_text())
for name,digest in data['source_sha256'].items():assert sha(ROOT/name)==digest,name
for row in data['cases']:assert sha(Path(row['artifact_path']))==row['artifact_sha256'],row['mode']
files=[H/n for n in ['Stack32Codec.lean','CompiledCodec.lean','Emit.lean','profile.py','profile-audit.json','check.py','CHECKPOINT.md']]
before={str(p.relative_to(ROOT)):sha(p)for p in files}
core=['TlsMpc/TlsChatResponse.lean','TlsMpc/TlsChatResponseMux.lean','TlsMpc/Signal/Word64.lean','TlsMpc/ByteAuth.lean','TlsMpc/TlsWebSocketFrame.lean']
coreSources={name:sha(ROOT/name)for name in core};coreObjects={str(ROOT/'.lake/build/lib/lean'/Path(name).with_suffix('.olean')):sha(ROOT/'.lake/build/lib/lean'/Path(name).with_suffix('.olean'))for name in core}
out=H/'Build/proof-v1-final';env=os.environ.copy();env['CHAT_RESPONSE_OUTPUT_ROOT']=str(out)
token=hashlib.sha256(json.dumps(before,sort_keys=True).encode()).hexdigest()[:12];logPath=H/f'proof-{token}-{os.getpid()}.log'
with logPath.open('x')as log:
 subprocess.run(['python3',str(CHAT/'check.py'),'ParserCircuitCandidateV1.Stack32Codec','ParserCircuitCandidateV1.CompiledCodec'],env=env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=60)
log=logPath.read_text();assert 'sorryAx'not in log and '_native.'not in log
for name in ['one_step_projection','output_length','expand_length','compact_map','expand_map','runByte_map','compiled_correct']:assert name in log,name
assert before=={str(p.relative_to(ROOT)):sha(p)for p in files}
for name,digest in coreSources.items():assert sha(ROOT/name)==digest,name
for name,digest in coreObjects.items():assert sha(Path(name))==digest,name
receipt={'candidate_only':True,'aggregate_exit_code':0,'scope':'One-step compact-input/stack-output projected equality and all-assignment exported compiler correctness only. Fresh/full streaming/private length/fragmented assembly/reachable stack32/error-carry equivalence remains OPEN; runtime untouched.','source_sha256':before,'core_source_sha256':coreSources,'core_object_sha256':coreObjects,'kernel_log_path':str(logPath),'kernel_log_sha256':sha(logPath),'kernel_log':log,'objects_sha256':{str(out/'ChatResponseReferenceWork/ParserCircuitCandidateV1'/(m+'.olean')):sha(out/'ChatResponseReferenceWork/ParserCircuitCandidateV1'/(m+'.olean'))for m in ['Stack32Codec','CompiledCodec']}}
(H/'proof-audit.json').write_text(json.dumps(receipt,indent=2)+'\n');print('Stack32 one-step/compiler kernel PASS aggregate0; '+logPath.name)
