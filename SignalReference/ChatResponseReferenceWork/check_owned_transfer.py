#!/usr/bin/env python3
"""Reproduce the scoped owned-slice candidate; no assumed decoder result."""
from pathlib import Path
import hashlib,json,os,subprocess,time
H=Path(__file__).resolve().parent;ROOT=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
run=lambda args,**kw:subprocess.run(args,check=True,timeout=180,**kw)
run(['python3',str(H/'replay_owned_slice.py')])
run(['python3',str(H/'extract.py'),'owned_transferred'])
run(['python3',str(H/'translate.py'),'owned_transferred'])
rust=ROOT/'.deps/rust-nightly-2026-08-18';env=os.environ.copy();env.update(PATH=str(rust/'bin')+os.pathsep+env['PATH'],CARGO_HOME=str(ROOT/'.deps/libsignal-cargo-home'),CARGO_TARGET_DIR=str(ROOT/'.deps/chat-response-owned-diff-target'))
with (H/'owned-decode-differential.log').open('w') as f:
 run([str(rust/'bin/cargo'),'run','--offline','--locked','--bin','owned-decode-check'],cwd=H/'Rust',env=env,stdout=f,stderr=subprocess.STDOUT)
assert '66408 actual original/specialized outcomes: 1723 full records, 64685 exact Debug errors' in (H/'owned-decode-differential.log').read_text()
output=Path(os.environ.get('CHAT_RESPONSE_OUTPUT_ROOT',str(H/'Revisions/owned-transfer-audit'))).resolve();env=os.environ.copy();env['CHAT_RESPONSE_OUTPUT_ROOT']=str(output)
modules=['GeneratedOwnedTransferred.TypesExternal','GeneratedOwnedTransferred.Types','GeneratedOwnedTransferred.FunsExternal','GeneratedOwnedTransferred.Funs','OwnedTransferredReference']
with (H/'owned-transfer-audit.log').open('w') as f:
 run(['python3',str(H/'check.py'),*modules],env=env,stdout=f,stderr=subprocess.STDOUT)
log=(H/'owned-transfer-audit.log').read_text();assert 'sorryAx' not in log
assert "decode_normal_form' depends on axioms: [propext]" in log
assert "decode_error' depends on axioms: [propext]" in log
paths=[H/x for x in ['check_owned_transfer.py','replay_owned_slice.py','owned-slice-replay.json','owned-slice-transfer.diff','Rust/src/owned_slice_replay.rs','Rust/src/bin/owned-decode-check.rs','Rust/src/lib.rs','Rust/Cargo.lock','extract.py','translate.py','OwnedTransferredReference.lean']]+sorted((H/'GeneratedOwnedTransferred').glob('*.lean'))
report={'candidate_only':True,'scope':'Actual generated owned decode wrapper control/error projection; merge is an explicit dictionary operation, NOT a proved response decoder.','source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in paths},'objects':{str(output/('ChatResponseReferenceWork/'+m.replace('.','/')+'.olean')):sha(output/('ChatResponseReferenceWork/'+m.replace('.','/')+'.olean')) for m in modules},'extraction':json.loads((H/'Artifacts/owned_transferred/inventory.json').read_text()),'translation':json.loads((H/'owned_transferred-translation.json').read_text()),'rustc':subprocess.check_output([str(rust/'bin/rustc'),'--version'],text=True).strip(),'native_differential':(H/'owned-decode-differential.log').read_text(),'lean_log':log,'remaining':['Universal source equivalence of the narrowly typed buffer transfer is a translation boundary supported by exact source diff and native comparisons.','Actual default merge/schema/streaming composition is not discharged here.','std UTF8 raw-pointer body and full internal String DropGuard mutation refinement remain open.']}
(H/'owned-transfer-audit.json').write_text(json.dumps(report,indent=2)+'\n');print('owned transfer candidate: kernel and 66408 native comparisons PASS')
