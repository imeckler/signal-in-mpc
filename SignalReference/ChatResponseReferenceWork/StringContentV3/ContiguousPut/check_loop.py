#!/usr/bin/env python3
"""Kernel actual-loop elision + native control/byte/suffix comparisons."""
from pathlib import Path
import subprocess,json,os,hashlib
H=Path(__file__).resolve().parent;ROOT=H.parents[3];CHAT=H.parents[1];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=ROOT/'.deps/libsignal-vendor/bytes-1.12.0/src/buf/buf_mut.rs';checksum=json.loads((source.parents[2]/'.cargo-checksum.json').read_text())['files']['src/buf/buf_mut.rs'];assert sha(source)==checksum
subprocess.run(['python3',str(H/'replay.py')],check=True,timeout=30)
rust=ROOT/'.deps/rust-nightly-2026-08-18';env=os.environ.copy();env.update(PATH=str(rust/'bin')+os.pathsep+env['PATH'],CARGO_HOME=str(ROOT/'.deps/libsignal-cargo-home'),CARGO_TARGET_DIR=str(H/'Build/native'))
with (H/'native.log').open('w') as f:subprocess.run([str(rust/'bin/cargo'),'run','--offline','--locked','--bin','check'],cwd=H/'Rust',env=env,stdout=f,stderr=subprocess.STDOUT,check=True,timeout=120)
native=(H/'native.log').read_text();assert 'Compared 7020 actual/original-replay/guarded-single-body Vec results and exact suffixes' in native
output=H/'Build/loop-final';env['CHAT_RESPONSE_OUTPUT_ROOT']=str(output)
modules=['StringContentV3.ContiguousPut.LoopLowering','StringContentV3.ContiguousPut.CanonicalTake']
with (H/'loop-audit.log').open('w') as f:subprocess.run(['python3',str(CHAT/'check.py'),*modules],env=env,stdout=f,stderr=subprocess.STDOUT,check=True,timeout=120)
log=(H/'loop-audit.log').read_text();assert 'sorryAx' not in log
for name in ['loop_lowering','body_suffix','canonical_stop','canonical_lowering']:assert name+"' depends on axioms:" in log
assert sha(source)==checksum
files=[H/p for p in ['check_loop.py','replay.py','replay.json','LoopLowering.lean','CanonicalTake.lean','Rust/Cargo.toml','Rust/Cargo.lock','Rust/.cargo/config.toml','Rust/src/lib.rs','Rust/src/bin/check.rs']]
old=ROOT/'SignalReference/ProtoParseWork/BytesReferenceWork';dependencies=[old/'Generated/vec_replace_put_body/Funs.lean',old/'Generated/vec_replace_put_body/Types.lean',old/'Modules/ProtoParseWork/BytesReferenceWork/Generated/vec_replace_put_body/FunsExternal.lean',old/'Modules/BytesReferenceWork/VecReference.lean']
(H/'loop-audit.json').write_text(json.dumps({'candidate_only':True,'scope':'Actual accepted generic Vec.put loop equals guarded single-body control on explicit canonical contiguous Take content. Includes errors/divergence and exact successful body suffix. No full String/raw-trait source composition claim.','source_sha256':{str(p.relative_to(ROOT)):sha(p) for p in files},'actual_loop_dependencies_sha256':{str(p.relative_to(ROOT)):sha(p) for p in dependencies},'pinned_bytes_source_sha256':checksum,'native_log':native,'kernel_log':log,'object_sha256':{str(output/('ChatResponseReferenceWork/'+m.replace('.','/')+'.olean')):sha(output/('ChatResponseReferenceWork/'+m.replace('.','/')+'.olean')) for m in modules},'remaining':['Raw/trait ABI and actual Std Take content bridge of the specialized generated copier.','Kernel-check generated copier and compose actual String/owned-error result.']},indent=2)+'\n');print('actual loop lowering/canonical exhaustion/native7020 PASS')
