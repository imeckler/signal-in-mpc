#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,subprocess,tempfile,shutil
H=Path(__file__).resolve().parent;CHAT=H.parent;ROOT=H.parents[2];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
extraction=json.loads((H/'extraction.json').read_text());assert extraction['exit_code']==0 and extraction['has_errors'] is False
assert sha(H/'Artifacts/schema.llbc')==extraction['llbc_sha256']
binary=ROOT/'SignalReference/ProtoParseWork/SkipTranslatorWork/Bin/candidate'
assert sha(binary)=='5ea6276549fac0be5c55ac6608ae8b4efa1dd1b147c15a988543871d8094bbec'
translated=H/'Build/translation'
command=[str(binary),'-backend','lean',str(H/'Artifacts/schema.llbc'),'-dest',str(translated),'-subdir','/Generated','-namespace','FnMutBorrowV1','-split-files','-warnings-as-errors','-no-progress-bar','-sequential']
with (H/'retranslation.log').open('w') as log:subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=30)
for p in (H/'Generated').glob('*.lean'):assert p.read_bytes()==(translated/'Generated'/p.name).read_bytes(),p
subprocess.run(['python3',str(H/'replay.py')],check=True,timeout=30)
# Unsupported argument-shape changes fail closed before an adapted module exists.
for old,new in [('Std.U32 × Std.U32 × Std.U32','Std.U32 × Std.U32 × Std.U64'),('core.ops.function.FnMut','unsupported.FnMut')]:
 with tempfile.TemporaryDirectory() as name:
  tmp=Path(name);shutil.copytree(H/'Generated',tmp/'Generated');shutil.copyfile(H/'replay.py',tmp/'replay.py')
  p=tmp/'Generated/Funs.lean';s=p.read_text();assert old in s;p.write_text(s.replace(old,new))
  run=subprocess.run(['python3',str(tmp/'replay.py')],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=30)
  assert run.returncode!=0,'unsupported ABI silently accepted'
# Original generated computations, with namespace/import paths only, must fail.
u=H/'Unadapted';u.mkdir(exist_ok=True)
for p in (H/'Generated').glob('*.lean'):
 s=p.read_text().replace('namespace FnMutBorrowV1','namespace UnadaptedFnMutBorrowV1').replace('end FnMutBorrowV1','end UnadaptedFnMutBorrowV1').replace('import Generated.Types','import ChatResponseReferenceWork.FnMutBorrowV1.Unadapted.Types')
 (u/p.name).write_text(s)
out=H/'Build/final';env=os.environ.copy();env['CHAT_RESPONSE_OUTPUT_ROOT']=str(out)
with (H/'unadapted.log').open('w') as log:
 failed=subprocess.run(['python3',str(CHAT/'check.py'),'FnMutBorrowV1.Unadapted.Types','FnMutBorrowV1.Unadapted.Funs'],env=env,stdout=log,stderr=subprocess.STDOUT,timeout=120)
assert failed.returncode!=0
originalLog=(H/'unadapted.log').read_text();assert 'error:' in originalLog
modules=['Projection','Replayed.Types','Replayed.Raw','ActualProjection','Replayed.Funs','Reference']
files=[H/Path(*m.split('.')).with_suffix('.lean') for m in modules]+list((H/'Generated').glob('*.lean'))+[H/n for n in ['extract.py','extraction.json','replay.py','replay.json','check.py','README.md','Rust/Cargo.toml','Rust/Cargo.lock','Rust/src/lib.rs','native.rs']]
before={str(p.relative_to(ROOT)):sha(p) for p in files}
with (H/'audit.log').open('w') as log:
 subprocess.run(['python3',str(CHAT/'check.py'),*['FnMutBorrowV1.'+m for m in modules]],env=env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=180)
log=(H/'audit.log').read_text();assert 'sorryAx' not in log
rust=ROOT/'.deps/rust-nightly-2026-08-18/bin/rustc';native=H/'Build/native';native.parent.mkdir(parents=True,exist_ok=True)
subprocess.run([str(rust),str(H/'native.rs'),'-o',str(native)],check=True,timeout=60)
run=subprocess.run([str(native)],check=True,stdout=subprocess.PIPE,text=True,timeout=30);assert run.stdout.startswith('8192 ')
for name,digest in before.items():assert sha(ROOT/name)==digest,name
(H/'audit.json').write_text(json.dumps({'candidate_only':True,'scope':'Minimal original generated FnMut borrowed-triple caller/helper connected by scoped typed raw/trait projection, not actual Prost integration.','source_sha256':before,'kernel_log':log,'unadapted_expected_failure':originalLog,'negative_shape_cases':2,'translator_sha256':sha(binary),'translation_command':command,'native_cases':8192,'native_stdout':run.stdout,'objects_sha256':{str(out/'ChatResponseReferenceWork/FnMutBorrowV1'/Path(*m.split('.')).with_suffix('.olean')):sha(out/'ChatResponseReferenceWork/FnMutBorrowV1'/Path(*m.split('.')).with_suffix('.olean')) for m in modules}},indent=2)+'\n')
print('Typed borrowed-triple projection PASS: original kernel rejection; adapted six-module kernel; 8192 native; two fail-closed ABI guards')
