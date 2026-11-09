#!/usr/bin/env python3
from pathlib import Path
import os,json,hashlib,subprocess
H=Path(__file__).resolve().parent;CHAT=H.parent;ROOT=H.parents[2];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
queue=[CHAT/'InnerScanV1/audit.json',CHAT/'FnMutBorrowV1/audit.json'];seen={};objects={};sources={}
while queue:
 path=queue.pop()
 if str(path) in seen:continue
 seen[str(path)]=sha(path);data=json.loads(path.read_text())
 for name,digest in data['source_sha256'].items():assert sha(ROOT/name)==digest,name;sources[name]=digest
 for name,digest in data.get('inherited_receipts_sha256',{}).items():assert sha(ROOT/name)==digest,name;queue.append(ROOT/name)
 for name,digest in data.get('objects_sha256',data.get('object_sha256',{})).items():
  p=Path(name);assert sha(p)==digest,name;module=name.rsplit('ChatResponseReferenceWork/',1)[1]
  if module in objects:assert objects[module][1]==digest,module
  objects[module]=(p,digest)
out=H/'Build/final'
for module,(p,digest) in objects.items():
 target=out/'ChatResponseReferenceWork'/module
 if target.exists():assert sha(target)==digest,target
 else:target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(p.resolve())
extraction=json.loads((H/'extraction.json').read_text());assert extraction['exit_code']==0 and extraction['has_errors'] is False
assert sha(H/'Artifacts/schema.llbc')==extraction['llbc_sha256']
subprocess.run(['python3',str(CHAT/'PartialMonoCandidate/name_specializations.py'),str(H/'Artifacts/schema.llbc'),str(H/'Artifacts/named.llbc')],check=True,timeout=30)
binary=ROOT/'SignalReference/ProtoParseWork/SkipTranslatorWork/Bin/candidate';assert sha(binary)=='5ea6276549fac0be5c55ac6608ae8b4efa1dd1b147c15a988543871d8094bbec'
command=[str(binary),'-backend','lean',str(H/'Artifacts/named.llbc'),'-dest',str(H/'Build/translation'),'-subdir','/Generated','-namespace','ActualSubmessageV1','-split-files','-warnings-as-errors','-no-progress-bar','-sequential']
with (H/'retranslation.log').open('w') as log:subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=30)
for p in (H/'Generated').glob('*.lean'):assert p.read_bytes()==(H/'Build/translation/Generated'/p.name).read_bytes(),p
subprocess.run(['python3',str(H/'replay.py')],check=True,timeout=30)
modules=['Replayed.Types','Replayed.FunsExternal','Replayed.Raw','ActualProjection','Replayed.Funs','Reference']
files=[H/Path(*m.split('.')).with_suffix('.lean') for m in modules]+list((H/'Generated').glob('*.lean'))+[H/n for n in ['check.py','extract.py','extraction.json','replay.py','replay.json','README.md','Rust/Cargo.toml','Rust/Cargo.lock','Rust/.cargo/config.toml','Rust/src/lib.rs','Native/Cargo.toml','Native/Cargo.lock','Native/.cargo/config.toml','Native/build.rs','Native/src/main.rs']]
before={str(p.relative_to(ROOT)):sha(p) for p in files};env=os.environ.copy();env['CHAT_RESPONSE_OUTPUT_ROOT']=str(out)
with (H/'audit.log').open('w') as log:subprocess.run(['python3',str(CHAT/'check.py'),*['SubmessageV1.'+m for m in modules]],env=env,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=180)
log=(H/'audit.log').read_text();assert 'sorryAx' not in log
for name in ['actual_closure_projection','wrong_wire','recursion_zero','delimited_overrun','delimited_exact_end']:assert name+"' depends on axioms:" in log
rust=ROOT/'.deps/rust-nightly-2026-08-18';env.update(PATH=str(rust/'bin')+os.pathsep+env['PATH'],DYLD_LIBRARY_PATH=str(rust/'lib'),CARGO_HOME=str(ROOT/'.deps/libsignal-cargo-home'),CARGO_TARGET_DIR=str(H/'Build/native'),CARGO_BUILD_JOBS='1')
with (H/'native.log').open('w') as native:subprocess.run([str(rust/'bin/cargo'),'run','--offline','--locked','--quiet'],cwd=H/'Native',env=env,stdout=native,stderr=subprocess.STDOUT,check=True,timeout=90)
native=(H/'native.log').read_text();assert native.startswith('10800 ')
for name,digest in {**sources,**before}.items():assert sha(ROOT/name)==digest,name
for p,digest in objects.values():assert sha(p)==digest,p
(H/'audit.json').write_text(json.dumps({'candidate_only':True,'scope':'Kernel checked actual generic Prost submessage/merge-loop bodies through grounded typed borrowed-triple projection; exact wire/recursion/end/parent-overrun facts. Not complete outer/streaming refinement.','source_sha256':before,'inherited_receipts_sha256':{str(Path(p).relative_to(ROOT)):digest for p,digest in seen.items()},'inherited_source_count':len(sources),'inherited_object_count':len(objects),'translator_sha256':sha(binary),'translation_command':command,'llbc_sha256':sha(H/'Artifacts/schema.llbc'),'kernel_log':log,'native_cases':10800,'native_output':native,'objects_sha256':{str(out/'ChatResponseReferenceWork/SubmessageV1'/Path(*m.split('.')).with_suffix('.olean')):sha(out/'ChatResponseReferenceWork/SubmessageV1'/Path(*m.split('.')).with_suffix('.olean')) for m in modules}},indent=2)+'\n')
print('Actual submessage six-module kernel+10800 native comparisons PASS; complete submessage/outer/streaming composition OPEN')
