#!/usr/bin/env python3
"""Scoped source/primitive dispatcher integration, not complete response proof."""
from pathlib import Path
import hashlib,json,os,subprocess
H=Path(__file__).resolve().parent;ROOT=H.parents[2];CHAT=H.parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[CHAT/'BytesContentV1/audit.json',CHAT/'StringContentV3/audit.json',CHAT/'StringContentV3/full-audit.json',CHAT/'RepeatedStringV1/audit.json',CHAT/'SchemaV1/diagnostic-audit.json'];source_maps={};objects={}
for path in receipts:
 receipt=json.loads(path.read_text())
 for name,digest in receipt['source_sha256'].items():assert sha(ROOT/name)==digest,name;source_maps[name]=digest
 for name,digest in receipt.get('objects_sha256',receipt.get('object_sha256',{})).items():
  p=Path(name);assert sha(p)==digest,p
  module=name.rsplit('ChatResponseReferenceWork/',1)[1]
  if module in objects:assert objects[module][1]==digest,('inherited object conflict',module)
  objects[module]=(p,digest)
# No blanket ancestor rebuild: link exact verified objects into the new output.
out=H/'Build/final';out.mkdir(parents=True,exist_ok=True)
for module,(p,digest) in objects.items():
 target=out/'ChatResponseReferenceWork'/module
 if target.exists():assert sha(target)==digest,target
 else:target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(p.resolve())
raw=H/'Artifacts/schema.llbc';extraction=json.loads((H/'extraction.json').read_text());assert extraction['exit_code']==0 and extraction['has_errors'] is False and sha(raw)==extraction['llbc_sha256'];named=raw.with_name('named.llbc')
subprocess.run(['python3',str(CHAT/'PartialMonoCandidate/name_specializations.py'),str(raw),str(named)],check=True,timeout=30)
binary=ROOT/'SignalReference/ProtoParseWork/MessageReferenceWork/FnItemCandidate/candidate-dbae191bb9f72719';assert sha(binary)=='dbae191bb9f7271935b70966ead68296d4d5f5369a16b70e6c4450f188a2a164';translation=H/'Build/translation';command=[str(binary),'-backend','lean',str(named),'-dest',str(translation),'-subdir','/ChatResponseReferenceWork/InnerResponseV1/Generated','-namespace','ActualInnerResponseV1','-split-files','-warnings-as-errors','-no-progress-bar','-sequential']
with (H/'retranslation.log').open('w') as f:subprocess.run(command,stdout=f,stderr=subprocess.STDOUT,check=True,timeout=30)
for p in (H/'Generated').glob('*.lean'):assert p.read_bytes()==(translation/'ChatResponseReferenceWork/InnerResponseV1/Generated'/p.name).read_bytes(),p
for script in ['replay.py','replay_scalars.py','make_callbacks.py']:subprocess.run(['python3',str(H/script)],check=True,timeout=30)
modules=['Replayed.Types','BufferBridge','ScalarSource','ScalarReference','StringBridge','BytesBridge','SkipBridge','Callbacks','Replayed.FunsExternal','Replayed.Funs','FieldSpec','DispatcherReference','BytesReference','StringReference','SkipReference'];files=[H/p for p in ['extract.py','extraction.json','replay.py','replay.json','replay_scalars.py','scalar-source.json','make_callbacks.py','callback-models.json','check.py','README.md','Rust/Cargo.toml','Rust/Cargo.lock','Rust/.cargo/config.toml','Rust/build.rs','Rust/src/lib.rs']]+[H/Path(*m.split('.')).with_suffix('.lean') for m in modules]+list((H/'Generated').glob('*.lean'));before={str(p.relative_to(ROOT)):sha(p) for p in files}
env=os.environ.copy();env['CHAT_RESPONSE_OUTPUT_ROOT']=str(out)
with (H/'audit.log').open('w') as f:subprocess.run(['python3',str(CHAT/'check.py'),*['InnerResponseV1.'+m for m in modules]],env=env,stdout=f,stderr=subprocess.STDOUT,check=True,timeout=240)
log=(H/'audit.log').read_text();assert 'sorryAx' not in log
for name in ['scalar_full_reference','default_exact','dispatcher_reference','bytes_source_exact','bytes_full_reference','string_full_reference','headers_full_reference','skip_full_reference']:assert name+"' depends on axioms:" in log
for name,digest in {**source_maps,**before}.items():assert sha(ROOT/name)==digest,name
for module,(p,digest) in objects.items():assert sha(p)==digest,p
(H/'audit.json').write_text(json.dumps({'candidate_only':True,'scope':'Actual generated inner response default/complete field dispatcher and all primitive bridges, preserving option initialization, existing fields, errors/cleanup, exact suffix and modeled allocation/divergence. No complete scan, outer submessage, HTTP or streaming/compiler theorem yet.','source_sha256':before,'inherited_receipts_sha256':{str(p.relative_to(ROOT)):sha(p) for p in receipts},'inherited_source_count':len(source_maps),'inherited_object_count':len(objects),'llbc_sha256':sha(raw),'named_llbc_sha256':sha(named),'translator_sha256':sha(binary),'translation_command':command,'kernel_log':log,'objects_sha256':{str(out/'ChatResponseReferenceWork/InnerResponseV1'/Path(*m.split('.')).with_suffix('.olean')):sha(out/'ChatResponseReferenceWork/InnerResponseV1'/Path(*m.split('.')).with_suffix('.olean')) for m in modules},'boundaries':['Explicit executable diagnostic callback model: actual static-reference push extraction remains OPEN/trusted, no warning-log equivalence.','Inherited executable UTF8/std unsafe body, bounded successful allocation and canonical contiguous buffer/Take/raw loan content models.','Unused encode-only append fails closed. Supported buffer domain is contiguous; no arbitrary segmented Buf claim.'],'remaining':['Full scan→streaming state invariants and private actual end.','Actual outer envelope/submessage/owned decoder composition.','HTTP headers/Unicode trim source validation, correlation and compiler composition.']},indent=2)+'\n');print('15-module inner default/dispatcher/actual primitive integration PASS; scan/outer/streaming open')
