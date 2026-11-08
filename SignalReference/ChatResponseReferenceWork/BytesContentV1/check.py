#!/usr/bin/env python3
"""Actual Bytes adapter/merger all-outcomes contiguous source checkpoint."""
from pathlib import Path
import os,subprocess,json,hashlib
H=Path(__file__).resolve().parent;ROOT=H.parents[2];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
extraction=json.loads((H/'extraction.json').read_text());assert extraction['exit_code']==0 and extraction['has_errors'] is False
raw=H/'Artifacts/bytes.llbc';assert sha(raw)==extraction['llbc_sha256'];named=raw.with_name('named.llbc')
subprocess.run(['python3',str(H.parent/'PartialMonoCandidate/name_specializations.py'),str(raw),str(named)],check=True,timeout=30)
binary=ROOT/'SignalReference/ProtoParseWork/SkipTranslatorWork/Bin/candidate';assert sha(binary)=='5ea6276549fac0be5c55ac6608ae8b4efa1dd1b147c15a988543871d8094bbec'
output=H/'Build/translation';command=[str(binary),'-backend','lean',str(named),'-dest',str(output),'-subdir','/ChatResponseReferenceWork/BytesContentV1/Generated','-namespace','ActualResponseBytesV1','-split-files','-warnings-as-errors','-no-progress-bar','-sequential']
with (H/'retranslation.log').open('w') as f:subprocess.run(command,stdout=f,stderr=subprocess.STDOUT,check=True,timeout=30)
for p in (H/'Generated').glob('*.lean'):assert p.read_bytes()==(output/'ChatResponseReferenceWork/BytesContentV1/Generated'/p.name).read_bytes(),p
assert 'def bytes.bytes.Bytes.Insts.ProstEncodingSealedBytesAdapter.replace_with' in (H/'Generated/Funs.lean').read_text()
subprocess.run(['python3',str(H/'replay.py')],check=True,timeout=30)
files=[H/p for p in ['extract.py','extraction.json','replay.py','replay.json','check.py','Reference.lean','FullReference.lean','README.md','Rust/Cargo.toml','Rust/Cargo.lock','Rust/.cargo/config.toml','Rust/src/lib.rs']]+list((H/'Generated').glob('*.lean'))+list((H/'Replayed').glob('*.lean'))
before={str(p.relative_to(ROOT)):sha(p) for p in files}
modules=['BytesContentV1.Replayed.TypesExternal','BytesContentV1.Replayed.Types','BytesContentV1.Replayed.FunsExternal','BytesContentV1.Replayed.Funs','BytesContentV1.Reference','BytesContentV1.FullReference'];out=H/'Build/final';env=os.environ.copy();env['CHAT_RESPONSE_OUTPUT_ROOT']=str(out)
with (H/'audit.log').open('w') as f:subprocess.run(['python3',str(H.parent/'check.py'),*modules],env=env,stdout=f,stderr=subprocess.STDOUT,check=True,timeout=180)
log=(H/'audit.log').read_text();assert 'sorryAx' not in log
for name in ['slice_copy','replace_bytes','bytes_wire_error','bytes_full_reference']:assert name+"' depends on axioms:" in log
for name,digest in before.items():assert sha(ROOT/name)==digest,name
vendorfiles=['prost-0.14.4/src/encoding.rs','prost-0.14.4/src/encoding/wire_type.rs','prost-0.14.4/src/error.rs','bytes-1.12.0/src/buf/buf_impl.rs','bytes-1.12.0/src/bytes.rs'];vendor={}
for relative in vendorfiles:
 package,name=relative.split('/',1);base=ROOT/'.deps/libsignal-vendor'/package;digest=json.loads((base/'.cargo-checksum.json').read_text())['files'][name];assert sha(base/name)==digest;vendor[relative]=digest
(H/'audit.json').write_text(json.dumps({'candidate_only':True,'scope':'Actual pinned Prost bytes::Bytes replacement body and full field merger, exact wrong-wire/varint/underflow/old-field/success/suffix behavior on contiguous bounded input. No adapter/decoder correctness or termination premise. Not full response schema/streaming refinement.','source_sha256':before,'pinned_vendor_sha256':vendor,'llbc_sha256':sha(raw),'named_llbc_sha256':sha(named),'translator_sha256':sha(binary),'translation_command':command,'kernel_log':log,'objects_sha256':{str(out/('ChatResponseReferenceWork/'+m.replace('.','/')+'.olean')):sha(out/('ChatResponseReferenceWork/'+m.replace('.','/')+'.olean')) for m in modules},'boundaries':['Reuse accepted immutable Bytes/safe contiguous buffer allocation/content model; backing allocation, reference counts, unsafe memory unobserved.','Unused encode-only append_to fails closed; no decode theorem invokes it.','Actual response schema/default/submessage/repeated headers, HTTP validation and private-end streaming/compiler composition remain open.']},indent=2)+'\n');print('actual Bytes adapter/merger: unchanged generation + six-module full reference PASS')
