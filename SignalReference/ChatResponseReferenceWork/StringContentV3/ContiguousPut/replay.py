#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
H=Path(__file__).resolve().parent;ROOT=H.parents[3];source=ROOT/'.deps/libsignal-vendor/bytes-1.12.0/src/buf/buf_mut.rs';text=source.read_text();section=text.index('unsafe impl BufMut for Vec<u8>');start=text.index('fn put<T: super::Buf>',section);opening=text.index('{',start);depth=1;end=opening+1
while depth:depth+=(text[end]=='{')-(text[end]=='}');end+=1
body=text[opening+1:end-1];assert body.count('self.')==2
special=re.sub(r'\bself\b','value',body)
lowered=special.replace('while src.has_remaining() {','if src.has_remaining() {');end_brace=lowered.rfind('}');lowered=lowered[:end_brace]+'assert!(!src.has_remaining());\n        '+lowered[end_brace:]
assert special.count('while src.has_remaining() {')==1
output=H/'Rust/src/lib.rs';output.write_text('''// Exact pinned Vec.put body with concrete contiguous Take<&mut &[u8]> input.
use bytes::Buf;
pub fn put_contiguous(value:&mut Vec<u8>,input:&mut &[u8],limit:usize) {
    let mut src = input.take(limit);
'''+special+'}\n\npub fn put_contiguous_one_step(value:&mut Vec<u8>,input:&mut &[u8],limit:usize) {\n    let mut src=input.take(limit);\n'+lowered+'}\n')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(H/'replay.json').write_text(json.dumps({'candidate_only':True,'source_sha256':sha(source),'original_body_sha256':hashlib.sha256(body.encode()).hexdigest(),'output_sha256':sha(output),'script_sha256':sha(Path(__file__)),'changes':'Rename self to value; concrete buffer Take<&mut &[u8]> introduced before unchanged body. Loop, operations, arguments and ordering unchanged.','domain':'Safe Sized contiguous immutable shared-slice buffer, modeled successful bounded Vec allocation; no general Buf claim.'},indent=2)+'\n')
