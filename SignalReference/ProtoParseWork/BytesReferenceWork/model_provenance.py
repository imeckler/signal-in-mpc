#!/usr/bin/env python3
import hashlib,json,difflib
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[2];FIELD=HERE.parent/'FieldReferenceWork'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 pairs=[(FIELD/'Generated/bytes_step/TypesExternal_Template.lean',HERE/'Modules/ProtoParseWork/FieldReferenceWork/Generated/bytes_step/TypesExternal.lean'),
 (FIELD/'Generated/bytes_step/FunsExternal_Template.lean',HERE/'Modules/ProtoParseWork/FieldReferenceWork/Generated/bytes_step/FunsExternal.lean'),
 (HERE/'Generated/vec_replace_put_body/FunsExternal_Template.lean',HERE/'Modules/ProtoParseWork/BytesReferenceWork/Generated/vec_replace_put_body/FunsExternal.lean')]
 diff=''.join(''.join(difflib.unified_diff(a.read_text().splitlines(True),b.read_text().splitlines(True),fromfile=str(a.relative_to(ROOT)),tofile=str(b.relative_to(ROOT))))for a,b in pairs)
 (HERE/'model-diff.patch').write_text(diff)
 paths=['.deps/libsignal-vendor/bytes-1.12.0/src/bytes.rs','.deps/libsignal-vendor/bytes-1.12.0/src/buf/buf_impl.rs','.deps/libsignal-vendor/bytes-1.12.0/src/buf/buf_mut.rs','.deps/libsignal-vendor/prost-0.14.4/src/encoding.rs','.deps/rust-nightly-2026-08-18/lib/rustlib/src/rust/library/alloc/src/vec/mod.rs']
 report={'candidate_only':True,'accepted_model':False,'rust_changes':[],
 'source_sha256':{p:sha(ROOT/p)for p in paths},'model_and_template_sha256':{str(p.relative_to(ROOT)):sha(p)for pair in pairs for p in pair},
 'delta_sha256':sha(HERE/'model-diff.patch'),'scope_document_sha256':sha(HERE/'README.txt'),
 'new_trusted_assumptions':['Content representation of immutable Bytes','Contiguous-only Buf.copy_to_bytes content model','Vec<u8> clear/reserve content model under valid-buffer and successful allocation below isize::MAX assumptions','Extraction-local trait dictionary projection preserves remaining/chunk/advance/default has_remaining methods'],
 'not_claimed':['Arbitrary Buf','Allocator/capacity/isize panic or OOM equivalence','Generic Drop or uninitialized memory','Memory erasure','Whole numeric parser agreement']}
 (HERE/'model-provenance.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
