Candidate contiguous byte-field reference (NOT yet root-accepted)

The unchanged Prost 0.14.4 bytes::merge and actual Vec<u8>::replace_with /
bytes 1.12.0 Vec::put bodies are translated by pinned RELEASE Aeneas. The
bytes merge extraction has seven reversible unused Step metadata removals,
recorded in ../FieldReferenceWork/Artifacts/bytes-step. The Vec extraction
has NO LLBC preprocessing. No Rust computational body is edited. The optional
replace_with root and explicit foreign put inclusion select existing bodies;
they do not supply replacement code. The Skip translator candidate is not used.

Content models added here (exact template diffs in model-diff.patch):
* immutable Bytes is its remaining Slice U8 contents; reference counts,
  allocation identity and capacity are unobserved;
* copy_to_bytes follows content prefix/suffix and bounds on a CONTIGUOUS Buf
  whose chunk is all remaining contents. It is not a model for arbitrary
  segmented, effectful or overriding Buf implementations;
* Bytes remaining/chunk/advance/copy are the corresponding content views;
* Vec<u8> clear returns empty contents, reserve preserves contents on the
  modeled usize bound, and has_remaining uses remaining>0. reserve/clear are
  used only on Vec<u8>, not arbitrary destructible T. Existing Aeneas
  extend_from_slice and u8 clone models are reused unchanged.

NEW TRUST BOUNDARY: these models abstract successful normal allocation and
valid Rust slices/Vecs. They do not model allocation failure, isize::MAX
capacity panics, allocator state, reference counts, Drop side effects, pointer
identity or memory erasure. Content theorems quantify all model slices; applying
them to Rust requires valid Rust buffers and successful bounded allocation
(e.g. parser buffers below isize::MAX). This precondition is external to the
content theorem, not a proved Rust allocator property. No whole-memory claim.
The unused UninitSlice type is only a dictionary-signature placeholder;
no uninitialized-memory operation is modeled or called by this parsing path.

The actual replacement bridge projects the same remaining/chunk/advance/default
has_remaining methods between extraction-local Buf types. All UNOBSERVED
BytesAdapter dictionary fields remain universally quantified; no dummy append
implementation, signature-validation flag or axiom stands in for replacement.
The concrete replace_with method is the extracted Rust function. The loop is
proved for one contiguous chunk (including empty), not arbitrary streams.

Kernel proofs cover prefix/suffix partition and length, overflow rejection,
wire type first, varint errors preserving old value and exact suffix, length
underflow, successful actual Vec replacement, total MODELED field behavior
using accepted varint PrefixPost/ErrorPost, and later duplicate overwriting.
The nine accepted full-varint proofs are replayed after exact common-body
comparison; only names/imports plus the explicit copy_to_bytes dictionary slot
change. This does NOT yet prove the numeric parser, generated SignalMessage
merge, table lookup, complete scan/group invariants or AIG parser agreement.

check_oracle.py checks 5,638 native public cases against unchanged pinned bytes
and Prost. Fixtures support model/source review; they are not universal proofs.
audit.py rebuilds every candidate module, checks transitive axiom closures,
verifies inherited source/inventory/oracle hashes and freezes exact inputs.
Only propext, Classical.choice and Quot.sound may occur. Original candidate
flags stay false until a separate root-review.json records scoped acceptance.
