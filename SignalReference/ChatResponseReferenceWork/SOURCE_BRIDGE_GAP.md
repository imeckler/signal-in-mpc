The actual response source bridge remains incomplete. The owned wrapper, actual
Prost default merge driver/key dependency, and HTTP completion flags have new
kernel-checked components, but no theorem yet equates the full streaming circuit
with the actual chat response decoder.

The current concrete obstruction is the borrowed buffer returned through
`bytes::merge_one_copy`'s generic `BytesAdapter::replace_with` call at pinned
Prost `encoding.rs:740`. Its instantiation is `Take<&mut B>`. The generic
Aeneas interface returns only the replacement field; the instantiated caller
also needs the mutated borrowed buffer. A narrow actual `mem::forget` guard
specialization is committed and tested. A pure Take-constructor inline candidate
also translates, but does not resolve the remaining adapter interface.

Pinned Charon's intended `--monomorphize-mut=all` rejects its transformed LLBC
with a mismatch between the original and specialized Buf trait dictionaries.
The supported `except-types` variant, with required `--remove-adt-clauses` and
`--lift-associated-types=*`, fails at the same call. This needs a type-preserving
trait-clause substitution repair in
`charon/src/transform/normalize/partial_monomorphization.rs`, or an equivalently
narrow verified-by-inspection specialization/inlining pipeline; bypassing the
type check is not acceptable. Full monomorphization is a different unsuccessful
candidate: it erases the DropGuard lifetime while retaining its mutable Vec
reference, which Aeneas rejects before translating functions.

`source-bridge-gap.json` records exact receipts/log/source hashes. Candidate
sources and generated files are preserved under ignored
`Revisions/string-abi-candidates`; canonical translator/model sources and tested
TLS/private-parser modules were not changed. No live check handles remain.
The std UTF8 unsafe-body bridge and full mutable String error-state theorem
remain separate obligations; the existing executable UTF8 specification and
owned-error cleanup observation do not imply them.
