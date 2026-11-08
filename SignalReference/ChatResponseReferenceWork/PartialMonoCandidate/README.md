This is a scoped Charon candidate for the actual Prost String/Vec adapter call.
It is not a general generic-trait-method implementation and does not establish
whole String or response refinement.

`python3 build.py` copies the pinned Charon source into ignored Source, patches
only that copy, and builds separate binaries. `python3 check.py` reproduces the
original error, static/free positive and abstract/mixed negative regressions,
4,097 native typed-counterpart comparisons, unchanged Prost String extraction,
name-only normalization, Aeneas translation, and the minimal kernel theorem.
All paths, source/binary hashes and exact commands are in audit.json and its
build/test receipts. The canonical tool and models remain unchanged.

The seven-line abstract regression has a generic Adapter method receiving
Take<&mut B>. Charon's partial-monomorph pass specializes the supplied Buf
proof while leaving that generic method unspecialized. The candidate limits
closed dictionary specialization to the exact one-copy adapter function and its
fixture counterpart. It keeps the concrete closed Self type and supplied static
impl, substitutes the original predicates with binder-aware APIs, retains all
region/outlives bounds, and resolves the actual inherited sealed method through
Charon's existing parent-proof and method resolvers. The remaining type/buffer
parameters stay generic. The old template is removed only after a whole-crate
function-reference check proves it unused. Any remaining abstract caller is an
explicit error. Existing post-transformation type checks remain enabled.

Aeneas otherwise aliases partial-specialization names and cannot derive an impl
name when specialization consumes the Self type parameter. name_specializations
changes declaration names/rename attributes only; it checks the entire semantic
payload, including every body/type/region, is unchanged. No generated Lean body
is edited. The existing isolated naming-only Aeneas binary is hash checked.

The minimal generated module has no external model declarations. Its theorem
preserves the delegate operation's normal/failure/divergent result and exact
borrowed buffer for every implementation. Actual Prost extraction/translation
now succeed, and generated one-copy/replace/put signatures retain borrowed state.
The full generated Prost module is not kernel-checked yet: std UTF8/content
models and an opaque mutable Buf.advance trait-field/auxiliary-backward interface
need separate composition. Precise DropGuard error mutation remains distinct
from the already proved owned-error observation.
