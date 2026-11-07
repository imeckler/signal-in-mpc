This directory isolates the actual RustCrypto PKCS7 leaf used by pinned
libsignal v0.106.1 (`904c8dc8216073b078a5f2f5090e3da8382e6a92`). Its Cargo.lock
selects `block-padding` 0.4.2; the extracted source is the unmodified
`src/lib.rs` implementation of `Pkcs7::raw_pad`, lines 186–195. The source hash
and crate archive hash are in `../pins.json`. No handwritten Rust function is
used as the reference.

`Generated/ExcludeArraySize/Funs.lean` is direct output from the existing pinned
Charon 0.1.245/Aeneas August 27 stack. It preserves the two panic checks,
checked `usize` subtraction, narrowing byte cast, mutable suffix indexing, and
slice fill. Charon and Aeneas both exit successfully, with `has_errors=false`.
There are no external Lean templates or generated type assumptions.

`Proofs.lean` proves the exact successful output for every slice length at most
255 and every valid position. Separate theorems prove the translated
`.fail .assertionFailure` result for oversized slices and positions at or past
the end, including empty slices. `raw_pad_total` covers every translated input.
The panic payload and formatting are erased by the translation; the theorem
does not claim to preserve a Rust panic string, unwinding, or allocator effects.

`cbc_pad_refines_artifact` connects every compiled output bit to this actual
translated operation for a 16-byte AES block and every position 0–15. Both
the slice bytes and circuit inputs may be arbitrary secrets. The public length
restriction makes the translated error branches unreachable in this circuit
operation. `cbc_message_pad_refines_artifact` additionally preserves an
arbitrary secret prefix containing whole 16-byte blocks. A zero-length tail
therefore adds a full padding block, covering empty and block-aligned messages.
This is an implementation equivalence proof for padding. The RustCrypto AES
and CBC wrapper composition is still a separate obligation.

The extraction excludes these declarations:

- `block_padding::Padding::{pad,unpad,pad_detached,unpad_blocks}`;
- `block_padding::*::{raw_unpad,unpad}`;
- `hybrid_array::traits::ArraySize`.

None is called by the selected `Pkcs7::raw_pad` body, whose arguments are a
plain byte slice and an integer. The default generic trait method signatures
pull in `ArraySize` despite the selected function having no generic array
argument. Excluding only those default methods still fails Charon's GAT
transformation; excluding `ArraySize` removes the unused type-level graph.
These exclusions do not justify claims about the omitted array-based wrappers,
unpadders, trait implementations, or complete CBC encryption.

The function depends on the existing Aeneas standard models for scalar
comparisons, checked subtraction, casts, slice length/indexing/backward updates,
and `Slice.fill` with `CloneU8`. `check.py` compares the relevant model files
byte-for-byte with the pinned official Aeneas archive. The full LLBC inventory
also contains unused `SliceIndex` dictionary methods and panic-formatting
metadata. Its only opaque type is `core::fmt::Arguments`; Aeneas removes that
metadata with the panic formatting, and generated `Types.lean` is empty. The
generated function has no formatting calls. These standard models and faithful
Charon/Aeneas translation remain the explicit trusted reference boundary.

Reproduce extraction and the complete local check with:

```sh
python3 SignalReference/PaddingWork/extract_padding.py ExcludeArraySize
python3 SignalReference/PaddingWork/check.py --packages-dir /path/to/matching/.lake/packages
```

The proof check validates pinned source hashes, exact extraction inventory and
exclusions, generated-file hashes, unchanged standard models, and matching Lean
and mathlib versions. It compiles the proofs and audits all eight theorem
endpoints for dependencies on custom assumptions. The resulting
`proof-check.json` records their scope and hashes. No finite vector comparison
or native proof checker is used to establish these theorems.

The generated reference and LLBC derive from RustCrypto's MIT-or-Apache-2.0
source; both license texts are preserved in `licenses/`. This directory does
not change the repository's license or the licenses of other generated Signal
references.
