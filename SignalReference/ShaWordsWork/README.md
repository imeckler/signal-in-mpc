# Unaccepted byte-loading candidate

The actual `sha2 0.11.0` `to_u32s` wrapper calls `core::array::from_fn`.
The default extraction leaves that constructor external. Extracting its actual
body with the recorded full-MIR sysroot reaches `try_from_fn_erased`, where
Aeneas reports “Can't copy a mutable borrow” at `core/src/array/mod.rs:930`.
The complete wrapper remains unproved.

`extract_selected.py` selects only the unchanged actual conversion closure and
its closed dependencies from the no-dedup LLBC. Charon's entry-path resolver
cannot directly select closure methods. The explicit selection deletes the
unproved caller and `from_fn`, changes no retained declaration, and checks for
remaining references. This selection is trusted and has not been accepted into
the canonical reference audit.

`Reference.lean` proves the closure's result for every 64-byte array and every
index below 16, retaining the unchanged captured array. However, the translated
`Result.unwrap` carries the existing Aeneas Debug dictionary and its opaque
`core.fmt.Formatter` type. The theorem's assumption audit reports that type
axiom as well as the three standard Lean axioms. Consequently this candidate
is **not counted among completed refinements**, and has no numeric circuit
bridge. No cryptographic body or Rust source was replaced.

The exact source, selection and assumption boundaries are in `review.json`.
The failed full-wrapper profiles are `Extraction/sha256_to_words.json` and
`Extraction/sha256_to_words_bodies.json`.
