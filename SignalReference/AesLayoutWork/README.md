The forward AES bit-layout operation is proved equivalent to the actual Aeneas-translated RustCrypto implementation. The selected function takes four secret 16-byte blocks and writes eight 64-bit bitplanes. The MPC operation uses only wire selection and concatenation; the exported artifact has 512 input wires, one constant node, and zero AND gates.

The reference is the unchanged `aes` 0.9.1 dependency locked by libsignal v0.106.1, commit `904c8dc8216073b078a5f2f5090e3da8382e6a92`. Extraction selects `aes::soft::fixslice::bitslice` from `src/soft/fixslice64.rs:1193-1267`, its nested `read_reordered` function, and `delta_swap_2` at lines 1121-1125. It selects the actual portable software backend using `--cfg aes_backend="soft"` on `aarch64-apple-darwin`. This does not claim equivalence to the separate hardware backend.

`bitslice_refines_artifact` in [Bridge.lean](Bridge.lean) proves that every numeric artifact output bit equals the encoding of the actual translated result. It covers every value of all 64 input bytes and every initial value of the eight output words. The public shape is fixed: four input slices of length 16 and an output slice of length 8. The actual length assertions remain in the generated reference; behavior outside this public shape is not claimed by this circuit theorem. All inputs and outputs remain secret.

The output encoding is eight little-endian u64 words in plane order 0 through 7. Within a word, bit `lane` equals bit `plane` of input block `lane % 4`, byte `(lane / 4) % 4 * 4 + lane / 16`. This mapping is proved for all 512 positions, using kernel-checked Lean proofs. `Network.lean` and `Circuit.lean` depend only on Std and the root compiler. The Aeneas reference and its bridges stay in this separate proof package.

Reproduce the extraction and proof audit with:

```sh
python3 SignalReference/AesLayoutWork/extract_layout.py Bitslice
python3 SignalReference/AesLayoutWork/check.py \
  --packages-dir /Users/izzy/repos/eco-theorem-combined/.lake/packages
```

The accepted toolchain is Aeneas `5b9dcf33dccdb1560ea7203ac57ea202476b6ed3`, Charon `4ad295c1bf982b5533ce7d85f4ddc889ff3127f8`, Rust nightly 2026-08-18, and Lean 4.31.0. [The parent pin file](../pins.json) records archive and actual source hashes. `extract_layout.py` performs no Rust source edits and the accepted `Bitslice` profile has no explicit exclusions or opaque patterns.

The generated call graph has three actual structured functions and nine standard-library entries. Computational models are the existing Aeneas checked slice lengths, indexing, range indexing, updates, unsigned-byte conversion, checked shifts, and bitwise operations. Other slice-trait methods appear only as dictionary metadata; the selected execution does not call unchecked indexing. The sole opaque type declaration is `core::fmt::Arguments`, discarded with panic formatting. Generated `Types.lean` has no declarations and no formatting call remains. No crypto function is opaque or modeled by a custom assumption. The check compares relevant standard-model files with the pinned official Aeneas archive.

[proof-check.json](proof-check.json) records the successful 16-theorem audit, exact proof and model hashes, and the standalone artifact hash. Only `propext`, `Classical.choice`, and `Quot.sound` appear in the audited dependency sets. The exporter and JSON transport remain unverified; the additional structural check inspects all 512 exported output references and confirms they select each input bit exactly once. No native MPC execution is claimed here.

The reverse `inv_bitslice` wrapper remains incomplete. The plain profile fails Charon's GAT lifting on `hybrid_array::traits::ArraySize`. Excluding that trait lets Charon finish, but Aeneas fails in `PrePasses.update_array_default` at `hybrid-array` 0.4.13 `src/sizes.rs:26`. Attempts to select the nested `write_reordered` helper directly and with a wildcard fail Charon path resolution. Their inventories and logs are retained under `Artifacts/InvBitslice*` and `Artifacts/WriteReordered*`; none is an accepted reference. The complete AES key schedule, rounds, reverse layout, CBC composition, and authenticated-release composition remain separate obligations.

RustCrypto's MIT and Apache 2.0 licenses are preserved in `LICENSES/`.
