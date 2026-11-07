# Actual RustCrypto AES linear-operation bridges

This directory proves that selected numeric circuits implement the actual
`aes 0.9.1` software functions locked by libsignal v0.106.1
(`904c8dc8216073b078a5f2f5090e3da8382e6a92`). The proof target is equality to
faithfully translated implementation behavior. It does not require a separate
proof that RustCrypto satisfies an AES standard or a cryptographic security
property.

The accepted operation endpoints are:

| Actual Rust function | Existing byte operation used by the circuit | Numeric refinement theorem |
| --- | --- | --- |
| `soft::fixslice::mix_columns_0` | `TlsMpc.Aes.mixColumns` | `SignalReference.AesLinear.mix_refines_artifact` |
| `soft::fixslice::shift_rows_1` | `TlsMpc.Aes.shiftRows` | `SignalReference.AesLinear.shift_refines_artifact` |
| `soft::fixslice::shift_rows_2` | two applications of `TlsMpc.Aes.shiftRows` | `SignalReference.AesLinear.shift2_refines_artifact` |
| `soft::fixslice::shift_rows_3` | three applications of `TlsMpc.Aes.shiftRows` | `SignalReference.AesLinear.shift3_refines_artifact` |

Each endpoint covers all values of four secret sixteen-byte blocks. The actual
Rust state is eight `u64` bitplanes in the ordinary layout already proved in
`LibSignalReference.Proofs.AesLayout`. The output remains secret and is encoded
as eight little-endian `u64` words. The numeric artifact has 512 secret input
bits and 512 secret output bits.

`Mix.lean` and `Shift.lean` are Std-only circuit definitions and compiler
homomorphisms. `Reference.lean` and `ShiftReference.lean` establish equality to
the generated Rust word operations. `Layout.lean`, `BitBasics.lean`,
`BitFormula.lean`, `Proofs.lean`, and `ShiftBits.lean` relate those word operations
to the root byte operations. `Bridge.lean` and `ShiftBridge.lean` compose that
equality with the proved numeric AIG exporter. The final statements include
successful return from the selected actual operation. Separate lemmas preserve
the three extracted ShiftRows functions' assertion failure for slices of public
length other than eight. The numeric circuits fix that public length to eight.

## Extraction and trusted boundary

`extract_linear.py` invokes the pinned Charon and Aeneas tools in
`../pins.json` against the unchanged locked source. It selects the actual
64-bit software module using `RUSTFLAGS='--cfg aes_backend="soft"'` and target
`aarch64-apple-darwin`. The file is named `src/soft/fixslice64.rs`; its Rust
module path is `soft::fixslice`. There are no source patches, replacement Rust
functions, explicit exclusions, or opaque cryptographic functions. This is a
reference to the selected software configuration, not to a hardware-accelerated
default backend. Its debug assertions are retained by the extraction.

The MixColumns call graph contains five translated bodies: `mix_columns_0`,
`rotate_rows_1`, `rotate_rows_2`, `ror`, and `ror_distance`. Its one opaque
standard-library function is `u64::rotate_right`, supplied by the pinned Aeneas
standard model. Array indexing and updates, scalar shifts, addition, and XOR
also use existing Aeneas models.

The ShiftRows call graph contains the three real loops and `delta_swap_1`.
Aeneas generates loop-body and loop definitions, giving ten generated functions.
The computational standard models are slice length, mutable-slice iteration,
iterator advancement and borrow writeback, and scalar bit operations. The
blanket `IntoIterator` operation is an identity and is inlined by translation.
Two extra opaque clone declarations and thirty opaque type declarations are
unused iterator/panic metadata. `core::slice::iter::IterMut` is the one opaque
type that is computationally relevant and has an existing Aeneas model. The
generated `Types.lean` files contain no definitions. `check.py` checks the exact
inventories, selected-body function references, and absence of computational
references to discarded namespaces.

The Charon/Aeneas translation and existing standard-library models remain
trusted. `check.py` verifies the relevant model sources byte-for-byte against
the pinned official Aeneas archive and checks toolchain/package pins. The Lean
proof audit accepts only `propext`, `Classical.choice`, and `Quot.sound`. No
custom axioms, admitted proofs, opaque crypto assumptions, or native-decide
proofs are used. Small Boolean identities use kernel evaluation.

Native Lean execution, JSON serialization, and the generic Python/backend
adapter remain unverified. `Export.lean` only serializes the already-proved
circuits. The audit checks the zero vector and all 512 input-bit basis vectors,
packed into integer lanes, against an independent byte-matrix/permutation
calculation. It checks both raw AIG traversal and the generic XOR-optimized
adapter. These native checks supplement the Lean theorem; they do not replace
it or establish an MPC execution/security result. No shared MPC compiler paths
are used by this audit.

## Reproduction

```sh
python3 SignalReference/AesLinearWork/extract_linear.py MixColumns0
python3 SignalReference/AesLinearWork/extract_linear.py ShiftRows
python3 SignalReference/AesLinearWork/check.py \
  --packages-dir /Users/izzy/repos/eco-theorem-combined/.lake/packages
```

`Artifacts/*/inventory.json` records extraction provenance and generated-source
hashes. `proof-check.json` records the accepted proof endpoints, exact source
and standard-model hashes, gate counts, and native-artifact checks. The
canonical layout modules are rebuilt as proof dependencies; their source
hashes are included in the report. The root and canonical source hashes must
remain unchanged during the audit.

The checked run audited 38 theorem endpoints. Its four-block MixColumns circuit
has 2,176 executed XOR gates and zero executed AND gates after the generic
adapter rewrite (the raw AIG has 6,528 AND gates encoding those XORs). Each
ShiftRows artifact has 513 nodes, including one unused constant node and 512
input wires, with no AND or XOR gates. All four artifacts passed the zero and
512-basis-vector checks in both adapter modes.

## Remaining composition work

This proves MixColumns phase zero in the ordinary layout. The other fixslice
MixColumns variants require their actual phase-dependent representation
relations; no such invariant is assumed here. Whole RustCrypto AES equality
still needs those phases, the key schedule, round composition and output-layout
conversion, followed by the actual cipher/CBC wrapper composition. The separate
padding proofs and these linear-operation proofs do not establish complete
Signal encryption/decryption or verification-before-release behavior.
