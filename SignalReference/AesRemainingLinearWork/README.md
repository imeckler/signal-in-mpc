# Actual RustCrypto MixColumns phases 1–3

This directory proves numeric-circuit equality to the actual locked
`aes 0.9.1` functions `soft::fixslice::mix_columns_1`, `mix_columns_2`, and
`mix_columns_3`, used by libsignal v0.106.1 at
`904c8dc8216073b078a5f2f5090e3da8382e6a92`. It uses the canonical layout,
MixColumns0 and ShiftRows proofs already integrated under
`LibSignalReference.Proofs.Aes*`. The reference is the selected 64-bit software
backend, extracted with `--cfg aes_backend="soft"` on `aarch64-apple-darwin`.

## Proved operation and representation

Let `S` be the existing root byte ShiftRows operation and `M` the existing byte
MixColumns operation. The three actual functions implement

```text
M_k = S^(-k) ∘ M ∘ S^k              k = 1, 2, 3
```

The masks in the Rust rotate helpers independently wrap rows and columns. A
one-row step at phase `k` advances the column by `k`; a two-row step advances it
by `2k`. `WordBits.lean` proves this coordinate relation for every input word
bit, then `Phase.lean` proves the conjugation. It also proves the four-ShiftRows
cycle and the round representation invariant: a state in phase `k−1` becomes a
state in phase `k` while the corresponding byte state applies ShiftRows and
MixColumns. These are equivalences to the extracted operations, not assumed
layout invariants or independent AES security claims.

`Circuit.lean` is Std-only. Its canonical `phaseBytes` uses the existing root
operations. Its efficient `phaseFastBytes` expresses ShiftRows as direct public
index permutations, avoiding repeated list construction. `phaseFastBytes_eq`
and `fast_network` prove the two constructions equal on the fixed public shape.
The symbolic circuit uses this fast path; its generic compiler refinement is
proved for all assignments.

`Reference.lean` proves all six rotate-helper instances and all three real
MixColumns functions equal to their word transformations. `Bridge.lean` joins
these results to the numeric AIG exporter. Its final theorem is
`SignalReference.AesRemainingLinear.mix_phases_refine_artifact`; public tags
`0,1,2` select the actual Rust phases `1,2,3`. It covers every value of four
secret sixteen-byte blocks. The Rust state has exactly eight `u64` bitplanes;
the output is encoded as eight secret little-endian `u64` words. No input or
output bit is opened.

## Extraction, assumptions, and checks

`extract_remaining.py MixColumnsPhases` extracts the unchanged dependency source
through the pinned Charon/Aeneas stack in `../pins.json`. There are ten translated
function bodies and one opaque standard-library declaration, `u64::rotate_right`,
provided by the existing pinned Aeneas model. Array indexing/updates and scalar
checked shifts, addition, XOR, AND and OR also use existing standard models.
There are no type declarations, global declarations, trait dictionaries,
exclusions, source patches, discarded metadata, or opaque cryptographic
functions in this selected graph.

The translator and its standard models remain trusted. The audit checks the
relevant model files against the official pinned Aeneas archive, verifies the
generated-source hashes and exact inventory, and rejects proof holes or custom
axioms. The canonical AES dependencies are reused from the existing successful
audit after checking all their source hashes. The only accepted foundational
axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Native execution/serialization and the generic backend adapter remain
unverified. `check.py` exports all three circuits and checks the zero vector
and all 512 input-bit basis vectors against a separate byte-matrix calculation
with the actual phase-dependent row/column coordinates. Both raw AIG traversal
and the generic XOR-optimized traversal are checked. These checks supplement
the Lean theorem and make no native MPC or network-execution claim.

```sh
python3 SignalReference/AesRemainingLinearWork/extract_remaining.py MixColumnsPhases
python3 SignalReference/AesRemainingLinearWork/check.py \
  --packages-dir /Users/izzy/repos/eco-theorem-combined/.lake/packages
```

The accepted audit and artifact statistics are in `proof-check.json`. The full
extraction inventory is `Artifacts/MixColumnsPhases/inventory.json`.

The checked run audited 27 theorem endpoints. Each of the three four-block
artifacts has 2,176 executed XOR gates and zero executed AND gates after the
generic adapter rewrite. Each raw AIG has 7,041 nodes, including 6,528 AND gates
encoding those XORs. All three passed the zero and 512-basis-vector checks.

## AES-256 key-schedule feasibility candidate

`extract_remaining.py Aes256KeySchedule` separately selects the real
`aes256_key_schedule`. Charon succeeds with eighteen structured bodies and
forty-three opaque standard-library declarations. Direct Aeneas translation
fails because the builtin `Iterator` dictionary lacks `rev`; the log points to
the key-schedule step-by loop at `fixslice64.rs:249` and `memshift32`'s actual
reverse loop at line 1354. This candidate is not an accepted reference.

The existing Aeneas library does model the computational `rev` constructor and
reverse iterator advancement. In this concrete LLBC, `memshift32` directly calls
the regular function declaration 40, while the `Iterator.rev` dictionary slot
is not called by a selected structured body. The called declaration remains
necessary, including review of its `TraitDefault` provenance. A possible
metadata-only preprocessing step must retain that function and the reverse
computation. The graph also contains the newer unused `Step` overflow slots.
No preprocessing or model changes have been applied here; the separate parent
extraction work is investigating that possibility. The raw failure, graph and
tool versions remain in `Artifacts/Aes256KeySchedule/`.

Whole AES/CBC equality is still incomplete. It needs key-schedule equality,
round/key composition, the output layout, and the actual cipher/CBC wrappers.
These completed linear phases do not discharge those obligations.
