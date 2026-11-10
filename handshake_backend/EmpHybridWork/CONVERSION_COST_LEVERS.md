# Reducing the cost of a private X25519: three levers

Status 2026-11-09. Investigation only; nothing here is implemented. Measured figures come from `hybrid-v3-report.json` and `validation-report.json` (statistical 128, loopback, bytes sent per party). Everything marked *estimate* is arithmetic from those figures and has not been run.

## Measured baseline

| Quantity | Value | Source |
|---|---|---|
| MASCOT triple, 255-bit field | about 79 KB | 2.276 GB / 28,935 triples and 1.077 GB / 13,503 triples agree (78.7, 79.8 KB) |
| Triples generated but unused | 3–5% | "794 / 695 triples left" in the run logs |
| Boolean AND at ρ = 128 | about 0.8 KB | SHA-256 graph, 22.5k ANDs, 36.1 MB both directions |
| Field multiplications per X25519 | 4,589 curve + 23,552 pool check | `NATIVE_LOGICAL completed_products=28141` |

So one operation today is about 0.36 GB for the curve and 1.86 GB for a fresh 1,024-pair mask pool. A field multiplication costs roughly 100× a Boolean AND, which decides everything below.

## Lever 1 — amortise the pool

The cut/bucket bound improves with pool size (same counting bound as `parameters.py`):

| Kept pairs | Bucket at ρ = 128 | Field multiplications per pair |
|---|---|---|
| 2^10 | 12 | 23 |
| 2^12 | 10 | 19 |
| 2^16 | 8 | 15 |
| 2^20 | 7 | 13 |

*Estimate* per operation (766 pairs consumed): 0.91 GB from a 2^16 pool, 0.79 GB from a 2^20 pool, against 1.86 GB now. Worth roughly 2×, no new cryptography, but the pool stays more than twice the cost of the curve. The generator currently admits only 256/512/1,024 and `parameters.py` caps at 4,096.

## Lever 2 — a cheaper triple source: not available for this prime

MP-SPDZ's homomorphic-encryption protocols (LowGear, HighGear) do not take a caller's prime. `FHE/NTL-Subs.cpp` generates the plaintext prime itself from a bit length and asserts `pr % m == 1` for the cyclotomic index; `FHE/FFT_Data.cpp` throws `invalid_params` when `(p−1) % 2m ≠ 0`. For p = 2^255 − 19, p − 1 = 4·(2^253 − 5), so no power-of-two ring of useful size fits. The tree here also has only `mascot-party.x` and `tinier-party.x` built.

MASCOT's ~79 KB per triple is in line with its OT-based design scaling with the square of the field size; I found no setting that changes it materially. Emulating the field multiplication in the Boolean engine would be far worse (*estimate*: tens of thousands of ANDs, 30–60 MB per multiplication).

Conclusion: the triple price is fixed; the only way down is fewer field multiplications.

## Lever 3 — do the checking in the Boolean engine, and convert less

Three changes, in order of value. All are *estimates* and (b), (c) are constructions that need review.

**(a) Stop converting the scalar per operation.** The ladder needs the scalar's bits as field elements, but nothing needs the scalar in Boolean form afterwards (only DH outputs enter the KDF). A long-term scalar can be converted once and kept as authenticated field-bit shares; an ephemeral scalar can be born in the field (each party inputs bits, one bitness check and one XOR multiplication per bit: about 768 triples, 61 MB, once per key). That removes 256 of the 766 pairs per operation. Existing-key import still needs a one-time bit conversion.

**(b) Full-width masks for the coordinate in and the result out.** Each of these converts one 255-bit field element, so it needs one uniform r ∈ F_p held as a field share and as 255 Boolean bits, not 255 single-bit pairs. Proposed generation, following the cut/bucket pattern already used but with the nonlinear work moved to the Boolean side:

1. Each party inputs candidates r_j as one field element and as 255 Boolean bits, with a Boolean range check r_j < p.
2. Joint coin; open a fraction of candidates in both engines and compare.
3. Joint-coin bucketing; within a bucket, for each non-reference s: open r_ref + s in the field (linear, MAC-checked) and the mod-p sum from a Boolean adder; compare. s is uniform, so the opening hides r_ref.
4. The mask is r^A + r^B mod p: linear in the field, one Boolean mod-p adder.

No field multiplications. A candidate whose two encodings differ survives only if its whole bucket is inconsistent with cancelling differences, which is the same event the existing counting bound covers. *Estimate*: 24–44 MB per mask depending on batch size (bucket 12 at 1,024 masks, 22 at 16), so 50–90 MB for the two an operation needs, against about 600 MB for 510 single-bit pairs.

This is modelled on the extended-daBit idea of Escudero et al. (CRYPTO 2020), recalled rather than re-read; using a mod-p adder directly, so that no carry bit needs converting, is my variation.

**(c) Cheaper single-bit pairs where they are still needed.** For a party's private bits b_i: input each as a field share with a bitness check (one multiplication), form s = Σ 2^i b_i linearly, and verify s against the Boolean bits with one full-width check as in (b). Uniqueness of binary representation then forces each field share to equal its Boolean bit. With the cross-party XOR that is about 3 field multiplications per pair instead of 13–23.

## Projected cost per operation (*estimate*, bytes sent per party)

| Configuration | Conversion | Curve | Total |
|---|---|---|---|
| Today (fresh 1,024 pool) | 1.86 GB | 0.36 GB | 2.2 GB |
| Lever 1 only (2^16 pool) | 0.91 GB | 0.36 GB | 1.3 GB |
| Lever 1 + (a) | 0.60 GB | 0.36 GB | 1.0 GB |
| (a) + (b) | 0.05–0.09 GB | 0.36 GB | about 0.45 GB |

After (a) and (b) the curve's own 4,589 triples are the floor. They are independent of the inputs and can be generated ahead of time, so they are a bandwidth cost rather than a latency cost.

## Implemented and measured (later on 2026-11-09)

(a) and (b) are implemented as candidates in `word_mask.h` and `curve_fixture_v2.cpp`, together with free multiplication by public constants in the field engine (`FieldEngine::scale`, used by `CurveProgram::evaluate`; the pinned program is unchanged). `check_hybrid_v3.py` runs both fixtures; bytes sent per party, one cold loopback run each:

| | Original fixture | New fixture |
|---|---|---|
| Native field traffic | 2.28 GB | 0.43 GB |
| Field multiplications | 28,141 | 4,841 |
| Boolean traffic (sent, one party) | 4 MB | 151 MB for a batch of 16 masks, 2 consumed |
| Boolean AND gates | 4,600 | 537,055 |
| Wall time | 6.7 s | 2.3 s |
| Peak memory | 868 MB | 919 MB |

The 4,841 multiplications are 768 for the scalar's bitness checks and XORs (once per key in a real caller) and 4,073 for the curve (529 constant multiplications removed; 13 products with derived constants still use a triple). Measured Boolean cost was about 0.5 KB per AND for both directions together at this chunk size, lower than the estimate above, so a 16-mask batch came to about 17 MB per mask for both directions together.

Counting only what one operation consumes (2 of 16 masks), that is about 0.45 GB per party against 2.28 GB, a factor of five; with the scalar conversion amortised per key, about 0.34 GB.

Fault cases now exercised: every candidate inconsistent between engines (rejected at the cut), a single inconsistent candidate (rejected at the cut or its bucket), and a non-bit scalar contribution (rejected at the bitness opening). The result still matches the independent library value, and low-order and mismatch cases still reject.

Not yet done: (c); pool amortisation for single-bit pairs; batches larger than 16 (the generator keeps large wire arrays on the stack); the optimised ladder and masked inversion described in the review discussion (about 2,800 curve multiplications instead of 4,073), which need a new verified field program.

## Circuits from Lean, and the leaner ladder (2026-11-10)

Rule adopted: every circuit is compiled from Lean. The path above no longer contains hand-written gate logic. Reproduce with `lower_word_circuits.py` (exports, checks and pins), `build_hybrid_v3.py`, `check_hybrid_v3.py`.

| Lean module | What it defines | What is proved |
|---|---|---|
| `TlsMpc/BoolDag.lean` | Gate-level Boolean circuits (XOR/AND with shared subterms), multi-output, with a validated translation to a node list | `compile_correct`: every accepted compilation computes its source expressions |
| `TlsMpc/WordMask.lean` | Modular add, single reduction, range and threshold bits, zero test; the exported mask circuits | Value of each against natural-number arithmetic for all inputs (`modAdd_val`, `reduceOnce_val`, `belowP_eval`, `atLeast32_eval`, `isZero_eval`, `intoField_val`), and the two masking round-trip identities |
| `TlsMpc/FieldBits.lean` | Field-side bitness check, bit XOR, bit recomposition, mask pair | On bit inputs the check is zero and the XOR is the XOR; recomposition is Horner evaluation minus the reference |
| `TlsMpc/FieldDagMulti.lean` | Multi-output field compilation | `compileAll_correct` |
| `TlsMpc/X25519Fast.lean` | Leaner ladder returning the projective pair | `compiled_correct`: for every accepted compilation, the quotient of the two outputs is the RFC 7748 specification already used by `TlsMpc.X25519` |
| `TlsMpc/X25519SwapBits.lean` | Swap bits from scalar bits (no AND gates) | Each output equals the swap bit the ladder theorem assumes; XOR shares commute with the derivation |

All theorems depend only on `propext`, `Quot.sound` and, for the word arithmetic, `Classical.choice`.

Gate counts of the Lean exports: modular add 765 AND gates (the earlier hand-built C++ was 766; the bit-vector compiler route gave 1,275). The ladder has 2,794 products between secret values against 4,073: one product per coordinate pair in each conditional swap, swap bits supplied as inputs instead of computed in the field, and the final inversion done as a masked opening (two products) instead of a 254-squaring exponentiation.

Outside the theorems: the text printer in `EmitWordMask.lean`, the C++ loaders, and the masked inversion itself (that x·r/(z·r) = x/z for nonzero r, z is field algebra not mechanised here). The masked inversion opens z·r, which is uniform when z ≠ 0 and reveals only the all-zero outcome otherwise. `lower_word_circuits.py` checks every export against integer arithmetic or an independent X25519 library before pinning it.

Measured on the same checks (per party, one cold loopback run):

| | Original fixture | Current fixture |
|---|---|---|
| Native field traffic | 2.28 GB | 0.29 GB |
| Field products | 28,141 | 3,552 |
| Boolean traffic, both directions | 7 MB | 278 MB for 16 masks (843 MB for 64) |
| Wall time | 6.0 s | 1.5 s |

The 3,552 products are 2,794 for the ladder, 2 for the mask pair and 756 for the swap-bit shares (once per key). With 64 masks per batch the Boolean cost is about 13 MB per mask for both directions together, against 17 MB at 16.

## Review points for (b)

1. Counting bound: a candidate is bad if its Boolean bits are non-canonical or differ from its field value. Opened bad candidates are rejected; a kept reference is range-checked; a canonical but inconsistent reference passes its bucket only if every partner is also bad. This is the event `parameters.py` bounds, with the same parameters (bucket 22 for 16 masks, cut factor 2).
2. The range check on kept references is necessary: a reference encoded as f + p would pass its bucket against good partners.
3. Each partner s is used in exactly one opening r_ref + s, so the opening is uniform; the final mask rA + rB is uniform if either party is honest.
4. Both engines' candidate inputs are fixed (and the field side MAC-checked) before the first joint coin.

## Recommendation

Keep (a), (b), (c) and the leaner ladder as the working path; all four are implemented and exercised. Lever 1 alone remains the fallback if (b) does not survive review. Lever 2 is closed for this field. Open on this path: mask batches of 256 and 1,024, a cheating-party test inside the bucket adders, and mechanising the bitness converse and the masked-inversion identity (both need the field to have no zero divisors).
