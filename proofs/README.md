# proofs/: the Mathlib-backed proof package

Proof-only Lean package (REORGANIZATION_PLAN.md section 1, rule 6, "Superseded 2026-11-12"). It
uses Mathlib to turn H-QR into theorems, to state hiding as probability, to prove the
cut-and-choose counting bound, and to prove H-GROUP for the Edwards formulas (items 10–15). **Nothing in the main package imports it**, so no executable,
emitter or circuit-cache key can reach Mathlib.

## Layout and isolation

| Path | What |
|---|---|
| `lakefile.toml`, `lean-toolchain` (v4.31.0), `lake-manifest.json` | this package's own Lake configuration; requires Mathlib `v4.31.0` |
| `TlsMpcProofs/*.lean` | the proofs (below) |
| `TlsMpcProofs/SecurityMathlib.lean` | the index, in the format of `TlsMpc/Security.lean`, with `#print axioms` |
| `SECURITY_MATHLIB_AXIOMS.txt` | axioms of every theorem here, written by `scripts/check_axioms_mathlib.py` |
| `.lake/` (git-ignored) | the Mathlib checkout and cache (about 7.2 GB) and this package's build (about 30 MB) |

How the main package's definitions are reached: the library `TlsMpcSources` has
`srcDir = ".."` and root `TlsMpc`, so `import TlsMpc.FieldDag` here compiles the main package's
working-tree source **into `proofs/.lake/build`**. Only the modules the proofs import are compiled:
FieldDag, FieldDagMulti, X25519, EdwardsAffine, EdwardsHinted, Signal.XEdDsaField,
Signal.XEdDsaScalar (for `order`), Signal.Unpad, ByteAuth, GhashShares, Ghash, ByteCircuit, Sha256,
BoolDag, WordMask, MaskedAgreement and their imports (a few seconds). `Signal.ReceiveFirst`
(`varintValue`, `canonicalRange`) is deliberately not imported: its closure is 52 main-package
modules (about 9,400 lines: AES, TLS, Signal sessions).
A Lake `path` dependency on `..` was not used on purpose: Lake builds a path dependency inside the
dependency's own directory, so it would read and, when stale, rewrite the main package's `.lake`
while other engineers build there. The main package's `lakefile.toml`, `lake-manifest.json` and
`.lake` are never opened by this package.

Do not run `lake build TlsMpcSources`: that would compile the whole main library here.

## Commands (from the repository root; every build through `scripts/guarded.py`)

```
# once (or after changing the Mathlib rev): clone Mathlib and its dependencies into proofs/.lake,
# then download the prebuilt Mathlib .olean cache (Lake runs `lake exe cache get` itself as
# Mathlib's post-update hook). Never compiles Mathlib.
cd proofs && python3 ../scripts/guarded.py 4 1800 lake update
cd proofs && python3 ../scripts/guarded.py 4 1800 lake exe cache get     # only if the hook did not run

# build the proofs (does not need --heavy: it writes only proofs/.lake)
cd proofs && python3 ../scripts/guarded.py 12 3600 lake build TlsMpcProofs

# axioms of every theorem; writes proofs/SECURITY_MATHLIB_AXIOMS.txt; fails on anything beyond
# propext, Classical.choice, Quot.sound, and on sorry/native_decide/bv_decide/axiom/... in the sources
python3 scripts/check_axioms_mathlib.py
```

Measured on this machine (2026-11-12): `lake update` with the cache hook 107 s, peak 1.4 GB (the
Mathlib cache was already in the user's cache directory, so it only decompressed; a cold machine
also downloads it, a few GB); a from-scratch `lake build TlsMpcProofs` 22 s, peak 6.0 GB (Lake
compiles a few files in parallel; one Mathlib-importing file alone peaks at about 3.5 GB); the
axiom check 4 s, peak 3.3 GB. Disk: 7.3 GB under `proofs/.lake`.

## What is proved (all with only propext, Classical.choice, Quot.sound)

1. **`2²⁵⁵ − 19` is prime** (`Prime25519.lean`). Pocklington's criterion is proved from Mathlib
   (`orderOf`, `ZMod`, factorizations); the certificate chain is p ← Q (236-bit factor of p − 1)
   ← 31757755568855353 (a 55-bit factor of Q − 1, found by ECM) ← primes below 2·10⁶ (`norm_num`).
   The modular powers and gcds are evaluated by the kernel (`decide +kernel` on a structurally
   recursive square-and-multiply over `Nat`, which the kernel runs with GMP). No `native_decide`,
   no `decide` on primality itself, no hypothesis.
2. **Bridge** (`FieldBridge.lean`): `toZMod : FieldDag.F ≃+* ZMod p`; `ofNat`, `power`,
   `inverse` (the main package's definitions) are `ZMod p`'s cast, power and inverse.
3. **H-QR** (`QuadraticResidue.lean`): 2 is a non-square; Euler's criterion (both halves);
   `sqrtMinusOne = 2^((p−1)/4)` and squares to −1; the p ≡ 5 (mod 8) candidate (`c⁴ = x²` iff
   square; `c² = ±x`); the program `EdwardsAffine.recipient`: its check is zero iff its `x²` is a
   square, and then its `x` is a square root; the hinted lift: selection rule (`sel xor b`) for the
   formula and for `liftOpen`'s output, every value has exactly two preimages `(r, b)`, and the
   opened `w` is exactly uniform on F for `q ≠ 0` (also with the other party's bit XORed in).
4. **Hiding as probability** (`Uniform.lean`, `Hiding.lean`): `hiding_of_bijection` (a bijection
   on the uniform randomness carrying one view to the other gives equal output distributions) and
   its applications: `ghash_share_hides` (via the main package's `share_views_equal`), the ceremony
   mask, P-RAND(b), P-B2F(b), P-W2F(b), P-F2W(b), P-INV(c), `maskedAgreement_mask_hides` and
   P-HINT(c) (both for any finite commutative group).
5. **Cut-and-choose** (`CutAndChoose.lean`, `CutAndChooseAll.lean`): a uniform challenge
   permutation puts a bad set of `B·t` candidates exactly on a union of whole buckets with
   probability exactly `C(N, t)/C(2BN, B·t)` (`parameters.py`'s `bound(t)`), and never if
   `B ∤ |S|`; `bound(t + 1) ≤ bound(t)` for every `N`, every `B ≥ 2`, `1 ≤ t < N`
   (`bound_step`), so `t = 1` is always the worst case (`bound_le_bound_one`; monotonicity holds
   on the whole range, no exception); `bound(1) < 2⁻¹²⁸` for the batch profile (N = 2¹⁹, B = 8)
   and the three profiles of `check_parameters_128.py` (256/14, 512/13, 1024/12); hence for each
   of these four profiles `bound(t) < 2⁻¹²⁸` for every `1 ≤ t ≤ N` (`*_bound_all_t`) and **every
   bad set, of any size, goes undetected with probability `< 2⁻¹²⁸`** (`*_undetected_lt`, via
   `undetected_lt_of_bound_t1`).
6. **XEdDSA `recover`** (`XEdDsaRecover.lean`): `X25519.powBits` on the concrete field is the power
   by the big-endian bit value (`toZMod_powBits`), so `XEdDsaField.exponent x n = x^n` for
   `n < 2²⁵⁵`, `X25519.inverse = FieldDag.inverse` and `XEdDsaField.zero` is the zero indicator;
   `recover X25519.concrete u = [valid, x, y]` with explicit value forms (`recover_eq`); `valid` is
   0 or 1, and 1 iff `u + 1 ≠ 0`, `d·y² + 1 ≠ 0` and `xx` is a square; whenever `xx` is a square
   `x·x = xx` (the same square-root statement as for `recipient`, under a weaker hypothesis); and
   `y = (u − 1)/(u + 1)`. No hypothesis (H-QR is proved).
7. **Offset agreement as probability** (`OffsetAgreementDist.lean`): for any finite commutative
   group `G` of order `ℓ`, scalars in `ZMod ℓ` acting by `k ↦ k.val • B`, and the offset uniform
   in `ZMod ℓ`, the published key `initial·B + offset·B` has the same distribution for any two
   initial scalars (`offset_public_key_independent`); if `ℓ` is prime and `B ≠ 0` it is uniform
   on `G` (`offset_public_key_uniform`).
8. **The deployed offset sampling** (`OffsetSampling.lean`). As deployed (`service_kernels.h`
   `seal_open`/`ephemeral`, `edwards_points.h` `step`/`step_inputs`), τ = `(mine XOR peer) mod 2²⁵²`
   (32 random bytes per party, SHA-256 commit then open, bytes XORed, `offset[31] &= 15`).
   `deployedOffset_uniform`: τ is exactly uniform on `[0, 2²⁵²)` for uniform `mine` and any fixed
   `peer`. Generic: two injections of a uniform `R` into `Z` give distributions within
   `(|Z| − |R|)/|R|` on every event (`eventClose_injective`); one injection is within
   `(|Z| − |R|)/|Z|` of uniform on `Z` in total variation (`statClose_uniform`). Hence, for any
   `ℓ ≥ 2²⁵²` and any finite commutative group of order `ℓ`: the key for any two initial scalars
   within `(ℓ − 2²⁵²)/2²⁵²` (`deployed_key_close`; this, not `/ℓ`, is the right bound: two shifted
   ranges differ in up to `ℓ − 2²⁵²` points of mass `2⁻²⁵²`), within `(ℓ − 2²⁵²)/ℓ` of the ideal
   key and, `ℓ` prime and `B ≠ 0`, of uniform on `G` (`deployed_key_close_ideal`, `_uniform`).
   `prime_order`: the Ed25519 order `ℓ = 2²⁵² + 27742317777372353535851937790883648493`
   (`Signal.XEdDsaScalar.order`) is prime (Pocklington chain ℓ ← 138-bit ← 134 ← 88 ← 62 ← 51-bit
   ← primes below 2·10⁶, reusing `Prime25519.pocklington`). `order_gap_lt`:
   `(ℓ − 2²⁵²)/2²⁵² < 2⁻¹²⁷`; so `ed25519_key_close` (two initial scalars, every event within
   `2⁻¹²⁷`) and `ed25519_key_close_uniform` (within `2⁻¹²⁷` of uniform on `G`). Several messages:
   `offset_public_keys_independent` / `_uniform` (offsets uniform mod `ℓ`: the joint keys of `k`
   messages do not depend on the initial scalar; uniform on `G^k`, i.e. independent of each
   other), `deployedOffsets_uniform`, `deployed_keys_close` (union bound over the messages:
   `k·(ℓ − 2²⁵²)/2²⁵²`) and `ed25519_keys_close` (`k·2⁻¹²⁷`).
9. **`Unpad.decode` is PKCS#7 unpadding** (`UnpadSpec.lean`, a 16-byte block, concrete bytes):
   padded with `p` (`1 ≤ p ≤ 16`, last `p` bytes equal `p`; unique) it returns
   `[255, 16 − p] ++ take (16 − p) ++ p zeros` (`decode_padded`), otherwise eighteen zeros
   (`decode_unpadded`); the status byte is 255 iff the padding is valid (`decode_accepts_iff`).

10. **H-GROUP: the Edwards formulas are a group law** (`EdwardsPoly.lean`, `EdwardsCurve.lean`,
    `EdwardsEd25519.lean`). For any field with `2 ≠ 0`, `−1` a square and `d` not a square, the
    points of `−x² + y² = 1 + d·x²·y²` with the unified addition
    `((x₁y₂ + y₁x₂)/(1 + d·x₁x₂y₁y₂), (y₁y₂ + x₁x₂)/(1 − d·x₁x₂y₁y₂))`, negation `(−x, y)` and
    zero `(0, 1)` are a commutative group (`Edwards.Point.instAddCommGroup`): completeness
    (`sq_delta_ne_one`, Bernstein–Lange: the denominators never vanish), closure, commutativity,
    identity, inverse, and **associativity**. Associativity is route (a) of the task (Hales–Raya):
    the cross-multiplied identity lies in the ideal of the three curve equations; the cofactors
    (16, 64 and 40 terms per coordinate) were found by rewriting `d·xᵢ²·yᵢ² → yᵢ² − xᵢ² − 1`
    (a 150-line Python script without any algebra library, `.deps/lowering-scratch/hg_gen.py`,
    which writes `EdwardsPoly.lean`) and are checked by `linear_combination`; the whole file
    compiles in 4 s. Route (b) (transfer from Mathlib's Weierstrass group) was not needed.
    For `ZMod (2²⁵⁵ − 19)`, `d = −121665/121666`: `dK_not_isSquare` (Euler's criterion, kernel
    power), `neg_one_isSquare`, so `Ed25519.Curve` is that group. The main package's formulas
    compute in it: `affine_pointAddValue` (`EdwardsAffine.pointAddValue`), `affine_neg`
    (`negate`), `curveCheckValue_zero_iff_exists` (`curveCheck` is zero exactly on the curve),
    `extRep_extAddValue` (`EdwardsHinted.extAddValue`; its `Z` is never zero),
    `extRep_ofAffineValue`, `affine_toAffineValue`, `affine_sumTreeValue`, `extRep_extSumValue`
    (the balanced sums are the group sum); `recipient_onCurve`, `recover_onCurve` (a passed check
    / `valid = 1` gives a curve point).
11. **The base point has order exactly `ℓ`** (`EdwardsBasePoint.lean`). `base_onCurve`;
    `order_nsmul_base`: `ℓ·B = 0`, by double-and-add in extended coordinates over `ℕ` mod `p`
    evaluated by the kernel (`decide +kernel`, `Nat` only), proved equal to the group's scalar
    multiple (`castT_smulN`, `Edwards.rep4_smul`); with `prime_order`, `addOrderOf_base` and
    `card_zmultiples_base` (the subgroup generated by `B` has exactly `ℓ` elements; the same for
    any `P ≠ 0` with `ℓ·P = 0`, `card_zmultiples_of_order`). The theorems of items 4, 7, 8 that
    take "a finite commutative group (of order `ℓ`)" are instantiated: `curve_public_key_uniform`,
    `curve_key_close`, `curve_key_close_uniform`, `curve_keys_close`, `base_key_close_uniform`,
    `base_keys_close` (the subgroup), `curve_hinted_Z_uniform`,
    `curve_maskedAgreement_mask_hides` (the whole curve).
12. **X25519 is scalar multiplication in the same group** (`MontgomeryLadder.lean`). With
    `u = (1 + y)/(1 − y)`, projectively `(X : Z) = (1 + y : 1 − y)` (`MRep`): the ladder's doubling
    and differential addition are doubling and addition of Edwards points (`mrep_double`,
    `mrep_diffadd`, all degenerate cases included, only `u ≠ 0` required), `X25519.advance` maps
    `(Q, R)` to `(2Q, Q + R)` (`advance_rep`), the ladder holds `(n·P, (n+1)·P)`
    (`ladderSpec_inv`), and `spec_eq_montU`: for `u ≠ 0` the coordinate of a curve point `P`,
    `X25519.spec input u` is the coordinate of `k·P`, `k` the clamped scalar.
13. **The clamped scalar and `u = 0`** (`X25519Clamp.lean`, `X25519Special.lean`).
    `clampedScalar_eq`: for any input bits, `k = 2²⁵⁴ + 8·m`, `m` the value of bits 3 … 253;
    `clampedScalar_decodeScalar`: for the bytes as `X25519.decodeScalar` reads them,
    `k = 2²⁵⁴ + 8·(⌊n/8⌋ mod 2²⁵¹)`, `n` their little-endian value (RFC 7748: low three bits
    cleared, bit 255 cleared, bit 254 set); `k ≡ 0 (mod 8)`, `2²⁵⁴ ≤ k < 2²⁵⁵`. `spec_u_zero`:
    `X25519.spec input 0 = 0` (every ladder step leaves `X·Z = 0` in both registers); the group
    reading: `u = 0` is `T2 = (0, −1)` of order 2 and `k` is even, so `k·T2 = 0`
    (`spec_u_zero_montU`); hence `spec_eq_montU'` (no `u ≠ 0`) and `x25519_on_curve`: for every
    `u` with `u(u² + 486662u + 1)` a square, `X25519.spec input u = montU (k·P)` for a curve
    point `P` with that coordinate.
14. **The scalar-multiple chains** (`EdwardsScalarMul.lean`, `EdwardsBitSum.lean`).
    `window_spec` (`windowValue`: `P … 8P`, next base `16P`), `windowChain_spec` (entry `8w + j`
    of the table is `((j+1)·16^w)·P`), `bitEntry_spec` / `prepareHinted_bitEntry` (`2^i·P`, once
    every link holds); `doublings_spec`, `doublingsChain_spec`, `bitTable_entry` (entry `i` is
    `2^i·P`); generic `chain_spec`. Digits: `recode` is the signed base-16 rule of
    `edwards_points.h` (`digit = nibble + carry; carry = digit > 8; digit -= 16·carry`):
    `recode_value` (the digits encode the number), `recode_bound` (digits in `−8 … 8`),
    `recode_carry_zero`, `recode64_value` (64 windows, offset `< 2²⁵²`: exact, no carry);
    `signed_entry`, `offsetSum_value`, `offsetSum_recoded` (`offsetSum` outputs `u(I + n·P)`).
    Unsigned: `sum_choose_smul`; `bitSum_value`, `bitSum_eq_x25519` (`bitSum`'s quotient is
    `X25519.spec`); `prepareHinted_initial` (`(kA + kB)·P`). XEdDSA: `xrep_add`
    (`XEdDsaField.add` is the group law), `xrep_mulBits`, `doubleScalar_spec` (`[s]B − [h]A`),
    `run_doubleScalar_spec` (the `xeddsa` program for the bits of `h < 2²⁵⁶`, `s < 2²⁵³`).
15. **`liftPoint`'s map** (`MontgomeryLift.lean`). `sA2_mul_self`
    (`EdwardsHinted.sqrtMinusA2² = −486664`); `montgomery_lift`: for `v² = u(u² + 486662u + 1)`,
    `v ≠ 0`, the point `(√(−486664)·u/v, (u − 1)/(u + 1))` is on the curve (`u + 1 ≠ 0` follows:
    `486660` is not a square), with Montgomery coordinate `u`; `montgomery_lift_neg` (`−v` gives
    `−P`); `montQ_isSquare_iff`: `u(u² + 486662u + 1)` is a square exactly when `u` is the
    coordinate of a curve point (`v = 0` only at `u = 0`: `montW_ne_zero`, the discriminant is
    `−d·486664²`); `lift_root` (`valid = sel xor b = 1` means `s² = q·r²`); `liftPoint_valid`
    (the program outputs a curve point with coordinate `u` and `Z = M_A + M_B + P`),
    `liftPoint_invalid` (the base point); `x25519_lift`.

## What stays a hypothesis or open

* **What remains of H-GROUP.** Not proved: the group order `#E = 8ℓ` (point counting), so not:
  "every point killed by `ℓ` is a multiple of `B`", nor the cofactor claim of
  `edwards-torsion-hinted` (`8Q = P` has a solution exactly for `P` in the prime-order subgroup).
  The instantiated offset theorems therefore take `P ≠ 0` and `ℓ·P = 0` as hypotheses about the
  recipient's point (they hold for `B`). Also not proved: X25519 for a `u` that is not the
  coordinate of a curve point (the quadratic twist, `u(u² + 486662u + 1)` not a square). There
  the ladder computes scalar multiplication on the twist `2v² = u³ + 486662u² + u`, whose Edwards
  model `−2x² + y² = 1 + 2d·x²y²` has `a = −2`, not a square in `ZMod p`; `EdwardsCurve.lean`'s
  construction needs `a = −1` (a square) and `d` not a square (a complete law), and moving to
  `a = −1` needs `√2`, so the twist is not an instance; it would need the incomplete projective
  law or a transfer from Mathlib's Weierstrass group, plus the x-only formulas against it. Not
  stated: that the C++ `step` / `step_inputs` implement `recode` (the Lean definition copies the
  C++ rule; the C++ is not in Lean), and the C++ `Local/Edwards`. What is assumed about the curve
  after items 10–15 is therefore only: nothing for curve points (group law, completeness, base
  point order `ℓ`, X25519 for every curve `u`, all chains and the lift are theorems); the group
  order `#E = 8ℓ` (and so the torsion reading) and the twist behaviour of X25519 are open. The
  generic statements (items 4, 7, 8) keep the form "any finite commutative group".
* **idealCommit**: the distributional statements take the other party's values as independent of
  the honest party's mask; that is the modelling assumption `idealCommit` justifies.
* **Cut-and-choose model:** the detection rules (P-CUT(d), (e)) and the single uniform challenge
  permutation (standing for P-CUT's two) are assumptions of the model, not theorems about
  `dyn_word_mask.h` / `dabit_generator.h`.
* **Offset agreement:** the peer's value is a fixed value independent of the honest party's
  (`idealCommit`; SHA-256 as a commitment is not proved), and per message a fixed value (a peer
  adapting its values across messages is not covered); the aborts on `mine = peer` (probability
  `2⁻²⁵⁶`) and on τ = 0 (`crypto_scalarmult_ed25519_base_noclamp` refuses it, `2⁻²⁵²`) are not
  modelled (they depend only on the offsets, not on the initial scalar); the digit recoding is
  proved for the Lean `recode`, which copies the C++ `step` rule (item 14); that the C++ code is
  that rule is read off the source, not proved.
* **Receive accept direction:** the value forms of `varintValue` (counter widths 2–5) and
  `canonicalRange` (`< 2²⁵⁵ − 19`) are not stated: they live in `Signal.ReceiveFirst`, whose import
  closure is not compiled into this package.
* **XEdDSA:** the sign of `x` (not normalised by `recover`) and its binding to the signature
  bit (`doubleScalar` itself is item 14); that the compiled artifact is the program is the main
  package's `XEdDsaField.compiled_output_correct`, not re-proved here.
* **`ceremony_masked_uniform`** restates the expression of `Ceremony.masked_hides` instead of
  importing `TlsMpc.CeremonyProofs`, whose imports (the receive kernels' proofs) would make this
  package compile a large part of the main library.
* **Lean pitfall (recorded for the next author):** do not let Lean's defeq checker compare a
  term containing `FieldDag.power x n` (or `inverse`) with a form it can only reach by
  unfolding, e.g. `rfl` after `rw` on `[a, b, c][2]?.getD _`: it unfolds `power` with a 255-bit
  exponent and exhausts memory (12 GB in 40 s). Use list injectivity (`List.cons.injEq`) or
  rewriting instead, as `XEdDsaRecover.recover_components` does.
