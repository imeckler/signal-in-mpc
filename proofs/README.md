# proofs/: the Mathlib-backed proof package

Proof-only Lean package (REORGANIZATION_PLAN.md section 1, rule 6, "Superseded 2026-11-12"). It
uses Mathlib to turn H-QR into theorems, to state hiding as probability, and to prove the
cut-and-choose counting bound. **Nothing in the main package imports it**, so no executable,
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
FieldDag, FieldDagMulti, X25519, EdwardsAffine, EdwardsHinted, Signal.XEdDsaField, GhashShares,
Ghash, ByteCircuit, Sha256, BoolDag, WordMask, MaskedAgreement and their imports (a few seconds).
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
5. **Cut-and-choose** (`CutAndChoose.lean`): a uniform challenge permutation puts a bad set of
   `B·t` candidates exactly on a union of whole buckets with probability exactly
   `C(N, t)/C(2BN, B·t)` (`parameters.py`'s `bound(t)`), and never if `B ∤ |S|`; and
   `bound(1) < 2⁻¹²⁸` for the batch profile (N = 2¹⁹, B = 8) and the three profiles of
   `check_parameters_128.py`.

## What stays a hypothesis or open

* **H-GROUP** (the Edwards formulas are the group law): stated as "any finite commutative group"
  where needed; never proved here.
* **idealCommit**: the distributional statements take the other party's values as independent of
  the honest party's mask; that is the modelling assumption `idealCommit` justifies.
* **Cut-and-choose, `t ≥ 2`:** that `bound(t) ≤ bound(1)` at the deployed parameters is not
  proved (`check_parameters_128.py` checks every `t` numerically). The model's detection rules
  (P-CUT(d), (e)) are assumptions of the model, not theorems about `dyn_word_mask.h`.
* **XEdDSA `recover`**: same mathematics as `recipient` but through `X25519.powBits`; not done.
* **`ceremony_masked_uniform`** restates the expression of `Ceremony.masked_hides` instead of
  importing `TlsMpc.CeremonyProofs`, whose imports (the receive kernels' proofs) would make this
  package compile a large part of the main library.
