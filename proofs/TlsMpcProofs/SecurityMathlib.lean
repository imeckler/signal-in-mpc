import TlsMpcProofs.FieldBridge
import TlsMpcProofs.Prime25519
import TlsMpcProofs.Uniform
import TlsMpcProofs.QuadraticResidue
import TlsMpcProofs.Hiding
import TlsMpcProofs.CutAndChoose
import TlsMpcProofs.CutAndChooseAll
import TlsMpcProofs.XEdDsaRecover
import TlsMpcProofs.OffsetAgreementDist
import TlsMpcProofs.OffsetSampling
import TlsMpcProofs.UnpadSpec
import TlsMpcProofs.EdwardsCurve
import TlsMpcProofs.EdwardsEd25519
import TlsMpcProofs.EdwardsBasePoint
import TlsMpcProofs.MontgomeryLadder
import TlsMpcProofs.EdwardsScalarMul
import TlsMpcProofs.X25519Clamp
import TlsMpcProofs.MontgomeryLift
import TlsMpcProofs.X25519Special
import TlsMpcProofs.EdwardsBitSum

/-!
# Security theorems that use Mathlib (companion to `TlsMpc/Security.lean`)

Proof-only. This file is in the separate package `proofs/` (its own lakefile, Mathlib
dependency, `.lake`); nothing in the main package imports it, so no executable, emitter or
circuit-cache key depends on Mathlib (REORGANIZATION_PLAN.md section 1, rule 6, superseded
2026-11-12). Every entry restates a theorem of `proofs/TlsMpcProofs/*.lean` by direct reference,
as `TlsMpc/Security.lean` does. `#print axioms` for every entry is at the end;
`scripts/check_axioms_mathlib.py` runs this file and writes `proofs/SECURITY_MATHLIB_AXIOMS.txt`.

Statuses as in `TlsMpc/Security.lean` (**K**, **K-fn**, **C**, **M**, **switch**), plus
**gen** for generic lemmas (about any type, used to derive the others).

## What changed against `TlsMpc/Security.lean`'s hypotheses

* **H-QR is now proved** (section 2), including the primality of `p = 2²⁵⁵ − 19` (section 1),
  with no hypothesis. The square-root formulas (`recipient`) and the hinted lift's selection
  rule and uniformity are theorems about the main package's programs.
* **H-GROUP is now proved for the Edwards formulas** (section 7): the points of
  `−x² + y² = 1 + d·x²·y²` over `ZMod p` with the unified addition law are a commutative group
  (completeness from "`d` is not a square, `−1` is"; associativity by the polynomial identity
  modulo the curve equations); `pointAddValue`, `extAddValue`, `negate`, `curveCheck`,
  `sumTreeValue`, `extSumValue` compute in that group; the base point has order exactly `ℓ`
  (`ℓ·B = 0` by kernel arithmetic, `ℓ` prime), so the subgroup it generates is a finite
  commutative group of order `ℓ` and the statements of sections 3–3c hold for it without a group
  hypothesis; the X25519 ladder computes scalar multiplication in the same group, for every
  coordinate of a curve point including `u = 0` (section 7c), with the clamped scalar in closed
  form; the scalar-multiple chains (`windowValue`, `doublingsValue`, the signed recoding of
  `offsetSum`, `bitSum`, `prepareHinted`'s initial point, XEdDSA's `doubleScalar`) are scalar
  multiples (section 7d); `liftPoint`'s map `x = √(−486664)·u/v` lands on the curve with
  Montgomery coordinate `u`, and `u(u² + 486662u + 1)` is a square exactly for those `u`
  (section 7e). The generic statements (sections 3–3c) keep their form "for any finite
  commutative group `G`"; section 7b instantiates them. **Still not proved:** the group order
  `#E = 8ℓ` (so: that every point killed by `ℓ` is a multiple of `B`, and what
  `edwards-torsion-hinted` assumes about `8Q = P`); X25519 for `u` on the quadratic twist.
* **idealCommit stays a hypothesis** (a cryptographic assumption). The distributional statements
  of section 3 assume, as their model, that the other party's value does not depend on the honest
  party's mask (that is what `idealCommit` provides in the protocols).
* **The cut-and-choose bound** (section 4) is proved exactly for every number of bad buckets
  `t`; `bound(t) ≤ bound(1)` for every `1 ≤ t ≤ N` and every `B ≥ 2` (so `t = 1` is the worst
  case, for all parameters, not only the deployed ones); `bound(1) < 2⁻¹²⁸` for the four
  deployed profiles; hence every bad set goes undetected with probability `< 2⁻¹²⁸` there. The
  detection rules P-CUT(d), (e) remain the model's assumptions.
* **XEdDSA `recover`** (section 2b): `X25519.powBits` is proved to be the field power, and the
  square-root correctness of `recipient` is proved for `recover` too.
* **The offset agreement's public key** (section 3b): independent of the initial scalar as a
  probability statement, with scalars in `ZMod ℓ` for any finite commutative group of order `ℓ`
  (H-GROUP as that hypothesis); uniform on `G` when `ℓ` is prime and `B ≠ 0`.
* **The deployed offset sampling** (section 3c): the offset `(mine XOR peer) mod 2²⁵²` is exactly
  uniform on `[0, 2²⁵²)` for the honest party's uniform `mine` and any (independent) peer value;
  the published keys for any two initial scalars are within `(ℓ − 2²⁵²)/2²⁵² < 2⁻¹²⁷` (every
  event), and within `(ℓ − 2²⁵²)/ℓ` of uniform on `G`; `k` messages: the joint keys within
  `k·2⁻¹²⁷`, and with offsets uniform mod `ℓ` exactly independent of the initial scalar (uniform
  on `G^k`). The Ed25519 group order `ℓ` is proved prime (section 1).
* **`Unpad.decode` is PKCS#7 unpadding** (section 6). `varintValue` and `canonicalRange` are not
  stated: they live in `TlsMpc.Signal.ReceiveFirst`, whose imports (52 modules) are not compiled
  into this package.
-/

namespace TlsMpcProofs.Security
open TlsMpc

/-! ## 1. The field and its modulus -/

/-- **p = 2²⁵⁵ − 19 (the main package's `FieldDag.modulus`) is prime.** By a Pocklington
certificate chain (p ← a 236-bit prime Q ← a 55-bit prime ← small primes), its modular
arithmetic checked by the kernel's GMP-accelerated `Nat` operations (`decide +kernel`, no
`native_decide`). **gen** (used by every entry below). -/
theorem prime_modulus : Nat.Prime FieldDag.modulus :=
  TlsMpcProofs.prime_modulus

/-- **The Ed25519 group order `ℓ = 2²⁵² + 27742317777372353535851937790883648493` (the main
package's `Signal.XEdDsaScalar.order`) is prime.** Pocklington chain: `ℓ` ← a 138-bit prime ←
134-bit ← 88-bit ← 62-bit ← 51-bit ← primes below 2·10⁶. **gen** (used by
`ed25519_key_close_uniform`). -/
theorem prime_order : Nat.Prime Signal.XEdDsaScalar.order :=
  TlsMpcProofs.OffsetSampling.prime_order

/-- **Pocklington's criterion** (proved here from Mathlib's `orderOf`/`ZMod`): a checked
certificate whose listed factors are prime proves `N` prime. **gen**. -/
theorem pocklington (N : ℕ) (cert : List (ℕ × ℕ × ℕ)) (hok : TlsMpcProofs.certOk N cert = true)
    (hp : ∀ c ∈ cert, c.1.Prime) : N.Prime :=
  TlsMpcProofs.pocklington N cert hok hp

/-- **The main package's constants are `ZMod p` constants:** `ofNat n ↦ n mod p` under the ring
isomorphism `toZMod : F ≃+* ZMod p` (`ZMod.finEquiv`). **gen** (the bridge). -/
theorem toZMod_ofNat (n : ℕ) : TlsMpcProofs.toZMod (FieldDag.ofNat n) = (n : ZMod FieldDag.modulus) :=
  TlsMpcProofs.toZMod_ofNat n

/-- **The main package's `power` is the `ZMod p` power.** **gen**. -/
theorem toZMod_power (x : FieldDag.F) (n : ℕ) :
    TlsMpcProofs.toZMod (FieldDag.power x n) = TlsMpcProofs.toZMod x ^ n :=
  TlsMpcProofs.toZMod_power x n

/-- **The main package's `inverse` (`x^(p−2)`) is the `ZMod p` inverse** (zero at zero). **gen**. -/
theorem toZMod_inverse (x : FieldDag.F) :
    TlsMpcProofs.toZMod (FieldDag.inverse x) = (TlsMpcProofs.toZMod x)⁻¹ :=
  TlsMpcProofs.toZMod_inverse x

/-! ## 2. H-QR -/

/-- **2 is not a square mod p** (p ≡ 5 mod 8). **gen** (H-QR, used by the hinted lift). -/
theorem two_not_square : ¬ ∃ r : FieldDag.F, r * r = FieldDag.ofNat 2 :=
  TlsMpcProofs.two_not_square

/-- **Euler's criterion for p**, with the main package's `power`: a nonzero `x` is a square iff
`x^((p−1)/2) = 1`. **gen** (H-QR). -/
theorem euler_criterion (x : FieldDag.F) (hx : x ≠ FieldDag.ofNat 0) :
    (∃ r : FieldDag.F, r * r = x) ↔ FieldDag.power x ((FieldDag.modulus - 1) / 2) = FieldDag.ofNat 1 :=
  TlsMpcProofs.euler_criterion x hx

/-- **A nonzero non-square has `x^((p−1)/2) = −1`.** **gen** (H-QR). -/
theorem euler_nonsquare (x : FieldDag.F) (hx : x ≠ FieldDag.ofNat 0) (hn : ¬ ∃ r : FieldDag.F, r * r = x) :
    FieldDag.power x ((FieldDag.modulus - 1) / 2) = FieldDag.ofNat 0 - FieldDag.ofNat 1 :=
  TlsMpcProofs.euler_nonsquare x hx hn

/-- **The constant `sqrtMinusOne` (also `XEdDsaField.sqrtM1`) is `2^((p−1)/4)`.** **K-fn**
(constant of `edwards-prepare` and `xeddsa-recover`). -/
theorem sqrtMinusOne_eq_power :
    FieldDag.ofNat EdwardsAffine.sqrtMinusOne =
      FieldDag.power (FieldDag.ofNat 2) ((FieldDag.modulus - 1) / 4) :=
  TlsMpcProofs.sqrtMinusOne_eq_power

/-- **`sqrtMinusOne² = −1` in F.** **K-fn**. -/
theorem sqrtMinusOne_mul_self :
    FieldDag.ofNat EdwardsAffine.sqrtMinusOne * FieldDag.ofNat EdwardsAffine.sqrtMinusOne =
      FieldDag.ofNat 0 - FieldDag.ofNat 1 :=
  TlsMpcProofs.sqrtMinusOne_mul_self

/-- **The p ≡ 5 (mod 8) candidate:** `c = x^((p+3)/8)` has `c⁴ = x²` exactly when `x` is a
square. **gen** (H-QR). -/
theorem candidate_fourth_iff (X : ZMod FieldDag.modulus) :
    (X ^ ((FieldDag.modulus + 3) / 8)) ^ 4 = X ^ 2 ↔ IsSquare X :=
  TlsMpcProofs.candidate_fourth_iff X

/-- **For a square `x`, the candidate squares to `x` or `−x`.** **gen** (H-QR). -/
theorem candidate_sq (X : ZMod FieldDag.modulus) (hX : IsSquare X) :
    (X ^ ((FieldDag.modulus + 3) / 8)) ^ 2 = X ∨ (X ^ ((FieldDag.modulus + 3) / 8)) ^ 2 = -X :=
  TlsMpcProofs.candidate_sq X hX

/-- **`recipient`'s check value is zero exactly when its `x²` is a square.** **K-fn**
(`recipient` is part of `edwards-prepare`, the non-hinted offset agreement; the composition with
`prepare`'s other outputs is not stated). That a zero check gives a point of the curve group is
`recipient_on_curve` (section 7). -/
theorem recipient_check_zero_iff (u : FieldDag.Expr) (input : ℕ → FieldDag.F) :
    (EdwardsAffine.recipient u).2.eval input = FieldDag.ofNat 0 ↔
      ∃ r : FieldDag.F, r * r = TlsMpcProofs.recXX (u.eval input) :=
  TlsMpcProofs.recipient_check_zero_iff u input

/-- **When the check passes, `recipient`'s `x` is a square root of its `x²`** (the root is `c`
if `c² = x²`, else `c·√−1`; the sign is not normalised, as the docstring of `recipient` says).
**K-fn**. -/
theorem recipient_x_mul_self (u : FieldDag.Expr) (input : ℕ → FieldDag.F)
    (h : (EdwardsAffine.recipient u).2.eval input = FieldDag.ofNat 0) :
    (EdwardsAffine.recipient u).1.1.eval input * (EdwardsAffine.recipient u).1.1.eval input =
      TlsMpcProofs.recXX (u.eval input) :=
  TlsMpcProofs.recipient_x_mul_self u input h

/-- **The lift's selection rule:** for `q, r ≠ 0`, `w = q·r²·(1 + b)` is a square iff
(`q` is a square iff `b = 0`); so validity is `sel xor b` for the public `sel`. **gen**
(P-HINT(b), H-QR). -/
theorem lift_select (q r : FieldDag.F) (bit : Bool) (hq : q ≠ FieldDag.ofNat 0) (hr : r ≠ FieldDag.ofNat 0) :
    (∃ s : FieldDag.F, s * s = q * r * r * (FieldDag.ofNat 1 + X25519.bitValue bit)) ↔
      ((∃ s : FieldDag.F, s * s = q) ↔ bit = false) :=
  TlsMpcProofs.lift_select q r bit hq hr

/-- **The same for the program:** `liftOpen`'s opened `w` (its first output, via
`EdwardsHinted.liftOpen_eval`), with the parties' bits `a`, `a'`, is a square iff
(`q = u·(u² + 486662u + 1)` is a square iff `a xor a' = 0`). **switch**. -/
theorem liftOpen_square_iff (input : ℕ → FieldDag.F) (a a' : Bool)
    (h2 : input 2 = X25519.bitValue a) (h3 : input 3 = X25519.bitValue a')
    (hq : input 0 * (input 0 * input 0 + FieldDag.ofNat 486662 * input 0 + FieldDag.ofNat 1) ≠ FieldDag.ofNat 0)
    (hr : input 1 ≠ FieldDag.ofNat 0) :
    (∃ s : FieldDag.F, s * s = ((EdwardsHinted.liftOpen ()).map (FieldDag.Expr.eval input)).headD (FieldDag.ofNat 0)) ↔
      ((∃ s : FieldDag.F, s * s = input 0 * (input 0 * input 0 + FieldDag.ofNat 486662 * input 0 + FieldDag.ofNat 1)) ↔
        (a ^^ a') = false) :=
  TlsMpcProofs.liftOpen_square_iff input a a' h2 h3 hq hr

/-- **Every value has exactly two preimages `(r, b)` under `q·r²·(1 + b)`** (`q ≠ 0`). **gen**
(P-HINT(b); the plan's "4 pairs" counts `(r, b_A, b_B)`). -/
theorem lift_fiber_card (q w : FieldDag.F) (hq : q ≠ FieldDag.ofNat 0) :
    (Finset.univ.filter (fun rb : FieldDag.F × Bool =>
      q * rb.1 * rb.1 * (FieldDag.ofNat 1 + X25519.bitValue rb.2) = w)).card = 2 :=
  TlsMpcProofs.lift_fiber_card q w hq

/-- **The lift's opened value is uniform on F** for `q ≠ 0`, a uniform mask `r` and a uniform
bit — so it reveals nothing about `u` beyond `q ≠ 0`. **switch** (P-HINT(b) as probability). -/
theorem lift_opened_uniform (q : FieldDag.F) (hq : q ≠ FieldDag.ofNat 0) :
    PMF.map (fun rb : FieldDag.F × Bool => q * rb.1 * rb.1 * (FieldDag.ofNat 1 + X25519.bitValue rb.2))
      (PMF.uniformOfFintype (FieldDag.F × Bool)) = PMF.uniformOfFintype FieldDag.F :=
  TlsMpcProofs.lift_opened_uniform q hq

/-- **The same with `b = a xor a'`**: uniform whatever bit `a'` the other party contributes.
**switch**. -/
theorem lift_opened_uniform_xor (q : FieldDag.F) (hq : q ≠ FieldDag.ofNat 0) (a' : Bool) :
    PMF.map (fun ra : FieldDag.F × Bool => q * ra.1 * ra.1 * (FieldDag.ofNat 1 + X25519.bitValue (ra.2 ^^ a')))
      (PMF.uniformOfFintype (FieldDag.F × Bool)) = PMF.uniformOfFintype FieldDag.F :=
  TlsMpcProofs.lift_opened_uniform_xor q hq a'

/-! ## 2b. XEdDSA `recover` (H-QR through `X25519.powBits`) -/

/-- **`X25519.powBits` on the concrete field is the power:** `powBits x acc bits =
acc^(2^|bits|) · x^(big-endian value of bits)`. **gen** (every exponentiation of the
`X25519`-based field programs). -/
theorem powBits_value (x acc : FieldDag.F) (bits : List Bool) :
    TlsMpcProofs.toZMod (X25519.powBits X25519.concrete x acc bits) =
      TlsMpcProofs.toZMod acc ^ (2 ^ bits.length) * TlsMpcProofs.toZMod x ^ TlsMpcProofs.bitsValue 0 bits :=
  TlsMpcProofs.toZMod_powBits x acc bits

/-- **`XEdDsaField.exponent x n = x^n`** for `n < 2²⁵⁵`. **K-fn** (`xeddsa-recover`). -/
theorem xeddsa_exponent_eq_power (x : FieldDag.F) (n : ℕ) (hn : n < 2 ^ 255) :
    Signal.XEdDsaField.exponent X25519.concrete x n = FieldDag.power x n :=
  TlsMpcProofs.exponent_eq_power x n hn

/-- **`X25519.inverse` (concrete) is `FieldDag.inverse`.** **gen**. -/
theorem x25519_inverse_eq (x : FieldDag.F) : X25519.inverse X25519.concrete x = FieldDag.inverse x :=
  TlsMpcProofs.x25519_inverse_eq x

/-- **`XEdDsaField.zero x` is the indicator of `x = 0`.** **K-fn**. -/
theorem xeddsa_zero_eq_ite (x : FieldDag.F) :
    Signal.XEdDsaField.zero X25519.concrete x = if x = FieldDag.ofNat 0 then FieldDag.ofNat 1 else FieldDag.ofNat 0 :=
  TlsMpcProofs.zero_eq_ite x

/-- **What `recover` computes:** `[valid, x, y]` with `y = (u−1)/(u+1)`, `xx = (y²−1)/(d·y²+1)`,
`x = c` or `c·√−1` for `c = xx^((p+3)/8)`, `valid` the product of the three indicators.
**K-fn** (`xeddsa-recover`; `XEdDsaField.compiled_output_correct` links the artifact to
`run X25519.concrete true`, which is `recover` of input 0, `run_recovery_eq`). -/
theorem xeddsa_recover_eq (U : FieldDag.F) :
    Signal.XEdDsaField.recover X25519.concrete U =
      [TlsMpcProofs.xedValid U, TlsMpcProofs.xedX U, TlsMpcProofs.xedY U] :=
  TlsMpcProofs.recover_eq U

/-- **The `xeddsa-recover` program is `recover` of input 0.** **K-fn**. -/
theorem xeddsa_run_recovery_eq (input : ℕ → FieldDag.F) :
    Signal.XEdDsaField.run X25519.concrete true input = Signal.XEdDsaField.recover X25519.concrete (input 0) :=
  TlsMpcProofs.run_recovery_eq input

/-- **`recover`'s validity output is `0` or `1`.** **K-fn**. -/
theorem xeddsa_recover_valid_zero_or_one (U valid x y : FieldDag.F)
    (h : Signal.XEdDsaField.recover X25519.concrete U = [valid, x, y]) :
    valid = FieldDag.ofNat 1 ∨ valid = FieldDag.ofNat 0 :=
  TlsMpcProofs.recover_valid_zero_or_one U valid x y h

/-- **`valid = 1` exactly when `u + 1 ≠ 0`, `v = d·y² + 1 ≠ 0` and `xx` is a square.** **K-fn**
(H-QR; that `valid = 1` gives a point of the curve group is `xeddsa_recover_on_curve`,
section 7). -/
theorem xeddsa_recover_valid_iff (U valid x y : FieldDag.F)
    (h : Signal.XEdDsaField.recover X25519.concrete U = [valid, x, y]) :
    valid = FieldDag.ofNat 1 ↔
      U + FieldDag.ofNat 1 ≠ FieldDag.ofNat 0 ∧ TlsMpcProofs.xedV U ≠ FieldDag.ofNat 0 ∧
        ∃ r : FieldDag.F, r * r = TlsMpcProofs.xedXX U :=
  TlsMpcProofs.recover_valid_iff U valid x y h

/-- **Whenever `xx` is a square, `recover`'s `x` is a square root of it** (sign not
normalised). **K-fn**. -/
theorem xeddsa_recover_x_mul_self (U valid x y : FieldDag.F)
    (h : Signal.XEdDsaField.recover X25519.concrete U = [valid, x, y])
    (hsq : ∃ r : FieldDag.F, r * r = TlsMpcProofs.xedXX U) : x * x = TlsMpcProofs.xedXX U :=
  TlsMpcProofs.recover_x_mul_self U valid x y h hsq

/-- **When `valid = 1`, `x·x = xx`.** **K-fn**. -/
theorem xeddsa_recover_x_mul_self_of_valid (U valid x y : FieldDag.F)
    (h : Signal.XEdDsaField.recover X25519.concrete U = [valid, x, y]) (hv : valid = FieldDag.ofNat 1) :
    x * x = TlsMpcProofs.xedXX U :=
  TlsMpcProofs.recover_x_mul_self_of_valid U valid x y h hv

/-- **`recover`'s `y` is `(u − 1)/(u + 1)`.** **K-fn**. -/
theorem xeddsa_recover_y (U valid x y : FieldDag.F)
    (h : Signal.XEdDsaField.recover X25519.concrete U = [valid, x, y]) : y = TlsMpcProofs.xedY U :=
  TlsMpcProofs.recover_y U valid x y h

/-! ## 3. Hiding as probability (plan section 7.0; Security.lean section 8) -/

/-- **A family of bijections on the randomness gives equal output distributions.** If
`view s r = view s' (σ r)` for a bijection `σ`, then with `r` uniform the view has the same
distribution under `s` and `s'`. **gen** (turns each bijection-form theorem into its
distributional form). -/
theorem hiding_of_bijection {S R V : Type} [Fintype R] [Nonempty R] (view : S → R → V)
    (s s' : S) (σ : R ≃ R) (h : ∀ r, view s r = view s' (σ r)) :
    PMF.map (view s) (PMF.uniformOfFintype R) = PMF.map (view s') (PMF.uniformOfFintype R) :=
  TlsMpcProofs.hiding_of_bijection view s s' σ h

/-- **A bijection carries the uniform distribution to the uniform distribution.** **gen**. -/
theorem map_uniform_equiv {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (e : α ≃ β) :
    PMF.map e (PMF.uniformOfFintype α) = PMF.uniformOfFintype β :=
  TlsMpcProofs.map_uniform_equiv e

/-- **`ghash_share_hides` as probability:** the masked key power B sees has the same
distribution for any two key powers (from `GhashShares.share_views_equal`). **M** (P-GHASH(d)). -/
theorem ghash_share_hides_dist (key other : GhashShares.W) :
    PMF.map (fun mask => key ^^^ mask) (PMF.uniformOfFintype GhashShares.W) =
      PMF.map (fun mask => other ^^^ mask) (PMF.uniformOfFintype GhashShares.W) :=
  TlsMpcProofs.ghash_share_hides_dist key other

/-- **… and it is uniform on 128-bit words.** **M**. -/
theorem ghash_share_uniform (key : GhashShares.W) :
    PMF.map (fun mask => key ^^^ mask) (PMF.uniformOfFintype GhashShares.W) =
      PMF.uniformOfFintype GhashShares.W :=
  TlsMpcProofs.ghash_share_uniform key

/-- **`ceremony_masked_hides` as probability:** `word ⊕ (other ⊕ m)` is uniform for a uniform
mask byte. Same expression, not linked by import (see the README). **ceremony**. -/
theorem ceremony_masked_uniform (word other : BitVec 8) :
    PMF.map (fun m => word ^^^ (other ^^^ m)) (PMF.uniformOfFintype (BitVec 8)) =
      PMF.uniformOfFintype (BitVec 8) :=
  TlsMpcProofs.ceremony_masked_uniform word other

/-- **P-RAND(b) as probability:** `r ⊕ v` is uniform for uniform `r`, whatever `v`. **M**
(the C++ joint randomness; `idealCommit` gives "v does not depend on r"). -/
theorem joint_random_uniform {n : ℕ} (v : BitVec n) :
    PMF.map (fun r => r ^^^ v) (PMF.uniformOfFintype (BitVec n)) = PMF.uniformOfFintype (BitVec n) :=
  TlsMpcProofs.joint_random_uniform v

/-- **P-B2F(b) as probability:** the opened bit `x ⊕ ρ` is uniform. **M**. -/
theorem bit_open_uniform (x : Bool) :
    PMF.map (fun ρ => x ^^ ρ) (PMF.uniformOfFintype Bool) = PMF.uniformOfFintype Bool :=
  TlsMpcProofs.bit_open_uniform x

/-- **P-W2F(b) as probability:** the opened `(u mod p + r) mod p` (the `into-field` circuit's
output) has the same distribution as a uniform field element, whatever `u`. **M**. -/
theorem word_to_field_open_uniform (u : ℕ) :
    PMF.map (fun r : FieldDag.F => (u % WordMask.P + r.val) % WordMask.P) (PMF.uniformOfFintype FieldDag.F) =
      PMF.map (fun r : FieldDag.F => r.val) (PMF.uniformOfFintype FieldDag.F) :=
  TlsMpcProofs.word_to_field_open_uniform u

/-- **P-F2W(b) as probability:** the opened `v − f` is uniform. **M**. -/
theorem field_to_word_open_uniform (v : FieldDag.F) :
    PMF.map (fun f : FieldDag.F => v - f) (PMF.uniformOfFintype FieldDag.F) = PMF.uniformOfFintype FieldDag.F :=
  TlsMpcProofs.field_to_word_open_uniform v

/-- **P-INV(c) as probability:** for `b ≠ 0`, the opened `b·m` is uniform. **M**. -/
theorem masked_inverse_open_uniform (b : FieldDag.F) (hb : b ≠ FieldDag.ofNat 0) :
    PMF.map (fun m : FieldDag.F => b * m) (PMF.uniformOfFintype FieldDag.F) = PMF.uniformOfFintype FieldDag.F :=
  TlsMpcProofs.masked_inverse_open_uniform b hb

/-- **`maskedAgreement_mask_hides` as probability**, for any finite commutative group (H-GROUP
for the curve): the opened `R + maskA + maskB` has the same distribution for any two `R`. **M**. -/
theorem maskedAgreement_mask_hides_dist {G : Type} [AddCommGroup G] [Fintype G] [Nonempty G]
    (R other maskA : G) :
    PMF.map (fun maskB => MaskedAgreement.opened R maskA maskB) (PMF.uniformOfFintype G) =
      PMF.map (fun maskB => MaskedAgreement.opened other maskA maskB) (PMF.uniformOfFintype G) :=
  TlsMpcProofs.maskedAgreement_mask_hides_dist R other maskA

/-- **P-HINT(c) as probability** (H-GROUP as "a finite commutative group"): `Z = P + M_A + M_B`
is uniform for the honest party's uniform `M_B`. **M**. -/
theorem hinted_Z_uniform {G : Type} [AddCommGroup G] [Fintype G] [Nonempty G] (P maskA : G) :
    PMF.map (fun maskB => MaskedAgreement.opened P maskA maskB) (PMF.uniformOfFintype G) =
      PMF.uniformOfFintype G :=
  TlsMpcProofs.hinted_Z_uniform P maskA

/-! ## 3b. The offset agreement's public key as probability -/

open TlsMpcProofs.OffsetAgreement in
/-- **`offsetAgreement_public_key_independent` as probability** (H-GROUP as the hypothesis "`G`
is a finite commutative group of order `ℓ`"): with the offset uniform in `ZMod ℓ`, the published
key `initial·B + offset·B` has the same distribution for any two initial scalars. **M**
(the deployed offset is drawn from `[0, 2²⁵²)`, not uniformly mod `ℓ`: section 3c). -/
theorem offset_public_key_independent {G : Type} [AddCommGroup G] [Fintype G] {ℓ : ℕ} [NeZero ℓ]
    (hℓ : Fintype.card G = ℓ) (B : G) (initial other : ZMod ℓ) :
    PMF.map (publicKey B initial) (PMF.uniformOfFintype (ZMod ℓ)) =
      PMF.map (publicKey B other) (PMF.uniformOfFintype (ZMod ℓ)) :=
  TlsMpcProofs.OffsetAgreement.offset_public_key_independent hℓ B initial other

open TlsMpcProofs.OffsetAgreement in
/-- **The published key is uniform on `G`** when `|G| = ℓ` is prime and `B ≠ 0`. **M**. -/
theorem offset_public_key_uniform {G : Type} [AddCommGroup G] [Fintype G] {ℓ : ℕ} [NeZero ℓ]
    [Fact ℓ.Prime] (hℓ : Fintype.card G = ℓ) (B : G) (hB : B ≠ 0) (initial : ZMod ℓ) :
    PMF.map (publicKey B initial) (PMF.uniformOfFintype (ZMod ℓ)) = PMF.uniformOfFintype G :=
  TlsMpcProofs.OffsetAgreement.offset_public_key_uniform hℓ B hB initial

open TlsMpcProofs.OffsetAgreement TlsMpcProofs.OffsetSampling in
/-- **Several messages, offsets uniform mod `ℓ`:** the joint distribution of the `k` keys of one
conversation is the same for any two initial scalars. **M**. -/
theorem offset_public_keys_independent {G : Type} [AddCommGroup G] [Fintype G] {ℓ k : ℕ} [NeZero ℓ]
    (hℓ : Fintype.card G = ℓ) (B : G) (initial other : ZMod ℓ) :
    PMF.map (publicKeys (k := k) B initial) (PMF.uniformOfFintype (Fin k → ZMod ℓ)) =
      PMF.map (publicKeys B other) (PMF.uniformOfFintype (Fin k → ZMod ℓ)) :=
  TlsMpcProofs.OffsetSampling.offset_public_keys_independent hℓ B initial other

open TlsMpcProofs.OffsetAgreement TlsMpcProofs.OffsetSampling in
/-- **… uniform on `G^k`** (`ℓ` prime, `B ≠ 0`): `k` independent uniform keys, so independent of
the initial scalar and of each other. **M**. -/
theorem offset_public_keys_uniform {G : Type} [AddCommGroup G] [Fintype G] {ℓ k : ℕ} [NeZero ℓ]
    [Fact ℓ.Prime] (hℓ : Fintype.card G = ℓ) (B : G) (hB : B ≠ 0) (initial : ZMod ℓ) :
    PMF.map (publicKeys (k := k) B initial) (PMF.uniformOfFintype (Fin k → ZMod ℓ)) =
      PMF.uniformOfFintype (Fin k → G) :=
  TlsMpcProofs.OffsetSampling.offset_public_keys_uniform hℓ B hB initial

/-! ## 3c. The deployed offset sampling (`[0, 2²⁵²)`, `mine XOR peer`)

`EventClose p q δ`: every event's probability under `p` is at most its probability under `q` plus
`δ`; `StatClose`: both directions (total variation `≤ δ`). The peer's value is fixed (independent
of the honest party's `mine`: `idealCommit`). -/

open TlsMpcProofs.OffsetSampling in
/-- **Two injections of a uniform `R` into `Z` give `(|Z| − |R|)/|R|`-close distributions.**
**gen**. -/
theorem eventClose_injective {R Z : Type} [Fintype R] [Nonempty R] [Fintype Z] (e1 e2 : R → Z)
    (h1 : Function.Injective e1) (h2 : Function.Injective e2) :
    EventClose (PMF.map e1 (PMF.uniformOfFintype R)) (PMF.map e2 (PMF.uniformOfFintype R))
      (((Fintype.card Z - Fintype.card R : ℕ) : ENNReal) / Fintype.card R) :=
  TlsMpcProofs.OffsetSampling.eventClose_injective e1 e2 h1 h2

open TlsMpcProofs.OffsetSampling in
/-- **An injection of a uniform `R` into `Z` is `(|Z| − |R|)/|Z|`-close to uniform on `Z`** (total
variation). **gen**. -/
theorem statClose_uniform {R Z : Type} [Fintype R] [Nonempty R] [Fintype Z] [Nonempty Z]
    (e : R → Z) (he : Function.Injective e) :
    StatClose (PMF.map e (PMF.uniformOfFintype R)) (PMF.uniformOfFintype Z)
      (((Fintype.card Z - Fintype.card R : ℕ) : ENNReal) / Fintype.card Z) :=
  TlsMpcProofs.OffsetSampling.statClose_uniform e he

open TlsMpcProofs.OffsetSampling in
/-- **The deployed offset `(mine XOR peer) mod 2²⁵²` is exactly uniform on `[0, 2²⁵²)`**
(`service_kernels.h` `seal_open`/`ephemeral`, `offset[31] &= 15` in `edwards_points.h`). **M**. -/
theorem deployedOffset_uniform (peer : BitVec 256) :
    PMF.map (fun mine => deployedOffset mine peer) (PMF.uniformOfFintype (BitVec 256)) =
      PMF.uniformOfFintype (Fin (2 ^ 252)) :=
  TlsMpcProofs.OffsetSampling.deployedOffset_uniform peer

open TlsMpcProofs.OffsetSampling in
/-- **The deployed offset modulo `ℓ` is `(ℓ − 2²⁵²)/ℓ`-close to uniform in `ZMod ℓ`** (any
`ℓ ≥ 2²⁵²`). **M**. -/
theorem offset_cast_close_uniform {ℓ : ℕ} [NeZero ℓ] (hN : 2 ^ 252 ≤ ℓ) (peer : BitVec 256) :
    StatClose (PMF.map (fun mine => castOffset ℓ (deployedOffset mine peer)) (PMF.uniformOfFintype (BitVec 256)))
      (PMF.uniformOfFintype (ZMod ℓ)) (((ℓ - 2 ^ 252 : ℕ) : ENNReal) / (ℓ : ENNReal)) :=
  TlsMpcProofs.OffsetSampling.offset_cast_close_uniform hN peer

open TlsMpcProofs.OffsetSampling in
/-- **Deployed sampling, one message, any two initial scalars:** every event's probability differs
by at most `(ℓ − 2²⁵²)/2²⁵²` (any `ℓ ≥ 2²⁵²`, any finite commutative group of order `ℓ`). **M**. -/
theorem deployed_key_close {G : Type} [AddCommGroup G] [Fintype G] {ℓ : ℕ} [NeZero ℓ]
    (hℓ : Fintype.card G = ℓ) (hN : 2 ^ 252 ≤ ℓ) (B : G) (peer : BitVec 256) (initial other : ZMod ℓ) :
    EventClose
      (PMF.map (fun mine => deployedKey B initial (deployedOffset mine peer)) (PMF.uniformOfFintype (BitVec 256)))
      (PMF.map (fun mine => deployedKey B other (deployedOffset mine peer)) (PMF.uniformOfFintype (BitVec 256)))
      (((ℓ - 2 ^ 252 : ℕ) : ENNReal) / ((2 ^ 252 : ℕ) : ENNReal)) :=
  TlsMpcProofs.OffsetSampling.deployed_key_close hℓ hN B peer initial other

open TlsMpcProofs.OffsetAgreement TlsMpcProofs.OffsetSampling in
/-- **The deployed key is `(ℓ − 2²⁵²)/ℓ`-close to the key with a uniform offset.** **M**. -/
theorem deployed_key_close_ideal {G : Type} [AddCommGroup G] [Fintype G] {ℓ : ℕ} [NeZero ℓ]
    (hℓ : Fintype.card G = ℓ) (hN : 2 ^ 252 ≤ ℓ) (B : G) (peer : BitVec 256) (initial : ZMod ℓ) :
    StatClose
      (PMF.map (fun mine => deployedKey B initial (deployedOffset mine peer)) (PMF.uniformOfFintype (BitVec 256)))
      (PMF.map (publicKey B initial) (PMF.uniformOfFintype (ZMod ℓ)))
      (((ℓ - 2 ^ 252 : ℕ) : ENNReal) / (ℓ : ENNReal)) :=
  TlsMpcProofs.OffsetSampling.deployed_key_close_ideal hℓ hN B peer initial

open TlsMpcProofs.OffsetSampling in
/-- **`ℓ` prime, `B ≠ 0`: the deployed key is `(ℓ − 2²⁵²)/ℓ`-close to uniform on `G`.** **M**. -/
theorem deployed_key_close_uniform {G : Type} [AddCommGroup G] [Fintype G] {ℓ : ℕ} [NeZero ℓ]
    [Fact ℓ.Prime] (hℓ : Fintype.card G = ℓ) (hN : 2 ^ 252 ≤ ℓ) (B : G) (hB : B ≠ 0)
    (peer : BitVec 256) (initial : ZMod ℓ) :
    StatClose
      (PMF.map (fun mine => deployedKey B initial (deployedOffset mine peer)) (PMF.uniformOfFintype (BitVec 256)))
      (PMF.uniformOfFintype G) (((ℓ - 2 ^ 252 : ℕ) : ENNReal) / (ℓ : ENNReal)) :=
  TlsMpcProofs.OffsetSampling.deployed_key_close_uniform hℓ hN B hB peer initial

open TlsMpcProofs.OffsetSampling in
/-- **Deployed sampling, `k` messages:** the joint keys for any two initial scalars, every event
within `k·(ℓ − 2²⁵²)/2²⁵²` (fixed peer values). **M**. -/
theorem deployed_keys_close {G : Type} [AddCommGroup G] [Fintype G] {ℓ k : ℕ} [NeZero ℓ]
    (hℓ : Fintype.card G = ℓ) (hN : 2 ^ 252 ≤ ℓ) (B : G) (peers : Fin k → BitVec 256)
    (initial other : ZMod ℓ) :
    EventClose
      (PMF.map (fun mines => deployedKeys B initial (deployedOffsets peers mines))
        (PMF.uniformOfFintype (Fin k → BitVec 256)))
      (PMF.map (fun mines => deployedKeys B other (deployedOffsets peers mines))
        (PMF.uniformOfFintype (Fin k → BitVec 256)))
      (k * (((ℓ - 2 ^ 252 : ℕ) : ENNReal) / ((2 ^ 252 : ℕ) : ENNReal))) :=
  TlsMpcProofs.OffsetSampling.deployed_keys_close hℓ hN B peers initial other

/-- **`(ℓ − 2²⁵²)/2²⁵² < 2⁻¹²⁷`** for the Ed25519 order (`ℓ − 2²⁵² ≈ 2^124.4`). **gen**. -/
theorem order_gap_lt :
    ((Signal.XEdDsaScalar.order - 2 ^ 252 : ℕ) : ENNReal) / ((2 ^ 252 : ℕ) : ENNReal) <
      1 / ((2 ^ 127 : ℕ) : ENNReal) :=
  TlsMpcProofs.OffsetSampling.order_gap_lt

open TlsMpcProofs.OffsetSampling in
/-- **Ed25519, one message:** any two initial scalars, every event within `2⁻¹²⁷`. **M**. -/
theorem ed25519_key_close {G : Type} [AddCommGroup G] [Fintype G]
    (hℓ : Fintype.card G = Signal.XEdDsaScalar.order) (B : G) (peer : BitVec 256)
    (initial other : ZMod Signal.XEdDsaScalar.order) :
    EventClose
      (PMF.map (fun mine => deployedKey B initial (deployedOffset mine peer)) (PMF.uniformOfFintype (BitVec 256)))
      (PMF.map (fun mine => deployedKey B other (deployedOffset mine peer)) (PMF.uniformOfFintype (BitVec 256)))
      (1 / ((2 ^ 127 : ℕ) : ENNReal)) :=
  TlsMpcProofs.OffsetSampling.ed25519_key_close hℓ B peer initial other

open TlsMpcProofs.OffsetSampling in
/-- **Ed25519, one message: the deployed key is within `2⁻¹²⁷` of uniform on `G`** (`B ≠ 0`;
`ℓ` prime is proved). **M**. -/
theorem ed25519_key_close_uniform {G : Type} [AddCommGroup G] [Fintype G]
    (hℓ : Fintype.card G = Signal.XEdDsaScalar.order) (B : G) (hB : B ≠ 0) (peer : BitVec 256)
    (initial : ZMod Signal.XEdDsaScalar.order) :
    StatClose
      (PMF.map (fun mine => deployedKey B initial (deployedOffset mine peer)) (PMF.uniformOfFintype (BitVec 256)))
      (PMF.uniformOfFintype G) (1 / ((2 ^ 127 : ℕ) : ENNReal)) :=
  TlsMpcProofs.OffsetSampling.ed25519_key_close_uniform hℓ B hB peer initial

open TlsMpcProofs.OffsetSampling in
/-- **Ed25519, `k` messages:** the joint keys, any two initial scalars, every event within
`k·2⁻¹²⁷`. **M**. -/
theorem ed25519_keys_close {G : Type} [AddCommGroup G] [Fintype G] {k : ℕ}
    (hℓ : Fintype.card G = Signal.XEdDsaScalar.order) (B : G) (peers : Fin k → BitVec 256)
    (initial other : ZMod Signal.XEdDsaScalar.order) :
    EventClose
      (PMF.map (fun mines => deployedKeys B initial (deployedOffsets peers mines))
        (PMF.uniformOfFintype (Fin k → BitVec 256)))
      (PMF.map (fun mines => deployedKeys B other (deployedOffsets peers mines))
        (PMF.uniformOfFintype (Fin k → BitVec 256)))
      (k * (1 / ((2 ^ 127 : ℕ) : ENNReal))) :=
  TlsMpcProofs.OffsetSampling.ed25519_keys_close hℓ B peers initial other

/-! ## 4. The cut-and-choose counting bound (formerly P7) -/

open TlsMpcProofs.CutAndChoose in
/-- **Every placement of the bad set is equally likely** under a uniform challenge permutation:
`#{π | π(S) = T} · C(|α|, |S|) = |α|!`. **gen**. -/
theorem fiber_mul_choose {α : Type} [Fintype α] [DecidableEq α] (S T : Finset α) (hT : T.card = S.card) :
    fiber S T * (Fintype.card α).choose S.card = (Fintype.card α).factorial :=
  TlsMpcProofs.CutAndChoose.fiber_mul_choose S T hT

open TlsMpcProofs.CutAndChoose Function in
/-- **Undetected corruption, counted:** for `N` disjoint buckets of size `B > 0` and a bad set of
`B·t` candidates (`t ≥ 1`), `#undetected · C(|α|, B·t) = C(N, t) · |α|!`. **gen**. -/
theorem undetected_count {α : Type} [Fintype α] [DecidableEq α] {N B : ℕ} (bucket : Fin N → Finset α)
    (hcard : ∀ j, (bucket j).card = B) (hB : 0 < B) (hdisj : Pairwise (Disjoint on bucket))
    (S : Finset α) (t : ℕ) (ht : 0 < t) (hS : S.card = B * t) :
    (undetected bucket S).card * (Fintype.card α).choose (B * t) = N.choose t * (Fintype.card α).factorial :=
  TlsMpcProofs.CutAndChoose.undetected_count bucket hcard hB hdisj S t ht hS

open TlsMpcProofs.CutAndChoose Function in
/-- **A bad set whose size is not a multiple of `B` (or empty) is always detected.** **gen**. -/
theorem undetected_count_zero {α : Type} [Fintype α] [DecidableEq α] {N B : ℕ} (bucket : Fin N → Finset α)
    (hcard : ∀ j, (bucket j).card = B) (hB : 0 < B) (hdisj : Pairwise (Disjoint on bucket))
    (S : Finset α) (hS : ¬ (B ∣ S.card) ∨ S = ∅) :
    undetected bucket S = ∅ :=
  TlsMpcProofs.CutAndChoose.undetected_count_zero bucket hcard hB hdisj S hS

open TlsMpcProofs.CutAndChoose in
/-- **P7 for the protocol layout** (`B·N` opened positions, `N` buckets of `B`, one uniform
challenge permutation; P-CUT steps 2–3): a bad set of `B·t` candidates fixed before the challenge
goes undetected with probability exactly `C(N, t) / C(2BN, B·t)` — `parameters.py`'s
`bound(t)`. **M** (the C++ `dyn_word_mask.h` / `dabit_generator.h` are not modelled; the
detection rules P-CUT(d), (e) are the model's assumption). -/
theorem cut_and_bucket_probability {N B : ℕ} (hB : 0 < B) (S : Finset (Position N B)) (t : ℕ)
    (ht : 0 < t) (htN : t ≤ N) (hS : S.card = B * t) :
    ((undetected (protocolBucket N B) S).card : ℚ) / (2 * B * N).factorial =
      (N.choose t : ℚ) / (2 * B * N).choose (B * t) :=
  TlsMpcProofs.CutAndChoose.cut_and_bucket_probability hB S t ht htN hS

/-- **Deployed batch profile (`N = 2¹⁹`, `B = 8`, NEEDS_REVIEW 1.2): `bound(1) < 2⁻¹²⁸`.**
**M**. (Every `t`: `deployed_bound_all_t` below.) -/
theorem deployed_bound_t1 : 2 ^ 128 * (2 ^ 19).choose 1 < (2 * 8 * 2 ^ 19).choose (8 * 1) :=
  TlsMpcProofs.CutAndChoose.deployed_bound_t1

/-- **`check_parameters_128.py` profile 256/14: `bound(1) < 2⁻¹²⁸`.** **M**. -/
theorem profile_256_bound_t1 : 2 ^ 128 * (256 : ℕ).choose 1 < (2 * 14 * 256).choose (14 * 1) :=
  TlsMpcProofs.CutAndChoose.profile_256_bound_t1

/-- **Profile 512/13: `bound(1) < 2⁻¹²⁸`.** **M**. -/
theorem profile_512_bound_t1 : 2 ^ 128 * (512 : ℕ).choose 1 < (2 * 13 * 512).choose (13 * 1) :=
  TlsMpcProofs.CutAndChoose.profile_512_bound_t1

/-- **Profile 1024/12: `bound(1) < 2⁻¹²⁸`.** **M**. -/
theorem profile_1024_bound_t1 : 2 ^ 128 * (1024 : ℕ).choose 1 < (2 * 12 * 1024).choose (12 * 1) :=
  TlsMpcProofs.CutAndChoose.profile_1024_bound_t1

/-- **`bound` is non-increasing:** `bound(t + 1) ≤ bound(t)` for every `N`, `B ≥ 2`, `t < N`
(without division). **gen**. -/
theorem cut_bound_step (N B t : ℕ) (hB : 2 ≤ B) (htN : t < N) :
    N.choose (t + 1) * (2 * B * N).choose (B * t) ≤ N.choose t * (2 * B * N).choose (B * (t + 1)) :=
  TlsMpcProofs.CutAndChoose.bound_step N B t hB htN

/-- **`t = 1` is the worst case:** `bound(t) ≤ bound(1)` for `1 ≤ t ≤ N`, `B ≥ 2`. **gen**
(`parameters.py`'s `exact_worst_bound` is always attained at `t = 1`). -/
theorem cut_bound_le_bound_one (N B t : ℕ) (hB : 2 ≤ B) (ht : 1 ≤ t) (htN : t ≤ N) :
    N.choose t * (2 * B * N).choose (B * 1) ≤ N.choose 1 * (2 * B * N).choose (B * t) :=
  TlsMpcProofs.CutAndChoose.bound_le_bound_one N B t hB ht htN

open TlsMpcProofs.CutAndChoose in
/-- **Every bad set:** if `B ≥ 2` and `bound(1) < 2⁻¹²⁸`, any bad set fixed before the uniform
challenge goes undetected with probability `< 2⁻¹²⁸`. **M** (detection rules P-CUT(d), (e)
assumed). -/
theorem undetected_lt_of_bound_t1 {N B : ℕ} (hB : 2 ≤ B)
    (h1 : 2 ^ 128 * N.choose 1 < (2 * B * N).choose (B * 1)) (S : Finset (Position N B)) :
    ((undetected (protocolBucket N B) S).card : ℚ) / (2 * B * N).factorial < 1 / 2 ^ 128 :=
  TlsMpcProofs.CutAndChoose.undetected_lt_of_bound_t1 hB h1 S

/-- **Batch profile, every `t`: `bound(t) < 2⁻¹²⁸`.** **M**. -/
theorem deployed_bound_all_t (t : ℕ) (ht : 1 ≤ t) (htN : t ≤ 2 ^ 19) :
    2 ^ 128 * (2 ^ 19).choose t < (2 * 8 * 2 ^ 19).choose (8 * t) :=
  TlsMpcProofs.CutAndChoose.deployed_bound_all_t t ht htN

/-- **Profile 256/14, every `t`.** **M**. -/
theorem profile_256_bound_all_t (t : ℕ) (ht : 1 ≤ t) (htN : t ≤ 256) :
    2 ^ 128 * (256 : ℕ).choose t < (2 * 14 * 256).choose (14 * t) :=
  TlsMpcProofs.CutAndChoose.profile_256_bound_all_t t ht htN

/-- **Profile 512/13, every `t`.** **M**. -/
theorem profile_512_bound_all_t (t : ℕ) (ht : 1 ≤ t) (htN : t ≤ 512) :
    2 ^ 128 * (512 : ℕ).choose t < (2 * 13 * 512).choose (13 * t) :=
  TlsMpcProofs.CutAndChoose.profile_512_bound_all_t t ht htN

/-- **Profile 1024/12, every `t`.** **M**. -/
theorem profile_1024_bound_all_t (t : ℕ) (ht : 1 ≤ t) (htN : t ≤ 1024) :
    2 ^ 128 * (1024 : ℕ).choose t < (2 * 12 * 1024).choose (12 * t) :=
  TlsMpcProofs.CutAndChoose.profile_1024_bound_all_t t ht htN

open TlsMpcProofs.CutAndChoose in
/-- **Batch profile (`N = 2¹⁹`, `B = 8`): any bad set goes undetected with probability
`< 2⁻¹²⁸`.** **M** (P7 closed for the model). -/
theorem deployed_undetected_lt (S : Finset (Position (2 ^ 19) 8)) :
    ((undetected (protocolBucket (2 ^ 19) 8) S).card : ℚ) / (2 * 8 * 2 ^ 19).factorial < 1 / 2 ^ 128 :=
  TlsMpcProofs.CutAndChoose.deployed_undetected_lt S

open TlsMpcProofs.CutAndChoose in
/-- **Profile 256/14, as a probability.** **M**. -/
theorem profile_256_undetected_lt (S : Finset (Position 256 14)) :
    ((undetected (protocolBucket 256 14) S).card : ℚ) / (2 * 14 * 256).factorial < 1 / 2 ^ 128 :=
  TlsMpcProofs.CutAndChoose.profile_256_undetected_lt S

open TlsMpcProofs.CutAndChoose in
/-- **Profile 512/13, as a probability.** **M**. -/
theorem profile_512_undetected_lt (S : Finset (Position 512 13)) :
    ((undetected (protocolBucket 512 13) S).card : ℚ) / (2 * 13 * 512).factorial < 1 / 2 ^ 128 :=
  TlsMpcProofs.CutAndChoose.profile_512_undetected_lt S

open TlsMpcProofs.CutAndChoose in
/-- **Profile 1024/12, as a probability.** **M**. -/
theorem profile_1024_undetected_lt (S : Finset (Position 1024 12)) :
    ((undetected (protocolBucket 1024 12) S).card : ℚ) / (2 * 12 * 1024).factorial < 1 / 2 ^ 128 :=
  TlsMpcProofs.CutAndChoose.profile_1024_undetected_lt S

/-! ## 5. Open (comments only)

* H-GROUP: proved in section 7 for the Edwards formulas, the base point's subgroup, the
  scalar-multiple chains, X25519 on every coordinate of a curve point and `liftPoint`'s map. What
  remains of it: the group order `#E = 8ℓ` (point counting; needed to say that the `ℓ`-torsion is
  exactly the multiples of `B`, and for the cofactor reading of `edwards-torsion-hinted`); the
  X25519 ladder on inputs of the quadratic twist (its Edwards model `−2x² + y² = 1 + 2d·x²y²`
  has `a = −2`, not a square, so the complete-law construction does not apply); the statement
  that the C++ `step` implements `recode` (the Lean `recode` is written to match it line by
  line).
* `idealCommit`; the C++ protocols themselves (P-CUT, P-HINT … as scripts, S9–S16).
* Cut-and-choose: the model's detection rules (P-CUT(d), (e)) against `dyn_word_mask.h` /
  `dabit_generator.h`; that the two challenge permutations of P-CUT compose to one uniform one.
* Offset agreement: `idealCommit` (the peer's value independent of the honest party's, modelled as
  a fixed value; peer values chosen adaptively across messages are not covered); the two aborts
  that depend only on the offsets (`mine = peer`, offset `0`) are not modelled; that the
  recipient's point is nonzero and killed by `ℓ` is the hypothesis of section 7b's statements
  (true for the base point; for a recipient key it is what the torsion check is for).
* XEdDSA `recover`: the sign of `x` and its binding to the signature bit (`doubleScalar` is
  proved to compute `s·B − h·A` for Boolean bit inputs: section 7d).
* Receive: the value forms of `varintValue` (widths 2–5) and `canonicalRange` (in
  `TlsMpc.Signal.ReceiveFirst`, whose 52-module import closure is not compiled here).
-/

/-! ## 6. Receive: `Unpad.decode` is PKCS#7 unpadding -/

open TlsMpcProofs.UnpadSpec in
/-- **At most one PKCS#7 padding length** (the last byte is `p`). **gen**. -/
theorem unpad_paddedWith_unique {block : List (BitVec 8)} (hlen : block.length = 16) {p q : ℕ}
    (hp : PaddedWith block p) (hq : PaddedWith block q) : p = q :=
  TlsMpcProofs.UnpadSpec.paddedWith_unique hlen hp hq

open TlsMpcProofs.UnpadSpec in
/-- **A block padded with `p` decodes to `[255, 16 − p] ++ take (16 − p) ++ p zero bytes`.**
**K-fn** (`Unpad.decode`, inside `CbcOpen.openCore`). -/
theorem unpad_decode_padded {block : List (BitVec 8)} (hlen : block.length = 16) {p : ℕ}
    (hp : PaddedWith block p) : Signal.Unpad.decode ByteAuth.concrete block = accepted block p :=
  TlsMpcProofs.UnpadSpec.decode_padded hlen hp

open TlsMpcProofs.UnpadSpec in
/-- **A block without PKCS#7 padding decodes to eighteen zero bytes.** **K-fn**. -/
theorem unpad_decode_unpadded {block : List (BitVec 8)} (hlen : block.length = 16)
    (h : ∀ p, ¬ PaddedWith block p) : Signal.Unpad.decode ByteAuth.concrete block = List.replicate 18 0 :=
  TlsMpcProofs.UnpadSpec.decode_unpadded hlen h

open TlsMpcProofs.UnpadSpec in
/-- **The status byte is 255 exactly when the block carries valid PKCS#7 padding.** **K-fn**. -/
theorem unpad_decode_accepts_iff {block : List (BitVec 8)} (hlen : block.length = 16) :
    (Signal.Unpad.decode ByteAuth.concrete block).head? = some 255 ↔ ∃ p, PaddedWith block p :=
  TlsMpcProofs.UnpadSpec.decode_accepts_iff hlen

/-! ## 7. H-GROUP: the Edwards formulas are a group law

`Ed25519.Curve` is the type of points of `−x² + y² = 1 + d·x²·y²` over `ZMod (2²⁵⁵ − 19)`,
`d = −121665/121666` (`Ed25519.dK`); its `+`, `−`, `0` are the unified addition law, `(−x, y)` and
`(0, 1)`. `Ed25519.Affine v P`: the pair `v` of main-package field values is the point `P`.
`Ed25519.ExtRep e P`: the extended coordinates `e` represent `P` (`Z ≠ 0`, `X = xZ`, `Y = yZ`,
`T = xyZ`). `Edwards.MRep X Z P`: `(X : Z)` is the projective Montgomery coordinate
`(1 + y : 1 − y)` of `P`. -/

open Ed25519 Edwards in
/-- **`d` is not a square mod `p`** (Euler's criterion, the power by kernel arithmetic). **gen**. -/
theorem edwards_d_not_square : ¬ IsSquare dK :=
  TlsMpcProofs.Ed25519.dK_not_isSquare

open Ed25519 Edwards in
/-- **`−1` is a square mod `p`.** **gen**. -/
theorem edwards_neg_one_square : IsSquare (-1 : ZMod FieldDag.modulus) :=
  TlsMpcProofs.Ed25519.neg_one_isSquare

open Ed25519 Edwards in
/-- **The addition law is complete** (Bernstein–Lange): on curve points neither denominator
vanishes. **gen** (H-GROUP; this is why the runtime's abort on a zero denominator cannot happen on
valid inputs). -/
theorem edwards_complete (P Q : Curve) :
    1 + dK * P.x * Q.x * P.y * Q.y ≠ 0 ∧ 1 - dK * P.x * Q.x * P.y * Q.y ≠ 0 :=
  ⟨Point.denom_x_ne_zero P Q, Point.denom_y_ne_zero P Q⟩

open Ed25519 Edwards in
/-- **The group operations are the formulas:** `P + Q`, `−P`, `0` in coordinates. **gen**. -/
theorem edwards_operations (P Q : Curve) :
    (P + Q).x = (P.x * Q.y + P.y * Q.x) / (1 + dK * P.x * Q.x * P.y * Q.y) ∧
      (P + Q).y = (P.y * Q.y + P.x * Q.x) / (1 - dK * P.x * Q.x * P.y * Q.y) ∧
      (-P).x = -P.x ∧ (-P).y = P.y ∧ (0 : Curve).x = 0 ∧ (0 : Curve).y = 1 :=
  ⟨Point.add_x P Q, Point.add_y P Q, rfl, rfl, rfl, rfl⟩

open Ed25519 Edwards in
/-- **Associativity of the Edwards addition law** (the polynomial identity modulo the three
curve equations, with explicit cofactors: `Edwards.assoc_x_poly`, `assoc_y_poly`). **gen**
(H-GROUP). -/
theorem edwards_add_assoc (P Q R : Curve) : P + Q + R = P + (Q + R) :=
  add_assoc P Q R

open Ed25519 Edwards in
/-- **Commutativity, identity, inverse.** With `edwards_add_assoc`: the curve points are a
commutative group (`Edwards.Point.instAddCommGroup`). **gen** (H-GROUP). -/
theorem edwards_group_laws (P Q : Curve) : P + Q = Q + P ∧ 0 + P = P ∧ -P + P = 0 :=
  ⟨add_comm P Q, zero_add P, neg_add_cancel P⟩

open Ed25519 in
/-- **`EdwardsAffine.pointAddValue` is the group law on curve points.** **K-fn** (every affine
addition of `edwards-prepare`, `edwards-offset-sum`, `lift-point`, the windows). -/
theorem pointAddValue_is_group_add {p q : EdwardsAffine.Value} {P Q : Curve} (hp : Affine p P)
    (hq : Affine q Q) : Affine (EdwardsAffine.pointAddValue p q) (P + Q) :=
  TlsMpcProofs.Ed25519.affine_pointAddValue hp hq

open Ed25519 in
/-- **`EdwardsHinted.negate` is the group negation; `(0, 1)` is the neutral element.** **K-fn**. -/
theorem negate_is_group_neg {v : EdwardsAffine.Value} {P : Curve} (hp : Affine v P) :
    Affine (FieldDag.ofNat 0 - v.1, v.2) (-P) ∧ Affine (FieldDag.ofNat 0, FieldDag.ofNat 1) (0 : Curve) :=
  ⟨TlsMpcProofs.Ed25519.affine_neg hp, TlsMpcProofs.Ed25519.affine_neutral⟩

open Ed25519 in
/-- **`EdwardsHinted.curveCheck` is zero exactly when the pair is a point of the group.**
**K-fn** (`lift-open`, `edwards-torsion-hinted`). -/
theorem curveCheck_zero_iff (input : ℕ → FieldDag.F) (p : EdwardsAffine.Point) :
    (EdwardsHinted.curveCheck p).eval input = FieldDag.ofNat 0 ↔
      ∃ P : Curve, Affine (EdwardsAffine.evalPoint input p) P := by
  rw [TlsMpcProofs.Ed25519.curveCheck_eval]
  exact TlsMpcProofs.Ed25519.curveCheckValue_zero_iff_exists _

open Ed25519 in
/-- **`EdwardsHinted.extAddValue` is the group law in extended coordinates**, and the `Z` of its
result is nonzero. **K-fn** (`extSum`, `doublings`, `torsionHinted`). -/
theorem extAddValue_is_group_add {p q : EdwardsHinted.ExtV} {P Q : Curve} (hp : ExtRep p P)
    (hq : ExtRep q Q) : ExtRep (EdwardsHinted.extAddValue p q) (P + Q) :=
  TlsMpcProofs.Ed25519.extRep_extAddValue hp hq

open Ed25519 in
/-- **`ofAffineValue` / `toAffineValue` move between the two representations.** **K-fn**. -/
theorem ext_affine_conversions {v : EdwardsAffine.Value} {e : EdwardsHinted.ExtV} {P : Curve} :
    (Affine v P → ExtRep (EdwardsHinted.ofAffineValue v) P) ∧
      (ExtRep e P → Affine (EdwardsHinted.toAffineValue e) P) :=
  ⟨TlsMpcProofs.Ed25519.extRep_ofAffineValue, TlsMpcProofs.Ed25519.affine_toAffineValue⟩

open Ed25519 in
/-- **`EdwardsAffine.sumTreeValue` of curve points is their sum in the group.** **K-fn**
(`edwards-offset-sum`, `edwards-prepare`'s initial point). -/
theorem sumTreeValue_is_group_sum (l : List (EdwardsAffine.Value × Curve))
    (h : ∀ a ∈ l, Affine a.1 a.2) :
    Affine (EdwardsAffine.sumTreeValue (l.map Prod.fst)) (l.map Prod.snd).sum :=
  TlsMpcProofs.Ed25519.affine_sumTreeValue l h

open Ed25519 in
/-- **`EdwardsHinted.extSumValue` of represented points represents their sum in the group.**
**K-fn** (`edwards-offset-sum-fast`, `edwards-bit-sum`, `edwards-signature-sum`). -/
theorem extSumValue_is_group_sum (l : List (EdwardsHinted.ExtV × Curve))
    (h : ∀ a ∈ l, ExtRep a.1 a.2) :
    ExtRep (EdwardsHinted.extSumValue (l.map Prod.fst)) (l.map Prod.snd).sum :=
  TlsMpcProofs.Ed25519.extRep_extSumValue l h

open Ed25519 in
/-- **When `recipient`'s check value is zero, its output is a point of the curve group** (the
reading of `recipient_check_zero_iff` that needed H-GROUP's formulas). **K-fn**. -/
theorem recipient_on_curve (u : FieldDag.Expr) (input : ℕ → FieldDag.F)
    (h : (EdwardsAffine.recipient u).2.eval input = FieldDag.ofNat 0) :
    ∃ P : Curve, Affine (EdwardsAffine.evalPoint input (EdwardsAffine.recipient u).1) P :=
  TlsMpcProofs.Ed25519.recipient_onCurve u input h

open Ed25519 in
/-- **When `recover` reports `valid = 1`, its `(x, y)` is a point of the curve group.** **K-fn**
(`xeddsa-recover`). -/
theorem xeddsa_recover_on_curve (U valid x y : FieldDag.F)
    (h : Signal.XEdDsaField.recover X25519.concrete U = [valid, x, y]) (hv : valid = FieldDag.ofNat 1) :
    ∃ P : Curve, TlsMpcProofs.toZMod x = P.x ∧ TlsMpcProofs.toZMod y = P.y :=
  TlsMpcProofs.Ed25519.recover_onCurve U valid x y h hv

/-! ### 7b. The base point and the subgroup of order `ℓ` -/

open Ed25519 in
/-- **`ℓ·B = 0` for the base point `B = (baseX, baseY)`** (on the curve: `Ed25519.base_onCurve`):
double-and-add in extended coordinates over `ℕ` mod `p`, evaluated by the kernel
(`decide +kernel`, `Nat` arithmetic only), proved to be the group's scalar multiple. **gen**. -/
theorem base_order_nsmul : Signal.XEdDsaScalar.order • B = 0 :=
  TlsMpcProofs.Ed25519.order_nsmul_base

open Ed25519 in
/-- **The base point has order exactly `ℓ`** (`ℓ` prime, `B ≠ 0`). **gen**. -/
theorem base_addOrderOf : addOrderOf B = Signal.XEdDsaScalar.order :=
  TlsMpcProofs.Ed25519.addOrderOf_base

open Ed25519 in
/-- **A nonzero point killed by `ℓ` generates a subgroup with exactly `ℓ` elements**; in
particular the base point. **gen** (this replaces "a finite commutative group of order `ℓ`" in
section 3b/3c; `#Curve = 8ℓ` is not proved and not needed). -/
theorem curve_subgroup_card {P : Curve} (h : Signal.XEdDsaScalar.order • P = 0) (hP : P ≠ 0) :
    Fintype.card (AddSubgroup.zmultiples P) = Signal.XEdDsaScalar.order ∧
      Fintype.card (AddSubgroup.zmultiples B) = Signal.XEdDsaScalar.order :=
  ⟨TlsMpcProofs.Ed25519.card_zmultiples_of_order h hP, TlsMpcProofs.Ed25519.card_zmultiples_base⟩

open Ed25519 TlsMpcProofs.OffsetAgreement in
/-- **Section 3b on the curve, H-GROUP discharged:** for a curve point `P ≠ 0` with `ℓ·P = 0`,
the published key `initial·P + offset·P` (offset uniform mod `ℓ`) is uniform on the subgroup `P`
generates, whatever the initial scalar. **M**. -/
theorem curve_offset_public_key_uniform {P : Curve} (h : Signal.XEdDsaScalar.order • P = 0)
    (hP : P ≠ 0) (initial : ZMod Signal.XEdDsaScalar.order) :
    PMF.map (publicKey (gen P) initial) (PMF.uniformOfFintype (ZMod Signal.XEdDsaScalar.order)) =
      PMF.uniformOfFintype (AddSubgroup.zmultiples P) :=
  TlsMpcProofs.Ed25519.curve_public_key_uniform h hP initial

open Ed25519 TlsMpcProofs.OffsetSampling in
/-- **Section 3c on the curve, H-GROUP discharged:** deployed sampling, one message, any two
initial scalars, every event within `2⁻¹²⁷`. **M**. -/
theorem curve_deployed_key_close {P : Curve} (h : Signal.XEdDsaScalar.order • P = 0) (hP : P ≠ 0)
    (peer : BitVec 256) (initial other : ZMod Signal.XEdDsaScalar.order) :
    EventClose
      (PMF.map (fun mine => deployedKey (gen P) initial (deployedOffset mine peer))
        (PMF.uniformOfFintype (BitVec 256)))
      (PMF.map (fun mine => deployedKey (gen P) other (deployedOffset mine peer))
        (PMF.uniformOfFintype (BitVec 256)))
      (1 / ((2 ^ 127 : ℕ) : ENNReal)) :=
  TlsMpcProofs.Ed25519.curve_key_close h hP peer initial other

open Ed25519 TlsMpcProofs.OffsetSampling in
/-- **… and within `2⁻¹²⁷` of uniform on the subgroup.** **M**. -/
theorem curve_deployed_key_close_uniform {P : Curve} (h : Signal.XEdDsaScalar.order • P = 0)
    (hP : P ≠ 0) (peer : BitVec 256) (initial : ZMod Signal.XEdDsaScalar.order) :
    StatClose
      (PMF.map (fun mine => deployedKey (gen P) initial (deployedOffset mine peer))
        (PMF.uniformOfFintype (BitVec 256)))
      (PMF.uniformOfFintype (AddSubgroup.zmultiples P)) (1 / ((2 ^ 127 : ℕ) : ENNReal)) :=
  TlsMpcProofs.Ed25519.curve_key_close_uniform h hP peer initial

open Ed25519 TlsMpcProofs.OffsetSampling in
/-- **`k` messages on the curve:** the joint keys, any two initial scalars, within `k·2⁻¹²⁷`.
**M**. -/
theorem curve_deployed_keys_close {P : Curve} (h : Signal.XEdDsaScalar.order • P = 0) (hP : P ≠ 0)
    {k : ℕ} (peers : Fin k → BitVec 256) (initial other : ZMod Signal.XEdDsaScalar.order) :
    EventClose
      (PMF.map (fun mines => deployedKeys (gen P) initial (deployedOffsets peers mines))
        (PMF.uniformOfFintype (Fin k → BitVec 256)))
      (PMF.map (fun mines => deployedKeys (gen P) other (deployedOffsets peers mines))
        (PMF.uniformOfFintype (Fin k → BitVec 256)))
      (k * (1 / ((2 ^ 127 : ℕ) : ENNReal))) :=
  TlsMpcProofs.Ed25519.curve_keys_close h hP peers initial other

open Ed25519 TlsMpcProofs.OffsetSampling in
/-- **The base point, no hypothesis at all:** the deployed key `initial·B + offset·B` is within
`2⁻¹²⁷` of uniform on the `ℓ`-element subgroup generated by `B`. **M**. -/
theorem base_deployed_key_close_uniform (peer : BitVec 256)
    (initial : ZMod Signal.XEdDsaScalar.order) :
    StatClose
      (PMF.map (fun mine => deployedKey (gen B) initial (deployedOffset mine peer))
        (PMF.uniformOfFintype (BitVec 256)))
      (PMF.uniformOfFintype (AddSubgroup.zmultiples B)) (1 / ((2 ^ 127 : ℕ) : ENNReal)) :=
  TlsMpcProofs.Ed25519.base_key_close_uniform peer initial

open Ed25519 in
/-- **P-HINT(c) on the curve, H-GROUP discharged:** `Z = P + M_A + M_B` is uniform on the curve
group for the honest party's uniform curve point `M_B`. **M**. -/
theorem curve_hinted_Z_uniform (P maskA : Curve) :
    PMF.map (fun maskB => MaskedAgreement.opened P maskA maskB) (PMF.uniformOfFintype Curve) =
      PMF.uniformOfFintype Curve :=
  TlsMpcProofs.Ed25519.curve_hinted_Z_uniform P maskA

open Ed25519 in
/-- **The masked agreement on the curve, H-GROUP discharged.** **M**. -/
theorem curve_maskedAgreement_mask_hides (R other maskA : Curve) :
    PMF.map (fun maskB => MaskedAgreement.opened R maskA maskB) (PMF.uniformOfFintype Curve) =
      PMF.map (fun maskB => MaskedAgreement.opened other maskA maskB) (PMF.uniformOfFintype Curve) :=
  TlsMpcProofs.Ed25519.curve_maskedAgreement_mask_hides R other maskA

/-! ### 7c. X25519 (the Montgomery ladder) -/

open Ed25519 Edwards in
/-- **One ladder step is `(Q, R) ↦ (2Q, Q + R)` in the Edwards group**, for representatives of
`Q`, `R` and the affine `u ≠ 0` of `R − Q` (all degenerate cases included). **K-fn**
(`X25519.advance`). -/
theorem x25519_advance {u : FieldDag.F} {s : X25519.Coordinates FieldDag.F} {Q R : Curve}
    (hD : MRep (TlsMpcProofs.toZMod u) 1 (R - Q)) (hu : TlsMpcProofs.toZMod u ≠ 0)
    (hQ : MRep (TlsMpcProofs.toZMod s.x2) (TlsMpcProofs.toZMod s.z2) Q)
    (hR : MRep (TlsMpcProofs.toZMod s.x3) (TlsMpcProofs.toZMod s.z3) R) :
    MRep (TlsMpcProofs.toZMod (X25519.advance X25519.concrete u s).x2)
        (TlsMpcProofs.toZMod (X25519.advance X25519.concrete u s).z2) (Q + Q) ∧
      MRep (TlsMpcProofs.toZMod (X25519.advance X25519.concrete u s).x3)
        (TlsMpcProofs.toZMod (X25519.advance X25519.concrete u s).z3) (Q + R) :=
  TlsMpcProofs.Ed25519.advance_rep hD hu hQ hR

open Ed25519 Edwards in
/-- **X25519 is scalar multiplication in the Edwards group:** if `u ≠ 0` is the Montgomery
coordinate `(1 + y)/(1 − y)` of a curve point `P`, `X25519.spec input u` is the Montgomery
coordinate of `k·P`, `k` the clamped scalar (`0` when `k·P = 0`). **K-fn** (`x25519`;
`X25519.compiled_compute_correct` links the artifact to `spec`). `u = 0`:
`x25519_spec_scalar_mult_all`; inputs on the quadratic twist are not covered. -/
theorem x25519_spec_scalar_mult (input : ℕ → Bool) (u : FieldDag.F) (P : Curve)
    (hP : MRep (TlsMpcProofs.toZMod u) 1 P) (hu : TlsMpcProofs.toZMod u ≠ 0) :
    TlsMpcProofs.toZMod (X25519.spec input u) = montU (clampedScalar input • P) :=
  TlsMpcProofs.Ed25519.spec_eq_montU input u P hP hu

open Ed25519 in
/-- **The clamped scalar in closed form, any input bits:** `2²⁵⁴ + 8·m`, `m` the value of input
bits 3 … 253 (bits 0–2 cleared, bit 254 set, bit 255 ignored). **K-fn** (`x25519`). -/
theorem x25519_clampedScalar_eq (input : ℕ → Bool) :
    clampedScalar input =
      2 ^ 254 + 8 * TlsMpcProofs.bitsValue 0 ((List.range 251).reverse.map (fun i => input (i + 3))) :=
  TlsMpcProofs.Ed25519.clampedScalar_eq input

open Ed25519 in
/-- **RFC 7748 `decodeScalar25519`:** for the scalar bytes as `X25519.decodeScalar` reads them,
the ladder's scalar is `2²⁵⁴ + 8·(⌊n/8⌋ mod 2²⁵¹)`, `n` the little-endian value of the bytes (low
three bits cleared, bit 255 cleared, bit 254 set). **K-fn**. -/
theorem x25519_clampedScalar_rfc (bytes : List UInt8) :
    clampedScalar (X25519.decodeScalar bytes) = 2 ^ 254 + 8 * (leValue bytes / 8 % 2 ^ 251) :=
  TlsMpcProofs.Ed25519.clampedScalar_decodeScalar bytes

open Ed25519 in
/-- **The clamped scalar is a multiple of 8 in `[2²⁵⁴, 2²⁵⁵)`.** **K-fn**. -/
theorem x25519_clampedScalar_bounds (input : ℕ → Bool) :
    clampedScalar input % 8 = 0 ∧ 2 ^ 254 ≤ clampedScalar input ∧ clampedScalar input < 2 ^ 255 :=
  ⟨TlsMpcProofs.Ed25519.clampedScalar_mod_eight input,
    TlsMpcProofs.Ed25519.clampedScalar_range input⟩

open Ed25519 Edwards in
/-- **X25519 at `u = 0` is `0`** (RFC 7748's all-zero output), and that is the group answer:
`u = 0` is `T2 = (0, −1)`, of order 2, and the clamped scalar is even, so `k·T2 = 0`. **K-fn**. -/
theorem x25519_u_zero (input : ℕ → Bool) {u : FieldDag.F} (hu : TlsMpcProofs.toZMod u = 0) :
    TlsMpcProofs.toZMod (X25519.spec input u) = 0 ∧ T2 + T2 = 0 ∧ clampedScalar input • T2 = 0 :=
  ⟨TlsMpcProofs.Ed25519.spec_u_zero input hu, TlsMpcProofs.Ed25519.T2_add_self,
    (TlsMpcProofs.Ed25519.spec_u_zero_montU input hu).1⟩

open Ed25519 Edwards in
/-- **X25519 is scalar multiplication for every curve point** (no `u ≠ 0`). **K-fn**. -/
theorem x25519_spec_scalar_mult_all (input : ℕ → Bool) (u : FieldDag.F) (P : Curve)
    (hP : MRep (TlsMpcProofs.toZMod u) 1 P) :
    TlsMpcProofs.toZMod (X25519.spec input u) = montU (clampedScalar input • P) :=
  TlsMpcProofs.Ed25519.spec_eq_montU' input u P hP

open Ed25519 Edwards in
/-- **X25519 on every Montgomery coordinate of a curve point:** if `u(u² + 486662u + 1)` is a
square, there is a curve point `P` with `(1 + y)/(1 − y) = u` and `X25519.spec input u` is the
coordinate of `k·P`. **K-fn**. -/
theorem x25519_on_curve (input : ℕ → Bool) (u : FieldDag.F)
    (h : IsSquare (montQ (TlsMpcProofs.toZMod u))) :
    ∃ P : Curve, P.y ≠ 1 ∧ montU P = TlsMpcProofs.toZMod u ∧
      TlsMpcProofs.toZMod (X25519.spec input u) = montU (clampedScalar input • P) :=
  TlsMpcProofs.Ed25519.x25519_on_curve input u h

/-! ### 7d. The scalar-multiple chains -/

open Ed25519 EdwardsAffine EdwardsHinted in
/-- **One window (`windowValue`):** entries `P, 2P, …, 8P`, next base `16P`. **K-fn**
(`edwards-prepare`, `edwards-prepare-hinted`). -/
theorem window_multiples {b : EdwardsAffine.Value} {P : Curve} (hb : Affine b P) :
    (windowValue b).1.length = 8 ∧ Multiples (windowValue b).1 P ∧
      Affine (windowValue b).2 (16 • P) :=
  TlsMpcProofs.Ed25519.window_spec hb

open Ed25519 EdwardsAffine EdwardsHinted in
/-- **The window table:** entry `8w + j` of `chain windowValue r n` is `((j+1)·16^w)·P`. **K-fn**. -/
theorem window_table {r : EdwardsAffine.Value} {P : Curve} (hr : Affine r P) (n : ℕ) :
    (chain windowValue r n).length = 8 * n ∧
      ∀ w < n, ∀ j < 8, Affine ((chain windowValue r n).getD (8 * w + j)
        (FieldDag.ofNat 0, FieldDag.ofNat 1)) (((j + 1) * 16 ^ w) • P) :=
  TlsMpcProofs.Ed25519.windowChain_spec hr n

open Ed25519 EdwardsAffine EdwardsHinted in
/-- **`prepareHinted`'s `bitEntry i` is `2^i·P`** once every link holds. **K-fn**. -/
theorem prepareHinted_bit_entry (input : ℕ → FieldDag.F) {P : Curve}
    (hP : Affine (input 0, input 1) P)
    (h : LinkedFrom (evalPoint input) window (inputPoint 0)
      ((List.range (windows - 1)).map (fun i => hinted (prepareHints + 4 * i))))
    (i : ℕ) (hi : i < 256) :
    Affine (evalPoint input (bitEntry (entries window (prepareBases ())) i)) (2 ^ i • P) :=
  TlsMpcProofs.Ed25519.prepareHinted_bitEntry input hP h i hi

open Ed25519 EdwardsAffine EdwardsHinted in
/-- **`prepareHinted`'s initial point is `(kA + kB)·P`** once every link holds. **K-fn**. -/
theorem prepareHinted_initial_point (input : ℕ → FieldDag.F) {P : Curve}
    (hP : Affine (input 0, input 1) P)
    (h : LinkedFrom (evalPoint input) window (inputPoint 0)
      ((List.range (windows - 1)).map (fun i => hinted (prepareHints + 4 * i))))
    (c : ℕ → Bool) (hbits : ∀ i < 2 * scalarBits, input (prepareBits + i) = X25519.bitValue (c i)) :
    ExtRep (evalExt input (extSum ((List.range (2 * scalarBits)).map (fun i =>
        chooseAffine (.input (prepareBits + i))
          (bitEntry (entries window (prepareBases ())) (i % scalarBits))))))
      ((TlsMpcProofs.bitsValue 0 ((List.range 252).reverse.map c) +
        TlsMpcProofs.bitsValue 0 ((List.range 252).reverse.map (fun i => c (252 + i)))) • P) :=
  TlsMpcProofs.Ed25519.prepareHinted_initial input hP h c hbits

open Ed25519 EdwardsAffine EdwardsHinted in
/-- **One doubling window (`doublingsValue`):** `P, 2P, 4P, 8P` (extended), next base `16P`.
**K-fn** (`edwards-bit-table`). -/
theorem doublings_multiples {b : EdwardsAffine.Value} {P : Curve} (hb : Affine b P) :
    (doublingsValue b).1.length = 4 ∧
      (∀ j < 4, ExtRep ((doublingsValue b).1.getD j neutralValue) (2 ^ j • P)) ∧
      Affine (doublingsValue b).2 (16 • P) :=
  TlsMpcProofs.Ed25519.doublings_spec hb

open Ed25519 EdwardsAffine EdwardsHinted in
/-- **`bitTable`'s entry `i` is `2^i·P`** once every link holds. **K-fn**. -/
theorem bitTable_entries (input : ℕ → FieldDag.F) {P : Curve} (hP : Affine (input 0, input 1) P)
    (h : LinkedFrom (evalPoint input) doublings (inputPoint 0)
      ((List.range (windows - 1)).map (fun i => hinted (2 + 4 * i))))
    (i : ℕ) (hi : i < 256) :
    ExtRep (((entries doublings (bitTableBases ())).map (evalExt input)).getD i neutralValue)
      (2 ^ i • P) :=
  TlsMpcProofs.Ed25519.bitTable_entry input hP h i hi

open Ed25519 in
/-- **The signed base-16 recoding (`edwards_points.h` `step`) encodes the number:**
`Σ dᵢ·16^i + 16^k·carry = (n mod 16^k) + c`. **gen**. -/
theorem recode_encodes (c n k : ℕ) :
    digitsValue (recode c n k).1 + 16 ^ k * ((recode c n k).2 : ℤ) = ((n % 16 ^ k : ℕ) : ℤ) + c :=
  TlsMpcProofs.Ed25519.recode_value c n k

open Ed25519 in
/-- **64 windows, offset `< 2²⁵²`:** the digits encode `n` exactly, lie in `−8 … 8`, and leave no
carry (the C++ check `need(!carry, …)` never fails). **gen**. -/
theorem recode_offset (n : ℕ) (hn : n < 2 ^ 252) :
    digitsValue (recode 0 n 64).1 = n ∧ (recode 0 n 64).2 = 0 ∧
      (recode 0 n 64).1.length = 64 ∧ ∀ d ∈ (recode 0 n 64).1, -8 ≤ d ∧ d ≤ 8 :=
  TlsMpcProofs.Ed25519.recode64_value n hn

open Ed25519 in
/-- **A signed table entry is the signed multiple** (sign `−1` for a negative digit). **K-fn**. -/
theorem signed_table_entry {x y s : FieldDag.F} {Q : Curve} {d : ℤ}
    (h : Affine (x, y) (d.natAbs • Q))
    (hs : TlsMpcProofs.toZMod s = if d < 0 then -1 else 1) : Affine (s * x, y) (d • Q) :=
  TlsMpcProofs.Ed25519.signed_entry h hs

open Ed25519 Edwards EdwardsAffine in
/-- **`offsetSum` with the C++ recoding computes `u(I + n·P)`** for an offset `n < 2²⁵²`. **K-fn**
(`edwards-offset-sum`). -/
theorem offsetSum_scalar_mult (input : ℕ → FieldDag.F) {I P : Curve} (n : ℕ) (hn : n < 2 ^ 252)
    (hI : Affine (input 0, input 1) I)
    (hw : ∀ w < windows,
      Affine (input (2 + 3 * w), input (2 + 3 * w + 1))
        ((((recode 0 n 64).1.getD w 0).natAbs * 16 ^ w) • P) ∧
      TlsMpcProofs.toZMod (input (2 + 3 * w + 2)) =
        if (recode 0 n 64).1.getD w 0 < 0 then -1 else 1) :
    ∃ o : FieldDag.F, offsetSum.map (FieldDag.Expr.eval input) = [o] ∧
      TlsMpcProofs.toZMod o = montU (I + n • P) :=
  TlsMpcProofs.Ed25519.offsetSum_recoded input n hn hI hw

open Ed25519 Edwards EdwardsHinted in
/-- **X25519 from a bit table (`bitSum`) is X25519:** with the table `2^i·P` (`i = 3 … 254`) of
the curve point `P` whose Montgomery representative is `u`, scalar bits 3 … 253 of `input'` and
`valid = 1`, the quotient of the two outputs is `X25519.spec input' u`. **K-fn**
(`edwards-bit-sum`). -/
theorem bitSum_is_x25519 (input : ℕ → FieldDag.F) (input' : ℕ → Bool) (u : FieldDag.F) {P : Curve}
    (hP : MRep (TlsMpcProofs.toZMod u) 1 P)
    (hpts : ∀ j ≤ agreementBits, ExtRep (evalExt input (extInput (2 + 4 * j))) (2 ^ (j + 3) • P))
    (hbits : ∀ j < agreementBits,
      input (2 + 4 * (agreementBits + 1) + j) = X25519.bitValue (input' (j + 3)))
    (hvalid : input 0 = FieldDag.ofNat 1) :
    ∃ N D : FieldDag.F, (bitSum ()).map (FieldDag.Expr.eval input) = [N, D] ∧
      TlsMpcProofs.toZMod N / TlsMpcProofs.toZMod D = TlsMpcProofs.toZMod (X25519.spec input' u) :=
  TlsMpcProofs.Ed25519.bitSum_eq_x25519 input input' u hP hpts hbits hvalid

open Ed25519 in
/-- **`XEdDsaField.add` is the group law** (unscaled extended coordinates, `k = 2d`). **K-fn**. -/
theorem xeddsa_add_is_group_add {p q : Signal.XEdDsaField.Point FieldDag.F} {P Q : Curve}
    (hp : XRep p P) (hq : XRep q Q) : XRep (Signal.XEdDsaField.add X25519.concrete p q) (P + Q) :=
  TlsMpcProofs.Ed25519.xrep_add hp hq

open Ed25519 in
/-- **`XEdDsaField.doubleScalar` computes `[s]B − [h]A`** for a curve point `A = (x, y)` and
Boolean bit lists (big-endian). **K-fn** (`xeddsa`). -/
theorem xeddsa_doubleScalar {x y : FieldDag.F} {A : Curve} (hA : Affine (x, y) A) (h s : List Bool) :
    ∃ v : EdwardsAffine.Value,
      Signal.XEdDsaField.doubleScalar X25519.concrete x y (h.map X25519.bitValue)
          (s.map X25519.bitValue) = [v.1, v.2] ∧
        Affine v (TlsMpcProofs.bitsValue 0 s • B - TlsMpcProofs.bitsValue 0 h • A) :=
  TlsMpcProofs.Ed25519.doubleScalar_spec hA h s

open Ed25519 in
/-- **The `xeddsa` field program computes `s·B − h·A`** for the bits of `h < 2²⁵⁶`, `s < 2²⁵³` at
inputs 2 …, 258 … and the curve point `A` at inputs 0, 1. **K-fn**. -/
theorem xeddsa_run_doubleScalar (input : ℕ → FieldDag.F) {A : Curve}
    (hA : Affine (input 0, input 1) A) (hh sc : ℕ) (hlt : hh < 2 ^ 256) (slt : sc < 2 ^ 253)
    (hbits : ∀ i < 256, input (2 + i) = X25519.bitValue (hh.testBit i))
    (sbits : ∀ i < 253, input (258 + i) = X25519.bitValue (sc.testBit i)) :
    ∃ v : EdwardsAffine.Value, Signal.XEdDsaField.run X25519.concrete false input = [v.1, v.2] ∧
      Affine v (sc • B - hh • A) :=
  TlsMpcProofs.Ed25519.run_doubleScalar_spec input hA hh sc hlt slt hbits sbits

/-! ### 7e. The Montgomery-to-Edwards map (`liftPoint`) -/

open Ed25519 Edwards in
/-- **The map `x = √(−486664)·u/v`, `y = (u − 1)/(u + 1)`** sends a Montgomery point with
`v ≠ 0` to a point of the Edwards group with Montgomery coordinate `u`. **gen**. -/
theorem montgomery_map_onCurve {u v : ZMod FieldDag.modulus} (hv : v * v = montQ u) (hv0 : v ≠ 0) :
    ∃ P : Curve, P.x = sA2 * u / v ∧ P.y = (u - 1) / (u + 1) ∧ P.y ≠ 1 ∧ montU P = u :=
  TlsMpcProofs.Ed25519.montgomery_lift hv hv0

open Ed25519 Edwards in
/-- **`v ↦ −v` is the group negation** (same `u`). **gen**. -/
theorem montgomery_map_neg {u v : ZMod FieldDag.modulus} {P : Curve} (hx : P.x = sA2 * u / v) :
    (-P).x = sA2 * u / (-v) ∧ (-P).y = P.y ∧ montU (-P) = montU P :=
  TlsMpcProofs.Ed25519.montgomery_lift_neg hx

open Ed25519 Edwards in
/-- **`u(u² + 486662u + 1)` is a square exactly when `u` is the Montgomery coordinate of a curve
point** (other than the neutral element). Also: `u = −1` and the roots of `u² + 486662u + 1`
(there are none) are not on the curve. **gen** (H-QR + H-GROUP; the lift's validity bit). -/
theorem montQ_square_iff (u : ZMod FieldDag.modulus) :
    (IsSquare (montQ u) ↔ ∃ P : Curve, P.y ≠ 1 ∧ montU P = u) ∧ ¬ IsSquare (montQ (-1)) ∧
      u ^ 2 + 486662 * u + 1 ≠ 0 :=
  ⟨TlsMpcProofs.Ed25519.montQ_isSquare_iff u,
    by rw [TlsMpcProofs.Ed25519.montQ_neg_one]; exact TlsMpcProofs.Ed25519.c486660_not_isSquare,
    TlsMpcProofs.Ed25519.montW_ne_zero u⟩

open Ed25519 in
/-- **What `valid = sel xor b = 1` means for the opened root:** `s² = q·r²`. **gen**. -/
theorem lift_root_relation {q r w s : ZMod FieldDag.modulus} {sel b : Bool}
    (hw : w = q * (r * r) * (if b then 2 else 1))
    (hs : if sel then s * s = w else 2 * (s * s) = w) (hv : (sel ^^ b) = true) :
    s * s = q * (r * r) :=
  TlsMpcProofs.Ed25519.lift_root hw hs hv

open Ed25519 Edwards EdwardsHinted in
/-- **`liftPoint` with `valid = 1` outputs a point `P` of the Edwards group with Montgomery
coordinate `u`, and `Z = M_A + M_B + P`.** **K-fn** (`lift-point`). -/
theorem liftPoint_valid_point (input : ℕ → FieldDag.F) {s : ZMod FieldDag.modulus} (hs0 : s ≠ 0)
    (h0 : TlsMpcProofs.toZMod (input 0) * s = sA2)
    (hsq : s * s = montQ (TlsMpcProofs.toZMod (input 2)) *
      (TlsMpcProofs.toZMod (input 3) * TlsMpcProofs.toZMod (input 3)))
    (hvalid : TlsMpcProofs.toZMod (input 1 + input 4 - FieldDag.ofNat 2 * (input 1 * input 4)) = 1)
    {MA MB : Curve} (hA : Affine (input 5, input 6) MA) (hB : Affine (input 7, input 8) MB) :
    ∃ (P : Curve) (val px py zx zy : FieldDag.F),
      (liftPoint ()).map (FieldDag.Expr.eval input) = [val, px, py, zx, zy] ∧
        TlsMpcProofs.toZMod val = 1 ∧ Affine (px, py) P ∧ montU P = TlsMpcProofs.toZMod (input 2) ∧
          P.y ≠ 1 ∧ Affine (zx, zy) (MA + MB + P) :=
  TlsMpcProofs.Ed25519.liftPoint_valid input hs0 h0 hsq hvalid hA hB

open Ed25519 EdwardsHinted in
/-- **`liftPoint` with `valid = 0` outputs the base point `B`, and `Z = M_A + M_B + B`.**
**K-fn**. -/
theorem liftPoint_invalid_point (input : ℕ → FieldDag.F)
    (hvalid : TlsMpcProofs.toZMod (input 1 + input 4 - FieldDag.ofNat 2 * (input 1 * input 4)) = 0)
    {MA MB : Curve} (hA : Affine (input 5, input 6) MA) (hB : Affine (input 7, input 8) MB) :
    ∃ (val px py zx zy : FieldDag.F),
      (liftPoint ()).map (FieldDag.Expr.eval input) = [val, px, py, zx, zy] ∧
        TlsMpcProofs.toZMod val = 0 ∧ Affine (px, py) B ∧ Affine (zx, zy) (MA + MB + B) :=
  TlsMpcProofs.Ed25519.liftPoint_invalid input hvalid hA hB

open Ed25519 Edwards in
/-- **X25519 of a lifted `u`** is the Montgomery coordinate of `k·P` for the lifted point.
**K-fn**. -/
theorem x25519_of_lift (input : ℕ → Bool) (u : FieldDag.F) {v : ZMod FieldDag.modulus}
    (hv : v * v = montQ (TlsMpcProofs.toZMod u)) (hv0 : v ≠ 0) :
    ∃ P : Curve, P.x = sA2 * TlsMpcProofs.toZMod u / v ∧
      P.y = (TlsMpcProofs.toZMod u - 1) / (TlsMpcProofs.toZMod u + 1) ∧
      TlsMpcProofs.toZMod (X25519.spec input u) = montU (clampedScalar input • P) :=
  TlsMpcProofs.Ed25519.x25519_lift input u hv hv0

end TlsMpcProofs.Security

/-! ## Machine checks -/

#print axioms TlsMpcProofs.Security.prime_modulus
#print axioms TlsMpcProofs.Security.prime_order
#print axioms TlsMpcProofs.Security.pocklington
#print axioms TlsMpcProofs.Security.toZMod_ofNat
#print axioms TlsMpcProofs.Security.toZMod_power
#print axioms TlsMpcProofs.Security.toZMod_inverse
#print axioms TlsMpcProofs.Security.two_not_square
#print axioms TlsMpcProofs.Security.euler_criterion
#print axioms TlsMpcProofs.Security.euler_nonsquare
#print axioms TlsMpcProofs.Security.sqrtMinusOne_eq_power
#print axioms TlsMpcProofs.Security.sqrtMinusOne_mul_self
#print axioms TlsMpcProofs.Security.candidate_fourth_iff
#print axioms TlsMpcProofs.Security.candidate_sq
#print axioms TlsMpcProofs.Security.recipient_check_zero_iff
#print axioms TlsMpcProofs.Security.recipient_x_mul_self
#print axioms TlsMpcProofs.Security.lift_select
#print axioms TlsMpcProofs.Security.liftOpen_square_iff
#print axioms TlsMpcProofs.Security.lift_fiber_card
#print axioms TlsMpcProofs.Security.lift_opened_uniform
#print axioms TlsMpcProofs.Security.lift_opened_uniform_xor
#print axioms TlsMpcProofs.Security.powBits_value
#print axioms TlsMpcProofs.Security.xeddsa_exponent_eq_power
#print axioms TlsMpcProofs.Security.x25519_inverse_eq
#print axioms TlsMpcProofs.Security.xeddsa_zero_eq_ite
#print axioms TlsMpcProofs.Security.xeddsa_recover_eq
#print axioms TlsMpcProofs.Security.xeddsa_run_recovery_eq
#print axioms TlsMpcProofs.Security.xeddsa_recover_valid_zero_or_one
#print axioms TlsMpcProofs.Security.xeddsa_recover_valid_iff
#print axioms TlsMpcProofs.Security.xeddsa_recover_x_mul_self
#print axioms TlsMpcProofs.Security.xeddsa_recover_x_mul_self_of_valid
#print axioms TlsMpcProofs.Security.xeddsa_recover_y
#print axioms TlsMpcProofs.Security.hiding_of_bijection
#print axioms TlsMpcProofs.Security.map_uniform_equiv
#print axioms TlsMpcProofs.Security.ghash_share_hides_dist
#print axioms TlsMpcProofs.Security.ghash_share_uniform
#print axioms TlsMpcProofs.Security.ceremony_masked_uniform
#print axioms TlsMpcProofs.Security.joint_random_uniform
#print axioms TlsMpcProofs.Security.bit_open_uniform
#print axioms TlsMpcProofs.Security.word_to_field_open_uniform
#print axioms TlsMpcProofs.Security.field_to_word_open_uniform
#print axioms TlsMpcProofs.Security.masked_inverse_open_uniform
#print axioms TlsMpcProofs.Security.maskedAgreement_mask_hides_dist
#print axioms TlsMpcProofs.Security.hinted_Z_uniform
#print axioms TlsMpcProofs.Security.offset_public_key_independent
#print axioms TlsMpcProofs.Security.offset_public_key_uniform
#print axioms TlsMpcProofs.Security.offset_public_keys_independent
#print axioms TlsMpcProofs.Security.offset_public_keys_uniform
#print axioms TlsMpcProofs.Security.eventClose_injective
#print axioms TlsMpcProofs.Security.statClose_uniform
#print axioms TlsMpcProofs.Security.deployedOffset_uniform
#print axioms TlsMpcProofs.Security.offset_cast_close_uniform
#print axioms TlsMpcProofs.Security.deployed_key_close
#print axioms TlsMpcProofs.Security.deployed_key_close_ideal
#print axioms TlsMpcProofs.Security.deployed_key_close_uniform
#print axioms TlsMpcProofs.Security.deployed_keys_close
#print axioms TlsMpcProofs.Security.order_gap_lt
#print axioms TlsMpcProofs.Security.ed25519_key_close
#print axioms TlsMpcProofs.Security.ed25519_key_close_uniform
#print axioms TlsMpcProofs.Security.ed25519_keys_close
#print axioms TlsMpcProofs.Security.fiber_mul_choose
#print axioms TlsMpcProofs.Security.undetected_count
#print axioms TlsMpcProofs.Security.undetected_count_zero
#print axioms TlsMpcProofs.Security.cut_and_bucket_probability
#print axioms TlsMpcProofs.Security.deployed_bound_t1
#print axioms TlsMpcProofs.Security.profile_256_bound_t1
#print axioms TlsMpcProofs.Security.profile_512_bound_t1
#print axioms TlsMpcProofs.Security.profile_1024_bound_t1
#print axioms TlsMpcProofs.Security.cut_bound_step
#print axioms TlsMpcProofs.Security.cut_bound_le_bound_one
#print axioms TlsMpcProofs.Security.undetected_lt_of_bound_t1
#print axioms TlsMpcProofs.Security.deployed_bound_all_t
#print axioms TlsMpcProofs.Security.profile_256_bound_all_t
#print axioms TlsMpcProofs.Security.profile_512_bound_all_t
#print axioms TlsMpcProofs.Security.profile_1024_bound_all_t
#print axioms TlsMpcProofs.Security.deployed_undetected_lt
#print axioms TlsMpcProofs.Security.profile_256_undetected_lt
#print axioms TlsMpcProofs.Security.profile_512_undetected_lt
#print axioms TlsMpcProofs.Security.profile_1024_undetected_lt
#print axioms TlsMpcProofs.Security.unpad_paddedWith_unique
#print axioms TlsMpcProofs.Security.unpad_decode_padded
#print axioms TlsMpcProofs.Security.unpad_decode_unpadded
#print axioms TlsMpcProofs.Security.unpad_decode_accepts_iff
#print axioms TlsMpcProofs.Security.edwards_d_not_square
#print axioms TlsMpcProofs.Security.edwards_neg_one_square
#print axioms TlsMpcProofs.Security.edwards_complete
#print axioms TlsMpcProofs.Security.edwards_operations
#print axioms TlsMpcProofs.Security.edwards_add_assoc
#print axioms TlsMpcProofs.Security.edwards_group_laws
#print axioms TlsMpcProofs.Security.pointAddValue_is_group_add
#print axioms TlsMpcProofs.Security.negate_is_group_neg
#print axioms TlsMpcProofs.Security.curveCheck_zero_iff
#print axioms TlsMpcProofs.Security.extAddValue_is_group_add
#print axioms TlsMpcProofs.Security.ext_affine_conversions
#print axioms TlsMpcProofs.Security.sumTreeValue_is_group_sum
#print axioms TlsMpcProofs.Security.extSumValue_is_group_sum
#print axioms TlsMpcProofs.Security.recipient_on_curve
#print axioms TlsMpcProofs.Security.xeddsa_recover_on_curve
#print axioms TlsMpcProofs.Security.base_order_nsmul
#print axioms TlsMpcProofs.Security.base_addOrderOf
#print axioms TlsMpcProofs.Security.curve_subgroup_card
#print axioms TlsMpcProofs.Security.curve_offset_public_key_uniform
#print axioms TlsMpcProofs.Security.curve_deployed_key_close
#print axioms TlsMpcProofs.Security.curve_deployed_key_close_uniform
#print axioms TlsMpcProofs.Security.curve_deployed_keys_close
#print axioms TlsMpcProofs.Security.base_deployed_key_close_uniform
#print axioms TlsMpcProofs.Security.curve_hinted_Z_uniform
#print axioms TlsMpcProofs.Security.curve_maskedAgreement_mask_hides
#print axioms TlsMpcProofs.Security.x25519_advance
#print axioms TlsMpcProofs.Security.x25519_spec_scalar_mult
#print axioms TlsMpcProofs.Security.x25519_clampedScalar_eq
#print axioms TlsMpcProofs.Security.x25519_clampedScalar_rfc
#print axioms TlsMpcProofs.Security.x25519_clampedScalar_bounds
#print axioms TlsMpcProofs.Security.x25519_u_zero
#print axioms TlsMpcProofs.Security.x25519_spec_scalar_mult_all
#print axioms TlsMpcProofs.Security.x25519_on_curve
#print axioms TlsMpcProofs.Security.window_multiples
#print axioms TlsMpcProofs.Security.window_table
#print axioms TlsMpcProofs.Security.prepareHinted_bit_entry
#print axioms TlsMpcProofs.Security.prepareHinted_initial_point
#print axioms TlsMpcProofs.Security.doublings_multiples
#print axioms TlsMpcProofs.Security.bitTable_entries
#print axioms TlsMpcProofs.Security.recode_encodes
#print axioms TlsMpcProofs.Security.recode_offset
#print axioms TlsMpcProofs.Security.signed_table_entry
#print axioms TlsMpcProofs.Security.offsetSum_scalar_mult
#print axioms TlsMpcProofs.Security.bitSum_is_x25519
#print axioms TlsMpcProofs.Security.xeddsa_add_is_group_add
#print axioms TlsMpcProofs.Security.xeddsa_doubleScalar
#print axioms TlsMpcProofs.Security.xeddsa_run_doubleScalar
#print axioms TlsMpcProofs.Security.montgomery_map_onCurve
#print axioms TlsMpcProofs.Security.montgomery_map_neg
#print axioms TlsMpcProofs.Security.montQ_square_iff
#print axioms TlsMpcProofs.Security.lift_root_relation
#print axioms TlsMpcProofs.Security.liftPoint_valid_point
#print axioms TlsMpcProofs.Security.liftPoint_invalid_point
#print axioms TlsMpcProofs.Security.x25519_of_lift
