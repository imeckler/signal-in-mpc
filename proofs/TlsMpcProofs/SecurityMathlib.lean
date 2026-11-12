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
* **H-GROUP stays a hypothesis.** Where a statement needs "the points form a group" (P-HINT(c),
  the masked agreement) it is stated for any finite commutative group `G`; nothing proves that
  `pointAddValue` is such a group law.
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
`prepare`'s other outputs is not stated). Reading "square ⇔ on the curve, not the twist" needs
H-GROUP's formulas. -/
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
(H-QR; reading "square ⇔ on the curve" needs H-GROUP's formulas). -/
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

* H-GROUP (the Edwards formulas are a group law; also needed to read "`xx` is a square" as "on
  the curve"); `idealCommit`; the C++ protocols themselves (P-CUT, P-HINT … as scripts, S9–S16).
* Cut-and-choose: the model's detection rules (P-CUT(d), (e)) against `dyn_word_mask.h` /
  `dabit_generator.h`; that the two challenge permutations of P-CUT compose to one uniform one.
* Offset agreement: `idealCommit` (the peer's value independent of the honest party's, modelled as
  a fixed value; peer values chosen adaptively across messages are not covered); the two aborts
  that depend only on the offsets (`mine = peer`, offset `0`) are not modelled; H-GROUP.
* XEdDSA `recover`: the sign of `x` and its binding to the signature bit; `doubleScalar`.
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
