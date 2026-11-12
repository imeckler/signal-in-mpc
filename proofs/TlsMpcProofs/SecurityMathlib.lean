import TlsMpcProofs.FieldBridge
import TlsMpcProofs.Prime25519
import TlsMpcProofs.Uniform
import TlsMpcProofs.QuadraticResidue
import TlsMpcProofs.Hiding
import TlsMpcProofs.CutAndChoose

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
  `t`, and numerically for `t = 1` for the deployed profiles. **Open:** that `t = 1` is the worst
  case (`check_parameters_128.py` checks all `t` numerically).
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
**M**. The other `t` are not covered (open item). -/
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

/-! ## 5. Open (comments only)

* `bound(t) ≤ bound(1)` for all `1 ≤ t ≤ N` at the deployed parameters (then
  `cut_and_bucket_probability` + `*_bound_t1` give "every bad set is undetected with probability
  below 2⁻¹²⁸"). `check_parameters_128.py` checks each `t` numerically.
* XEdDSA `recover` (`XEdDsaField.recover`): the same candidate argument as `recipient`, through
  `X25519.powBits` (needs a lemma "`powBits` is the power by the bits"); not done.
* H-GROUP; `idealCommit`; the C++ protocols themselves (P-CUT, P-HINT … as scripts, S9–S16).
* `offsetAgreement_public_key_independent` as probability: needs the offset uniform modulo the
  group order (`ZMod ℓ` scalars), not `Int`; not done.
-/

end TlsMpcProofs.Security

/-! ## Machine checks -/

#print axioms TlsMpcProofs.Security.prime_modulus
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
#print axioms TlsMpcProofs.Security.fiber_mul_choose
#print axioms TlsMpcProofs.Security.undetected_count
#print axioms TlsMpcProofs.Security.undetected_count_zero
#print axioms TlsMpcProofs.Security.cut_and_bucket_probability
#print axioms TlsMpcProofs.Security.deployed_bound_t1
#print axioms TlsMpcProofs.Security.profile_256_bound_t1
#print axioms TlsMpcProofs.Security.profile_512_bound_t1
#print axioms TlsMpcProofs.Security.profile_1024_bound_t1
