import TlsMpcProofs.FieldBridge
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.GroupTheory.OrderOfElement

/-!
# `2²⁵⁵ − 19` is prime

Mathlib does not know this, and neither `decide` nor `norm_num` can test a 255-bit number by
trial division. The proof is a **Pocklington certificate** checked by the kernel:

* `pocklington_step` (proved here from Mathlib's `orderOf` and `ZMod` lemmas): if `q` is prime,
  `q^k ∣ N − 1`, `a^(N−1) ≡ 1 (mod N)` and `gcd(a^((N−1)/q) − 1, N) = 1`, then every prime divisor
  `r` of `N` has `q^k ∣ r − 1`.
* `pocklington`: if that holds for a list of distinct primes whose prime powers multiply to
  `F` with `N ≤ F²`, then `N` is prime (every prime factor exceeds `√N`).
* The modular powers and gcds are computed by `powMod` (square-and-multiply on `Nat`,
  `FieldBridge`) and checked with `decide +kernel`, i.e. by the kernel's GMP-accelerated `Nat`
  arithmetic. No `native_decide`, no new axiom.

The chain (found by `.deps/lowering-scratch/pocklington_cert.py`, with one factor of `Q − 1` found
by elliptic-curve factoring; the certificate needs only the factored part, not the cofactor):

* `p − 1 = 4 · 3 · 65147 · Q`, `Q = 74058…40907` (236 bits): certify `p` with `F = Q`, base 2.
* `Q − 1` has factored part `2 · 353 · 57467 · 132049 · 1923133 · 31757755568855353` (118 bits,
  its square exceeds `Q`), base 2 for every factor.
* `31757755568855353 − 1` has factored part `2³ · 3 · 31 · 107 · 4153`; bases 5 (for 2) and 2.
* The remaining primes are below 2·10⁶ and are proved by `norm_num`.
-/

namespace TlsMpcProofs

/-- If `q^k ∣ n`, `o ∣ n` and `o ∤ n/q`, then `q^k ∣ o` (`q` prime, `n ≠ 0`). -/
theorem prime_pow_dvd_of_not_dvd_div {q k n o : ℕ} (hq : q.Prime) (hn : n ≠ 0)
    (hqk : q ^ k ∣ n) (ho : o ∣ n) (hnot : ¬ o ∣ n / q) : q ^ k ∣ o := by
  have ho0 : o ≠ 0 := by rintro rfl; exact hn (Nat.eq_zero_of_zero_dvd ho)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hqn : q ∣ n := (dvd_pow_self q hk.ne').trans hqk
  rw [hq.pow_dvd_iff_le_factorization ho0]
  by_contra hlt
  push_neg at hlt
  apply hnot
  have hnq0 : n / q ≠ 0 := by
    have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hqn) hq.pos
    omega
  rw [← Nat.factorization_le_iff_dvd ho0 hnq0, Nat.factorization_div hqn, hq.factorization,
    Finsupp.le_def]
  intro s
  have hle := Finsupp.le_def.mp ((Nat.factorization_le_iff_dvd ho0 hn).mpr ho) s
  have hkn := (hq.pow_dvd_iff_le_factorization hn).mp hqk
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
  split_ifs with h
  · subst h; omega
  · omega

/-- **Pocklington, one prime power.** -/
theorem pocklington_step {N q k a : ℕ} (hN : 1 < N) (hN' : N < 2 ^ 256) (hq : q.Prime)
    (hqk : q ^ k ∣ N - 1) (ha : powMod a (N - 1) N = 1)
    (hg : Nat.gcd (powMod a ((N - 1) / q) N - 1) N = 1)
    {r : ℕ} (hr : r.Prime) (hrN : r ∣ N) : q ^ k ∣ r - 1 := by
  haveI := Fact.mk hr
  have cast : ∀ e, e < 2 ^ 256 → (a : ZMod r) ^ e = ((powMod a e N : ℕ) : ZMod r) := by
    intro e he
    have h := congrArg (ZMod.castHom hrN (ZMod r)) (zmod_pow_eq_powMod (m := N) a e he)
    simpa only [map_pow, map_natCast] using h
  have hx1 : (a : ZMod r) ^ (N - 1) = 1 := by
    rw [cast _ (by omega), ha, Nat.cast_one]
  have hx0 : (a : ZMod r) ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega)] at hx1
    exact zero_ne_one hx1
  have hxq : (a : ZMod r) ^ ((N - 1) / q) ≠ 1 := by
    intro h1
    rw [cast _ (by have := Nat.div_le_self (N - 1) q; omega)] at h1
    have hy : 1 ≤ powMod a ((N - 1) / q) N := by
      rcases Nat.eq_zero_or_pos (powMod a ((N - 1) / q) N) with h0 | h0
      · rw [h0, Nat.cast_zero] at h1; exact absurd h1 zero_ne_one
      · exact h0
    have hdvd : r ∣ powMod a ((N - 1) / q) N - 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hy, h1, Nat.cast_one, sub_self]
    have h2 : r ∣ Nat.gcd (powMod a ((N - 1) / q) N - 1) N := Nat.dvd_gcd hdvd hrN
    rw [hg] at h2
    exact hr.one_lt.ne' (Nat.dvd_one.mp h2)
  have hord : orderOf (a : ZMod r) ∣ N - 1 := orderOf_dvd_of_pow_eq_one hx1
  have hnot : ¬ orderOf (a : ZMod r) ∣ (N - 1) / q := fun h => hxq (orderOf_dvd_iff_pow_eq_one.mp h)
  exact (prime_pow_dvd_of_not_dvd_div hq (by omega) hqk hord hnot).trans
    (ZMod.orderOf_dvd_card_sub_one hx0)

/-- The computable part of a certificate entry `(q, k, a)`. -/
def entryOk (N : ℕ) (c : ℕ × ℕ × ℕ) : Bool :=
  (N - 1) % (c.1 ^ c.2.1) == 0 && powMod c.2.2 (N - 1) N == 1 &&
    Nat.gcd (powMod c.2.2 ((N - 1) / c.1) N - 1) N == 1

/-- The factored part `F = ∏ q^k` of a certificate. -/
def certF (cert : List (ℕ × ℕ × ℕ)) : ℕ := (cert.map fun c => c.1 ^ c.2.1).prod

/-- Everything about a certificate that the kernel checks by evaluation. -/
def certOk (N : ℕ) (cert : List (ℕ × ℕ × ℕ)) : Bool :=
  decide (1 < N) && decide (N < 2 ^ 256) && cert.all (entryOk N) &&
    decide ((cert.map Prod.fst).Nodup) && decide (N ≤ certF cert ^ 2)

theorem certF_dvd {m : ℕ} : ∀ (cert : List (ℕ × ℕ × ℕ)), (∀ c ∈ cert, c.1.Prime) →
    (cert.map Prod.fst).Nodup → (∀ c ∈ cert, c.1 ^ c.2.1 ∣ m) → certF cert ∣ m
  | [], _, _, _ => by simp [certF]
  | c :: rest, hp, hnd, hd => by
    simp only [certF, List.map_cons, List.prod_cons] at *
    simp only [List.mem_cons, forall_eq_or_imp] at hp hd
    rw [List.nodup_cons] at hnd
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd _ hd.1 (certF_dvd rest hp.2 hnd.2 hd.2)
    unfold certF
    rw [Nat.coprime_list_prod_right_iff]
    intro n hn
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hn
    apply Nat.Coprime.pow
    rw [Nat.coprime_primes hp.1 (hp.2 c' hc')]
    rintro heq
    exact hnd.1 (heq ▸ List.mem_map_of_mem hc')

/-- **Pocklington's criterion.** A checked certificate whose factors are prime proves `N` prime. -/
theorem pocklington (N : ℕ) (cert : List (ℕ × ℕ × ℕ)) (hok : certOk N cert = true)
    (hp : ∀ c ∈ cert, c.1.Prime) : N.Prime := by
  simp only [certOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨hN, hN'⟩, hall⟩, hnd⟩, hsize⟩ := hok
  have hdiv : ∀ r, r.Prime → r ∣ N → certF cert ∣ r - 1 := by
    intro r hr hrN
    apply certF_dvd cert hp hnd
    intro c hc
    have he := hall c hc
    simp only [entryOk, Bool.and_eq_true, beq_iff_eq] at he
    obtain ⟨⟨hmod, ha⟩, hg⟩ := he
    exact pocklington_step hN hN' (hp c hc) (Nat.dvd_of_mod_eq_zero hmod) ha hg hr hrN
  by_contra hnp
  have hN1 : N ≠ 1 := by omega
  have hr := Nat.minFac_prime hN1
  have hF := Nat.le_of_dvd (by have := hr.two_le; omega) (hdiv _ hr (Nat.minFac_dvd N))
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hlt : certF cert < N.minFac := by have := hr.two_le; omega
  have hlt2 : certF cert ^ 2 < N.minFac ^ 2 := by gcongr
  exact absurd (lt_of_le_of_lt hsize hlt2) (not_lt.mpr hsq)

/-! ### The chain for `2²⁵⁵ − 19` -/

/-- A 55-bit prime factor of `Q − 1`. -/
theorem prime_31757755568855353 : Nat.Prime 31757755568855353 :=
  pocklington 31757755568855353 [(2, 3, 5), (3, 1, 2), (31, 1, 2), (107, 1, 2), (4153, 1, 2)]
    (by decide +kernel) (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro c (rfl | rfl | rfl | rfl | rfl) <;> norm_num)

/-- `Q`, the 236-bit prime factor of `p − 1`. -/
theorem prime_Q : Nat.Prime 74058212732561358302231226437062788676166966415465897661863160754340907 :=
  pocklington _ [(2, 1, 2), (353, 1, 2), (57467, 1, 2), (132049, 1, 2), (1923133, 1, 2),
      (31757755568855353, 1, 2)]
    (by decide +kernel)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro c (rfl | rfl | rfl | rfl | rfl | rfl)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · exact prime_31757755568855353)

/-- **`p = 2²⁵⁵ − 19` (the main package's `FieldDag.modulus`) is prime.** -/
theorem prime_modulus : Nat.Prime TlsMpc.FieldDag.modulus :=
  pocklington _ [(74058212732561358302231226437062788676166966415465897661863160754340907, 1, 2)]
    (by decide +kernel)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro c rfl
      exact prime_Q)

instance fact_prime_modulus : Fact (Nat.Prime TlsMpc.FieldDag.modulus) := ⟨prime_modulus⟩

end TlsMpcProofs
