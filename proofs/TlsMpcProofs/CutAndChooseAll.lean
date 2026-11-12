import TlsMpcProofs.CutAndChoose
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Field.Basic

/-!
# The cut-and-choose bound for every number of bad buckets

`CutAndChoose.lean` proves that a bad set of `B·t` candidates goes undetected with probability
exactly `bound(t) = C(N, t) / C(2BN, B·t)` (`parameters.py`'s `Parameters.bound`), and that
`bound(1) < 2⁻¹²⁸` for the deployed profiles. This file closes the remaining gap:

* **`bound` is non-increasing in `t`** (`bound_step`): for every `N`, every `B ≥ 2` and every
  `1 ≤ t < N`, `bound(t + 1) ≤ bound(t)`, stated without division as
  `C(N, t+1)·C(2BN, Bt) ≤ C(N, t)·C(2BN, B(t+1))`. Hence `bound(t) ≤ bound(1)` for all
  `1 ≤ t ≤ N` (`bound_le_bound_one`): `t = 1` is the worst case, for all parameters with
  `B ≥ 2` (`parameters.py` only uses `bucket ≥ 2`), not only the deployed ones. So
  `exact_worst_bound` (`max over t`) is always attained at `t = 1`.
* **Every bad set** (any size, fixed before the challenge) goes undetected with probability
  below `2⁻¹²⁸` as soon as `bound(1) < 2⁻¹²⁸` (`undetected_lt_of_bound_t1`); sizes that are not a
  positive multiple of `B`, and `t > N`, have probability `0`.
* Instantiated for the batch profile `N = 2¹⁹`, `B = 8` and the three profiles of
  `check_parameters_128.py` (256/14, 512/13, 1024/12): `*_bound_all_t` (counting form) and
  `*_undetected_lt` (probability form).

Proof of the step, with `k = B·t`, `M = 2BN`, `s = N − t ≥ 1`: multiply both sides by
`(t+1)(k+1)(k+2)`; `C(N,t+1)(t+1) = C(N,t)(N−t)` and `C(M,k+2)(k+1)(k+2) = C(M,k)(M−k)(M−k−1)`;
`C(M,k+2) ≤ C(M,k+B)` because `k + B ≤ M/2`; what remains is
`s(k+1)(k+2) ≤ (t+1)(M−k)(M−k−1)`, which holds factor by factor:
`s(k+1) ≤ (t+1)(M−k)` and `k + 2 ≤ M − k − 1` (this one uses `B ≥ 2`).
-/

namespace TlsMpcProofs.CutAndChoose
open Finset

/-- `C(n, ·)` is non-decreasing up to `n/2`. -/
theorem choose_mono_left_half {n r s : ℕ} (hrs : r ≤ s) (hs : s ≤ n / 2) : n.choose r ≤ n.choose s := by
  revert hs
  induction s, hrs using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ s _ ih =>
    intro hs
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- **One step:** `bound(t + 1) ≤ bound(t)` for `B ≥ 2`, `t < N` (without division). -/
theorem bound_step (N B t : ℕ) (hB : 2 ≤ B) (htN : t < N) :
    N.choose (t + 1) * (2 * B * N).choose (B * t) ≤ N.choose t * (2 * B * N).choose (B * (t + 1)) := by
  obtain ⟨b, rfl⟩ : ∃ b, B = b + 2 := ⟨B - 2, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, N = t + 1 + s := ⟨N - t - 1, by omega⟩
  generalize hM : 2 * (b + 2) * (t + 1 + s) = M
  have hkB : (b + 2) * (t + 1) = (b + 2) * t + 1 + 1 + b := by ring
  rw [hkB]
  generalize hk : (b + 2) * t = k
  have hMk : M - k = k + 2 * (b + 2) * (s + 1) := by
    apply Nat.sub_eq_of_eq_add; rw [← hM, ← hk]; ring
  have hMk1 : M - (k + 1) = k + 2 * (b + 2) * s + 2 * b + 3 := by
    apply Nat.sub_eq_of_eq_add; rw [← hM, ← hk]; ring
  have hNt : t + 1 + s - t = s + 1 := by omega
  have h1 := Nat.choose_succ_right_eq (t + 1 + s) t
  rw [hNt] at h1
  have h2 := Nat.choose_succ_right_eq M k
  have h3 := Nat.choose_succ_right_eq M (k + 1)
  have h4 : M.choose (k + 1 + 1) ≤ M.choose (k + 1 + 1 + b) := by
    apply choose_mono_left_half (Nat.le_add_right _ _)
    have hM2 : M / 2 = (b + 2) * (t + 1 + s) := by
      rw [← hM, mul_assoc]; exact Nat.mul_div_cancel_left _ (by norm_num)
    rw [hM2, ← hk]
    calc (b + 2) * t + 1 + 1 + b ≤ (b + 2) * t + 1 + 1 + b + (b + 2) * s := Nat.le_add_right _ _
      _ = (b + 2) * (t + 1 + s) := by ring
  have p1 : (s + 1) * (k + 1) ≤ (t + 1) * (M - k) := by
    rw [hMk, ← hk]
    calc (s + 1) * ((b + 2) * t + 1) ≤ (s + 1) * ((b + 2) * t + 1) +
          ((b + 2) * t * t + (b + 2) * t * s + 2 * (b + 2) * t + (2 * b + 3) * s + (2 * b + 3)) :=
          Nat.le_add_right _ _
      _ = (t + 1) * ((b + 2) * t + 2 * (b + 2) * (s + 1)) := by ring
  have p2 : k + 1 + 1 ≤ M - (k + 1) := by
    rw [hMk1]; omega
  have hpos : 0 < (t + 1) * ((k + 1) * (k + 1 + 1)) := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc (t + 1 + s).choose (t + 1) * M.choose k * ((t + 1) * ((k + 1) * (k + 1 + 1)))
      = ((t + 1 + s).choose (t + 1) * (t + 1)) * (M.choose k * ((k + 1) * (k + 1 + 1))) := by ring
    _ = (t + 1 + s).choose t * ((s + 1) * (k + 1)) * (M.choose k * (k + 1 + 1)) := by rw [h1]; ring
    _ ≤ (t + 1 + s).choose t * ((t + 1) * (M - k)) * (M.choose k * (M - (k + 1))) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ p1) (Nat.mul_le_mul_left _ p2)
    _ = (t + 1 + s).choose t * (t + 1) * ((M.choose k * (M - k)) * (M - (k + 1))) := by ring
    _ = (t + 1 + s).choose t * (t + 1) * ((M.choose (k + 1) * (M - (k + 1))) * (k + 1)) := by
        rw [← h2]; ring
    _ = (t + 1 + s).choose t * (t + 1) * (M.choose (k + 1 + 1) * ((k + 1) * (k + 1 + 1))) := by
        rw [← h3]; ring
    _ ≤ (t + 1 + s).choose t * (t + 1) * (M.choose (k + 1 + 1 + b) * ((k + 1) * (k + 1 + 1))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h4)
    _ = (t + 1 + s).choose t * M.choose (k + 1 + 1 + b) * ((t + 1) * ((k + 1) * (k + 1 + 1))) := by
        ring

/-- **`t = 1` is the worst case:** `bound(t) ≤ bound(1)` for `1 ≤ t ≤ N`, `B ≥ 2`, i.e.
`C(N, t)·C(2BN, B) ≤ C(N, 1)·C(2BN, B·t)`. -/
theorem bound_le_bound_one (N B t : ℕ) (hB : 2 ≤ B) (ht : 1 ≤ t) (htN : t ≤ N) :
    N.choose t * (2 * B * N).choose (B * 1) ≤ N.choose 1 * (2 * B * N).choose (B * t) := by
  revert htN
  induction t, ht using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ t ht ih =>
    intro htN
    have ih' := ih (by omega)
    have hs := bound_step N B t hB (by omega)
    have hpos : 0 < (2 * B * N).choose (B * t) := Nat.choose_pos (by nlinarith)
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc N.choose (t + 1) * (2 * B * N).choose (B * 1) * (2 * B * N).choose (B * t)
        = (N.choose (t + 1) * (2 * B * N).choose (B * t)) * (2 * B * N).choose (B * 1) := by ring
      _ ≤ (N.choose t * (2 * B * N).choose (B * (t + 1))) * (2 * B * N).choose (B * 1) :=
          Nat.mul_le_mul_right _ hs
      _ = (N.choose t * (2 * B * N).choose (B * 1)) * (2 * B * N).choose (B * (t + 1)) := by ring
      _ ≤ (N.choose 1 * (2 * B * N).choose (B * t)) * (2 * B * N).choose (B * (t + 1)) :=
          Nat.mul_le_mul_right _ ih'
      _ = N.choose 1 * (2 * B * N).choose (B * (t + 1)) * (2 * B * N).choose (B * t) := by ring

/-- **From `t = 1` to every `t`:** if `bound(1) < 2⁻¹²⁸` then `bound(t) < 2⁻¹²⁸` for every
`1 ≤ t ≤ N` (`B ≥ 2`). -/
theorem bound_all_t_of_t1 {N B : ℕ} (hB : 2 ≤ B) (h1 : 2 ^ 128 * N.choose 1 < (2 * B * N).choose (B * 1))
    (t : ℕ) (ht : 1 ≤ t) (htN : t ≤ N) : 2 ^ 128 * N.choose t < (2 * B * N).choose (B * t) := by
  have hmono := bound_le_bound_one N B t hB ht htN
  have hpos : 0 < (2 * B * N).choose (B * t) := Nat.choose_pos (by nlinarith)
  have hlt : 2 ^ 128 * N.choose t * (2 * B * N).choose (B * 1) <
      (2 * B * N).choose (B * t) * (2 * B * N).choose (B * 1) := by
    calc 2 ^ 128 * N.choose t * (2 * B * N).choose (B * 1)
        = 2 ^ 128 * (N.choose t * (2 * B * N).choose (B * 1)) := by ring
      _ ≤ 2 ^ 128 * (N.choose 1 * (2 * B * N).choose (B * t)) := Nat.mul_le_mul_left _ hmono
      _ = (2 ^ 128 * N.choose 1) * (2 * B * N).choose (B * t) := by ring
      _ < (2 * B * N).choose (B * 1) * (2 * B * N).choose (B * t) := Nat.mul_lt_mul_of_pos_right h1 hpos
      _ = (2 * B * N).choose (B * t) * (2 * B * N).choose (B * 1) := by ring
  exact Nat.lt_of_mul_lt_mul_right hlt

/-- **Every bad set, every size:** if `bound(1) < 2⁻¹²⁸` (and `B ≥ 2`), any set `S` of bad
candidates fixed before the uniform challenge permutation goes undetected with probability
below `2⁻¹²⁸`. (`|S| = B·t` with `1 ≤ t ≤ N`: `cut_and_bucket_probability` and
`bound_all_t_of_t1`; `t > N`, `B ∤ |S|` or `S = ∅`: probability `0`.) -/
theorem undetected_lt_of_bound_t1 {N B : ℕ} (hB : 2 ≤ B)
    (h1 : 2 ^ 128 * N.choose 1 < (2 * B * N).choose (B * 1)) (S : Finset (Position N B)) :
    ((undetected (protocolBucket N B) S).card : ℚ) / (2 * B * N).factorial < 1 / 2 ^ 128 := by
  have hB0 : 0 < B := by omega
  have hzero : (undetected (protocolBucket N B) S).card = 0 →
      ((undetected (protocolBucket N B) S).card : ℚ) / (2 * B * N).factorial < 1 / 2 ^ 128 := by
    intro h; rw [h, Nat.cast_zero, zero_div]; positivity
  by_cases hdiv : B ∣ S.card ∧ S ≠ ∅
  · obtain ⟨⟨t, ht⟩, hne⟩ := hdiv
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · exfalso; apply hne; rw [← Finset.card_eq_zero, ht, h, mul_zero]
      · exact h
    have hle : S.card ≤ Fintype.card (Position N B) := Finset.card_le_univ S
    by_cases htN : t ≤ N
    · rw [cut_and_bucket_probability hB0 S t htpos htN ht]
      have hc : 0 < (2 * B * N).choose (B * t) := Nat.choose_pos (by rw [← ht, ← position_card]; exact hle)
      have hlt := bound_all_t_of_t1 hB h1 t htpos htN
      rw [div_lt_div_iff₀ (by exact_mod_cast hc) (by positivity), one_mul, mul_comm]
      exact_mod_cast hlt
    · apply hzero
      have hcnt := undetected_count (protocolBucket N B) protocolBucket_card hB0 protocolBucket_disjoint
        S t htpos ht
      rw [Nat.choose_eq_zero_of_lt (show N < t by omega), zero_mul] at hcnt
      have hc : 0 < (Fintype.card (Position N B)).choose (B * t) := Nat.choose_pos (by rw [← ht]; exact hle)
      exact (Nat.mul_eq_zero.mp hcnt).resolve_right hc.ne'
  · apply hzero
    have hS : ¬ (B ∣ S.card) ∨ S = ∅ := by
      by_cases h : B ∣ S.card
      · right; by_contra h'; exact hdiv ⟨h, h'⟩
      · left; exact h
    rw [undetected_count_zero (protocolBucket N B) protocolBucket_card hB0 protocolBucket_disjoint S hS,
      Finset.card_empty]

/-! ### The deployed profiles, every `t` -/

/-- Batch profile (`N = 2¹⁹`, `B = 8`): `bound(t) < 2⁻¹²⁸` for every `1 ≤ t ≤ N`. -/
theorem deployed_bound_all_t (t : ℕ) (ht : 1 ≤ t) (htN : t ≤ 2 ^ 19) :
    2 ^ 128 * (2 ^ 19).choose t < (2 * 8 * 2 ^ 19).choose (8 * t) :=
  bound_all_t_of_t1 (by norm_num) deployed_bound_t1 t ht htN

/-- Profile 256/14: `bound(t) < 2⁻¹²⁸` for every `1 ≤ t ≤ 256`. -/
theorem profile_256_bound_all_t (t : ℕ) (ht : 1 ≤ t) (htN : t ≤ 256) :
    2 ^ 128 * (256 : ℕ).choose t < (2 * 14 * 256).choose (14 * t) :=
  bound_all_t_of_t1 (by norm_num) profile_256_bound_t1 t ht htN

/-- Profile 512/13: `bound(t) < 2⁻¹²⁸` for every `1 ≤ t ≤ 512`. -/
theorem profile_512_bound_all_t (t : ℕ) (ht : 1 ≤ t) (htN : t ≤ 512) :
    2 ^ 128 * (512 : ℕ).choose t < (2 * 13 * 512).choose (13 * t) :=
  bound_all_t_of_t1 (by norm_num) profile_512_bound_t1 t ht htN

/-- Profile 1024/12: `bound(t) < 2⁻¹²⁸` for every `1 ≤ t ≤ 1024`. -/
theorem profile_1024_bound_all_t (t : ℕ) (ht : 1 ≤ t) (htN : t ≤ 1024) :
    2 ^ 128 * (1024 : ℕ).choose t < (2 * 12 * 1024).choose (12 * t) :=
  bound_all_t_of_t1 (by norm_num) profile_1024_bound_t1 t ht htN

/-- **Batch profile, as a probability:** any bad set goes undetected with probability `< 2⁻¹²⁸`. -/
theorem deployed_undetected_lt (S : Finset (Position (2 ^ 19) 8)) :
    ((undetected (protocolBucket (2 ^ 19) 8) S).card : ℚ) / (2 * 8 * 2 ^ 19).factorial < 1 / 2 ^ 128 :=
  undetected_lt_of_bound_t1 (by norm_num) deployed_bound_t1 S

/-- Profile 256/14, as a probability. -/
theorem profile_256_undetected_lt (S : Finset (Position 256 14)) :
    ((undetected (protocolBucket 256 14) S).card : ℚ) / (2 * 14 * 256).factorial < 1 / 2 ^ 128 :=
  undetected_lt_of_bound_t1 (by norm_num) profile_256_bound_t1 S

/-- Profile 512/13, as a probability. -/
theorem profile_512_undetected_lt (S : Finset (Position 512 13)) :
    ((undetected (protocolBucket 512 13) S).card : ℚ) / (2 * 13 * 512).factorial < 1 / 2 ^ 128 :=
  undetected_lt_of_bound_t1 (by norm_num) profile_512_bound_t1 S

/-- Profile 1024/12, as a probability. -/
theorem profile_1024_undetected_lt (S : Finset (Position 1024 12)) :
    ((undetected (protocolBucket 1024 12) S).card : ℚ) / (2 * 12 * 1024).factorial < 1 / 2 ^ 128 :=
  undetected_lt_of_bound_t1 (by norm_num) profile_1024_bound_t1 S

end TlsMpcProofs.CutAndChoose
