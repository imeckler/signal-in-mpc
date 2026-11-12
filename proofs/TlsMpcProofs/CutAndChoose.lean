import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Powerset
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The cut-and-choose counting bound (formerly P7)

`handshake_backend/EmpHybridWork/parameters.py` (`Parameters.bound`) and
`check_parameters_128.py` choose the bucket size `B` for `N` outputs from
`bound(t) = C(N, t) / C(M, B·t)`, `M = 2·B·N` candidates, and require it below `2⁻¹²⁸` for every
`t = 1 … N`. The argument behind it: the adversary fixes its set `S` of bad candidates before the
challenge (`idealCommit`); the challenge is a uniform permutation of the `M` positions; the
first `B·N` positions are opened (a bad one there aborts) and the rest form `N` buckets of `B`
(P-CUT(e): a bucket that mixes good and bad candidates aborts). So corruption goes undetected only
if `S` lands exactly on a nonempty union of whole buckets.

Proved here, for any finite set of positions and any family of `N` pairwise disjoint buckets of
size `B > 0` (`undetected_count`, `undetected_probability`), and for the protocol's layout
`Fin (B·N) ⊕ (Fin N × Fin B)` (`cut_and_bucket_probability`):

  #{π | π(S) is a union of whole buckets, S ≠ ∅} / M! = C(N, t) / C(M, B·t)   when |S| = B·t,

and `0` when `B ∤ |S|` (`undetected_count_zero`). That is exactly `parameters.py`'s
`bound(t)` (with equality, not just ≤). The single challenge permutation models the two
permutations of P-CUT steps 2–3 (cut, then bucket); their composition is again uniform.

Numerically (`deployed_bound_t1`, `profile_*_bound_t1`): `bound(1) < 2⁻¹²⁸` for the batch
profile of NEEDS_REVIEW 1.2 (`N = 2¹⁹`, `B = 8`) and for the three profiles of
`check_parameters_128.py` (256/14, 512/13, 1024/12). That `t = 1` is the worst case
(`bound(t) ≤ bound(1)` for all `1 ≤ t ≤ N`, any `B ≥ 2`), and hence the bound for every bad set,
is in `CutAndChooseAll.lean`.
-/

namespace TlsMpcProofs.CutAndChoose
open Finset Function

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The positions of `S` after the permutation `π`. -/
def place (π : Equiv.Perm α) (S : Finset α) : Finset α := S.map π.toEmbedding

theorem place_mul (τ π : Equiv.Perm α) (S : Finset α) : place (τ * π) S = (place π S).map τ.toEmbedding := by
  ext x
  simp [place]
  rfl

theorem card_place (π : Equiv.Perm α) (S : Finset α) : (place π S).card = S.card := card_map _

/-- The number of challenges putting `S` exactly on `T`. -/
def fiber (S T : Finset α) : ℕ := (univ.filter (fun π : Equiv.Perm α => place π S = T)).card

/-- A permutation carrying any set onto any other set of the same size. -/
theorem exists_perm_map_eq (T T' : Finset α) (h : T.card = T'.card) :
    ∃ τ : Equiv.Perm α, T.map τ.toEmbedding = T' := by
  classical
  have hc : Fintype.card {x // x ∈ T} = Fintype.card {x // x ∈ T'} := by
    simp [Fintype.card_coe, h]
  let e : {x // x ∈ T} ≃ {x // x ∈ T'} := Fintype.equivOfCardEq hc
  refine ⟨Equiv.extendSubtype e, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    exact Equiv.extendSubtype_mem e x hx
  · rw [card_map, h]

/-- **All placements of the same size are equally likely.** -/
theorem fiber_eq (S T T' : Finset α) (h : T.card = T'.card) : fiber S T = fiber S T' := by
  obtain ⟨τ, hτ⟩ := exists_perm_map_eq T T' h
  have hτ' : T'.map τ⁻¹.toEmbedding = T := by
    rw [← hτ]; ext x; simp [Equiv.Perm.inv_def]
  unfold fiber
  apply Finset.card_nbij' (fun π => τ * π) (fun π => τ⁻¹ * π)
  · intro π hπ
    simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hπ ⊢
    rw [place_mul, hπ, hτ]
  · intro π hπ
    simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hπ ⊢
    rw [place_mul, hπ, hτ']
  · intro π _; simp
  · intro π _; simp

/-- **Each placement of size `|S|` has probability `1 / C(|α|, |S|)`:**
`fiber · C(|α|, |S|) = |α|!`. -/
theorem fiber_mul_choose (S T : Finset α) (hT : T.card = S.card) :
    fiber S T * (Fintype.card α).choose S.card = (Fintype.card α).factorial := by
  classical
  have htot : (univ : Finset (Equiv.Perm α)).card =
      ∑ T' ∈ powersetCard S.card (univ : Finset α), fiber S T' := by
    apply Finset.card_eq_sum_card_fiberwise
    intro π _
    simp [mem_powersetCard, card_place]
  rw [card_univ, Fintype.card_perm] at htot
  rw [htot, Finset.sum_congr rfl (fun T' hT' => fiber_eq S T' T ?_), sum_const, card_powersetCard,
    card_univ, smul_eq_mul, mul_comm]
  rw [(mem_powersetCard.mp hT').2, hT]

/-! ### Buckets -/

variable {N B : ℕ}

/-- The union of the buckets in `J`. -/
def union (bucket : Fin N → Finset α) (J : Finset (Fin N)) : Finset α := J.biUnion bucket

theorem card_union (bucket : Fin N → Finset α) (hcard : ∀ j, (bucket j).card = B)
    (hdisj : Pairwise (Disjoint on bucket)) (J : Finset (Fin N)) : (union bucket J).card = B * J.card := by
  rw [union, card_biUnion (fun i _ j _ hij => hdisj hij)]
  simp [hcard, mul_comm]

theorem union_injective (bucket : Fin N → Finset α) (hcard : ∀ j, (bucket j).card = B) (hB : 0 < B)
    (hdisj : Pairwise (Disjoint on bucket)) : Function.Injective (union bucket) := by
  have sub : ∀ J J' : Finset (Fin N), union bucket J = union bucket J' → J ⊆ J' := by
    intro J J' h j hj
    obtain ⟨x, hx⟩ : (bucket j).Nonempty := by
      rw [← card_pos, hcard]; exact hB
    have hxJ : x ∈ union bucket J' := h ▸ (mem_biUnion.mpr ⟨j, hj, hx⟩)
    obtain ⟨j', hj', hx'⟩ := mem_biUnion.mp hxJ
    by_cases hjj : j = j'
    · exact hjj ▸ hj'
    · exact absurd (Finset.disjoint_left.mp (hdisj hjj) hx) (not_not.mpr hx')
  intro J J' h
  exact Finset.Subset.antisymm (sub J J' h) (sub J' J h.symm)

/-- The challenges under which the bad set `S` goes undetected: it lands exactly on a nonempty
union of whole buckets. -/
def undetected (bucket : Fin N → Finset α) (S : Finset α) : Finset (Equiv.Perm α) :=
  univ.filter (fun π => ∃ J : Finset (Fin N), J.Nonempty ∧ place π S = union bucket J)

/-- **The count:** for `|S| = B·t` with `t ≥ 1`,
`#undetected · C(|α|, B·t) = C(N, t) · |α|!`. -/
theorem undetected_count (bucket : Fin N → Finset α) (hcard : ∀ j, (bucket j).card = B) (hB : 0 < B)
    (hdisj : Pairwise (Disjoint on bucket)) (S : Finset α) (t : ℕ) (ht : 0 < t) (hS : S.card = B * t) :
    (undetected bucket S).card * (Fintype.card α).choose (B * t) =
      N.choose t * (Fintype.card α).factorial := by
  classical
  have hset : undetected bucket S =
      (powersetCard t (univ : Finset (Fin N))).biUnion
        (fun J => univ.filter (fun π : Equiv.Perm α => place π S = union bucket J)) := by
    ext π
    simp only [undetected, mem_filter, mem_univ, true_and, mem_biUnion, mem_powersetCard,
      subset_univ]
    constructor
    · rintro ⟨J, _, hJ⟩
      refine ⟨J, ?_, hJ⟩
      have := congrArg card hJ
      rw [card_place, card_union bucket hcard hdisj, hS] at this
      exact (Nat.eq_of_mul_eq_mul_left hB this).symm
    · rintro ⟨J, hJt, hJ⟩
      refine ⟨J, ?_, hJ⟩
      rw [← card_pos, hJt]; exact ht
  rw [hset, card_biUnion]
  · have hf : ∀ J ∈ powersetCard t (univ : Finset (Fin N)),
        (univ.filter (fun π : Equiv.Perm α => place π S = union bucket J)).card = fiber S (union bucket J) :=
      fun J _ => rfl
    rw [Finset.sum_congr rfl hf, Finset.sum_mul]
    have hc : ∀ J ∈ powersetCard t (univ : Finset (Fin N)),
        fiber S (union bucket J) * (Fintype.card α).choose (B * t) = (Fintype.card α).factorial := by
      intro J hJ
      rw [← hS]
      apply fiber_mul_choose
      rw [card_union bucket hcard hdisj, (mem_powersetCard.mp hJ).2, hS]
    rw [Finset.sum_congr rfl hc, sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul]
  · intro J _ J' _ hJJ
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro π h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    exact hJJ (union_injective bucket hcard hB hdisj (h1.symm.trans h2))

/-- **If `|S|` is not a multiple of `B` (or `S = ∅`), corruption is always detected.** -/
theorem undetected_count_zero (bucket : Fin N → Finset α) (hcard : ∀ j, (bucket j).card = B) (hB : 0 < B)
    (hdisj : Pairwise (Disjoint on bucket)) (S : Finset α) (hS : ¬ (B ∣ S.card) ∨ S = ∅) :
    undetected bucket S = ∅ := by
  ext π
  simp only [undetected, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro ⟨J, hJ, h⟩
  have hc := congrArg card h
  rw [card_place, card_union bucket hcard hdisj] at hc
  rcases hS with hS | rfl
  · exact hS ⟨J.card, hc⟩
  · rw [card_empty] at hc
    have : 0 < B * J.card := Nat.mul_pos hB hJ.card_pos
    omega

/-- **The probability, as `parameters.py`'s `bound(t)`.** -/
theorem undetected_probability (bucket : Fin N → Finset α) (hcard : ∀ j, (bucket j).card = B) (hB : 0 < B)
    (hdisj : Pairwise (Disjoint on bucket)) (S : Finset α) (t : ℕ) (ht : 0 < t) (hS : S.card = B * t)
    (hfit : B * t ≤ Fintype.card α) :
    ((undetected bucket S).card : ℚ) / (Fintype.card α).factorial =
      (N.choose t : ℚ) / (Fintype.card α).choose (B * t) := by
  have h := undetected_count bucket hcard hB hdisj S t ht hS
  have h1 : ((Fintype.card α).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : ((Fintype.card α).choose (B * t) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hfit).ne'
  rw [div_eq_div_iff h1 h2]
  exact_mod_cast h

/-! ### The protocol's layout: `B·N` opened positions, then `N` buckets of `B` -/

/-- Positions: the opened part `Fin (B·N)` and the bucket slots `Fin N × Fin B`. -/
abbrev Position (N B : ℕ) := Fin (B * N) ⊕ (Fin N × Fin B)

/-- Bucket `j`: its `B` slots. -/
def protocolBucket (N B : ℕ) (j : Fin N) : Finset (Position N B) :=
  (univ : Finset (Fin B)).map ⟨fun i => Sum.inr (j, i), fun a b h => by simpa using h⟩

theorem protocolBucket_card (j : Fin N) : (protocolBucket N B j).card = B := by
  simp [protocolBucket]

theorem protocolBucket_disjoint : Pairwise (Disjoint on protocolBucket N B) := by
  intro j j' hjj
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [protocolBucket, mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk] at hx hx'
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨i', h⟩ := hx'
  simp only [Sum.inr.injEq, Prod.mk.injEq] at h
  exact hjj h.1.symm

theorem position_card : Fintype.card (Position N B) = 2 * B * N := by
  simp [Fintype.card_sum, Fintype.card_prod]; ring

/-- **P7 for the protocol layout.** A bad set `S` of `B·t` candidates (`t ≥ 1`, fixed before the
uniform challenge permutation) goes undetected with probability exactly
`C(N, t) / C(2·B·N, B·t)` — `parameters.py`'s `bound(t)`. -/
theorem cut_and_bucket_probability (hB : 0 < B) (S : Finset (Position N B)) (t : ℕ) (ht : 0 < t)
    (htN : t ≤ N) (hS : S.card = B * t) :
    ((undetected (protocolBucket N B) S).card : ℚ) / (2 * B * N).factorial =
      (N.choose t : ℚ) / (2 * B * N).choose (B * t) := by
  have h := undetected_probability (protocolBucket N B) protocolBucket_card hB protocolBucket_disjoint S t ht hS
    (by rw [position_card]; nlinarith)
  rwa [position_card] at h

/-! ### The deployed parameters at `t = 1` (`bound(1) = N / C(2BN, B) < 2⁻¹²⁸`)

`C(n, k) · k! = n·(n−1)⋯(n−k+1)` (`Nat.descFactorial`), which the kernel evaluates directly. -/

theorem bound_t1_of_descFactorial (N B : ℕ)
    (h : 2 ^ 128 * N * B.factorial < (2 * B * N).descFactorial B) :
    2 ^ 128 * N.choose 1 < (2 * B * N).choose (B * 1) := by
  rw [Nat.choose_one_right, mul_one]
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h
  have hf : 0 < B.factorial := Nat.factorial_pos B
  by_contra hc
  push_neg at hc
  have h2 : B.factorial * (2 * B * N).choose B ≤ B.factorial * (2 ^ 128 * N) := Nat.mul_le_mul_left _ hc
  have e : B.factorial * (2 ^ 128 * N) = 2 ^ 128 * N * B.factorial := by ring
  rw [e] at h2
  exact absurd h (not_lt.mpr h2)

/-- Batch profile of NEEDS_REVIEW.md 1.2: `N = 2¹⁹`, `B = 8`. -/
theorem deployed_bound_t1 : 2 ^ 128 * (2 ^ 19).choose 1 < (2 * 8 * 2 ^ 19).choose (8 * 1) :=
  bound_t1_of_descFactorial _ _ (by decide)

/-- `check_parameters_128.py` profile 256 outputs, bucket 14. -/
theorem profile_256_bound_t1 : 2 ^ 128 * (256 : ℕ).choose 1 < (2 * 14 * 256).choose (14 * 1) :=
  bound_t1_of_descFactorial _ _ (by decide)

/-- `check_parameters_128.py` profile 512 outputs, bucket 13. -/
theorem profile_512_bound_t1 : 2 ^ 128 * (512 : ℕ).choose 1 < (2 * 13 * 512).choose (13 * 1) :=
  bound_t1_of_descFactorial _ _ (by decide)

/-- `check_parameters_128.py` profile 1024 outputs, bucket 12. -/
theorem profile_1024_bound_t1 : 2 ^ 128 * (1024 : ℕ).choose 1 < (2 * 12 * 1024).choose (12 * 1) :=
  bound_t1_of_descFactorial _ _ (by decide)

end TlsMpcProofs.CutAndChoose
