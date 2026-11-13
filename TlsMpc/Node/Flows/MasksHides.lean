import TlsMpc.Node.Flows.MasksHiding

/-!
# P-CUT (c) in plan 7.0's form: `generate_hides`

REORGANIZATION_PLAN.md 7.0, 7.1 P-CUT (c); stage S10. Plan 7.0: for an honest party with secret s
and randomness ρ, and every adversary: for any other secret s′ there is a bijection Σ on the
randomness such that the transcript of (s, ρ) equals that of (s′, Σ ρ).

For `Masks.generate` the randomness is the honest party's M candidates `r` (canonical values; its
challenge randomness is fixed: the statement holds for each value of it) and the "secret" is where
its kept references end up. The experiment is `hideView δ r`: the adversary's view of the run with
candidates `r`, TOGETHER WITH the kept references moved by `δ` (`moveRef`: a rotation of [0, p) by
`δ j` for a word mask's reference; of [32, p) for a bit block's, whose flag says "at least 32").

  `generate_hides`:  hideView δ r = hideView 0 (reRand π δ r)       (π: the challenges of r's run)

`reRand π δ` is the re-randomisation Σ: every kept reference is moved by `δ` and every other member
of its bucket by the opposite amount mod p; the cut candidates are untouched. It is a bijection of
the canonical candidate vectors: `reRand_lt` (it yields canonical values), `reRand_inverse`
(`reRand (negShift δ)` undoes it; the challenges of the re-randomised run are the same, which is
part of the statement), `moveRef_negneg`. And any target is reached: `moveRef_reach_word`,
`moveRef_reach_bits`. So with uniform candidates the pair (view, kept references) has the same
distribution as (view, kept references moved by δ), for every δ: given the view, the honest
party's kept references are uniform (on [0, p), resp. [32, p)) — the form
`proofs/TlsMpcProofs/Uniform.lean` `hiding_of_bijection` consumes (view := `hideView`, s := δ,
s′ := 0, σ := `reRand π δ`).

All of it against any adversary, from any engine state and prior adversary view, for every
parameter set with `0 < M` and `bits ≤ N` (so the deployed profiles), under `WordLoaded` and
`ProgsLoaded` (the circuits and programs named compute their Lean definitions) and 32-byte hashes.
-/

namespace TlsMpc.Node.Flows.Masks

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs openThen frees Silent blankWire Leaves seqs_cons seqs_nil)
open TlsMpc.Node.Flows.Run
open TlsMpc.Node.Flows.Conv
open TlsMpc.FieldDag (F modulus)

/-! ## Moving a kept reference -/

theorem P_sub : P - 32 = 57896044618658097711785492504343953926634992332820282019728792003956564819917 := by
  decide

/-- **The new value of a kept reference**: a rotation by `δ` of [0, p) (a word mask's reference),
or of [32, p) (a bit block's reference: the flag phase reveals whether it is at least 32; a
reference below 32 stays, and its run aborts at the flags). -/
def moveRef (isBit : Bool) (δ v : Nat) : Nat :=
  if isBit then (if 32 ≤ v then 32 + (v - 32 + δ) % (P - 32) else v) else (v + δ) % P

/-- The amount that undoes `δ`. -/
def negAmt (isBit : Bool) (δ : Nat) : Nat := if isBit then (P - 32) - δ % (P - 32) else P - δ % P

theorem moveRef_lt (b : Bool) (δ v : Nat) (hv : v < P) : moveRef b δ v < P := by
  unfold moveRef
  rw [P_sub]
  rw [P_eq] at *
  cases b
  · simp only [Bool.false_eq_true, if_false]
    omega
  · simp only [if_true]
    split <;> omega

/-- **`moveRef` is a bijection** of the canonical values: `negAmt` undoes it. -/
theorem moveRef_neg (b : Bool) (δ v : Nat) (hv : v < P) : moveRef b (negAmt b δ) (moveRef b δ v) = v := by
  unfold moveRef negAmt
  rw [P_sub]
  rw [P_eq] at *
  cases b
  · simp only [Bool.false_eq_true, if_false]
    omega
  · simp only [if_true]
    by_cases h : 32 ≤ v
    · rw [if_pos h, if_pos (by omega)]
      omega
    · rw [if_neg h, if_neg h]

theorem moveRef_negneg (b : Bool) (δ v : Nat) : moveRef b (negAmt b (negAmt b δ)) v = moveRef b δ v := by
  unfold moveRef negAmt
  rw [P_sub]
  rw [P_eq]
  cases b
  · simp only [Bool.false_eq_true, if_false]
    omega
  · simp only [if_true]
    split <;> omega

theorem moveRef_zero (b : Bool) (v : Nat) (hv : v < P) : moveRef b 0 v = v := by
  unfold moveRef
  rw [P_sub]
  rw [P_eq] at *
  cases b
  · simp only [Bool.false_eq_true, if_false]
    omega
  · simp only [if_true]
    split <;> omega

/-- A bit block's reference is at least 32 after the move iff it was before. -/
theorem moveRef_32 (δ v : Nat) : 32 ≤ moveRef true δ v ↔ 32 ≤ v := by
  unfold moveRef
  simp only [if_true]
  split <;> omega

/-- **Any target is reached** (word masks): from `v` to any canonical `t`. -/
theorem moveRef_reach_word (v t : Nat) (hv : v < P) (ht : t < P) : moveRef false ((t + (P - v)) % P) v = t := by
  unfold moveRef
  simp only [Bool.false_eq_true, if_false]
  rw [P_eq] at *
  omega

/-- **Any target is reached** (bit blocks): from `v` to any `t`, both in [32, p). -/
theorem moveRef_reach_bits (v t : Nat) (hv : v < P) (hv32 : 32 ≤ v) (ht : t < P) (ht32 : 32 ≤ t) :
    moveRef true ((t - 32 + (P - 32 - (v - 32))) % (P - 32)) v = t := by
  unfold moveRef
  simp only [if_true]
  rw [P_sub]
  rw [P_eq] at *
  rw [if_pos hv32]
  omega

/-! ## Bucket positions -/

/-- The bucket positions (bucket `j`, member `k`). -/
def positions (p : Params) : List (Nat × Nat) :=
  (List.range p.N).flatMap fun j => (List.range p.B).map fun k => (j, k)

theorem mem_positions (p : Params) (e : Nat × Nat) : e ∈ positions p ↔ e.1 < p.N ∧ e.2 < p.B := by
  simp only [positions, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, k, hk, rfl⟩
    exact ⟨hj, hk⟩
  · rintro ⟨h1, h2⟩
    exact ⟨e.1, h1, e.2, h2, rfl⟩

/-- The bucket position of candidate `c`, if it is a reference or a member. -/
def posOf (p : Params) (π₁ π₂ : List Nat) (c : Nat) : Option (Nat × Nat) :=
  (positions p).find? fun e => member p π₁ π₂ e.1 e.2 == c

/-- The two challenges' permutations (P-CHAL (b)). -/
structure Perms (p : Params) (π₁ π₂ : List Nat) : Prop where
  h1 : PermSpec p.M π₁
  h2 : PermSpec p.K π₂

theorem getD_mem' (l : List Nat) (i : Nat) (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem _

theorem nodup_getD_inj : ∀ (l : List Nat), l.Nodup → ∀ i j, i < l.length → j < l.length →
    l.getD i 0 = l.getD j 0 → i = j
  | [], _, i, _, hi, _, _ => by simp at hi
  | a :: l, hn, i, j, hi, hj, h => by
    rw [List.nodup_cons] at hn
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        exfalso
        simp only [List.getD_cons_zero, List.getD_cons_succ] at h
        exact hn.1 (h ▸ getD_mem' l j (by simpa using hj))
    | succ i =>
      cases j with
      | zero =>
        exfalso
        simp only [List.getD_cons_zero, List.getD_cons_succ] at h
        exact hn.1 (h ▸ getD_mem' l i (by simpa using hi))
      | succ j =>
        simp only [List.getD_cons_succ] at h
        rw [nodup_getD_inj l hn.2 i j (by simpa using hi) (by simpa using hj) h]

theorem find?_unique {α : Type} (P : α → Bool) (a : α) : ∀ (l : List α), a ∈ l → P a = true →
    (∀ y ∈ l, P y = true → y = a) → l.find? P = some a
  | [], ha, _, _ => by simp at ha
  | y :: l, ha, hP, hu => by
    by_cases hy : P y = true
    · have := hu y (by simp) hy
      subst this
      simp [hy]
    · have hy' : P y = false := by simpa using hy
      simp only [List.find?_cons, hy']
      have hne : a ≠ y := fun e => hy (e ▸ hP)
      have ha' : a ∈ l := by
        simp only [List.mem_cons] at ha
        rcases ha with h | h
        · exact absurd h hne
        · exact h
      exact find?_unique P a l ha' hP (fun z hz => hu z (by simp [hz]))

theorem idx_lt (p : Params) (j k : Nat) (hj : j < p.N) (hk : k < p.B) : p.B * j + k < p.K := by
  have := Nat.mul_le_mul_left p.B (show j + 1 ≤ p.N by omega)
  rw [Nat.mul_succ] at this
  unfold Params.K
  omega

theorem idx_inj (B j k j' k' : Nat) (hk : k < B) (hk' : k' < B) (h : B * j + k = B * j' + k') :
    j = j' ∧ k = k' := by
  rcases Nat.lt_trichotomy j j' with hlt | heq | hgt
  · have := Nat.mul_le_mul_left B (show j + 1 ≤ j' by omega)
    rw [Nat.mul_succ] at this
    omega
  · subst heq
    exact ⟨rfl, by omega⟩
  · have := Nat.mul_le_mul_left B (show j' + 1 ≤ j by omega)
    rw [Nat.mul_succ] at this
    omega

section Positions

variable {p : Params} {π₁ π₂ : List Nat}

theorem remain_spec (hp : Perms p π₁ π₂) :
    (remainOf p π₁).length = p.K ∧ (remainOf p π₁).Nodup := by
  have hM : p.M = 2 * p.K := rfl
  refine ⟨?_, hp.h1.2.1.sublist (List.drop_sublist _ _)⟩
  unfold remainOf
  rw [List.length_drop, hp.h1.1]
  omega

theorem member_mem_remain (hp : Perms p π₁ π₂) (j k : Nat) (hj : j < p.N) (hk : k < p.B) :
    member p π₁ π₂ j k ∈ remainOf p π₁ := by
  unfold member
  apply getD_mem'
  rw [(remain_spec hp).1]
  exact hp.h2.2.2 _ (getD_mem' _ _ (by rw [hp.h2.1]; exact idx_lt p j k hj hk))

/-- Distinct bucket positions hold distinct candidates. -/
theorem member_inj (hp : Perms p π₁ π₂) (j k j' k' : Nat) (hj : j < p.N) (hk : k < p.B) (hj' : j' < p.N)
    (hk' : k' < p.B) (h : member p π₁ π₂ j k = member p π₁ π₂ j' k') : j = j' ∧ k = k' := by
  have hi := idx_lt p j k hj hk
  have hi' := idx_lt p j' k' hj' hk'
  obtain ⟨rl, rn⟩ := remain_spec hp
  unfold member at h
  have e1 := nodup_getD_inj _ rn _ _
    (by rw [rl]; exact hp.h2.2.2 _ (getD_mem' _ _ (by rw [hp.h2.1]; exact hi)))
    (by rw [rl]; exact hp.h2.2.2 _ (getD_mem' _ _ (by rw [hp.h2.1]; exact hi'))) h
  have e2 := nodup_getD_inj _ hp.h2.2.1 _ _ (by rw [hp.h2.1]; exact hi) (by rw [hp.h2.1]; exact hi') e1
  exact idx_inj p.B j k j' k' hk hk' e2

theorem posOf_member (hp : Perms p π₁ π₂) (j k : Nat) (hj : j < p.N) (hk : k < p.B) :
    posOf p π₁ π₂ (member p π₁ π₂ j k) = some (j, k) := by
  unfold posOf
  apply find?_unique
  · exact (mem_positions p (j, k)).mpr ⟨hj, hk⟩
  · simp
  · intro e he hPe
    have := (mem_positions p e).mp he
    simp only [beq_iff_eq] at hPe
    obtain ⟨h1, h2⟩ := member_inj hp e.1 e.2 j k this.1 this.2 hj hk hPe
    exact Prod.ext h1 h2

theorem posOf_cut (hp : Perms p π₁ π₂) (c : Nat) (hc : c ∈ cutOf p π₁) : posOf p π₁ π₂ c = none := by
  unfold posOf
  rw [List.find?_eq_none]
  intro e he
  simp only [beq_iff_eq]
  intro heq
  have := (mem_positions p e).mp he
  exact cut_disjoint p π₁ hp.h1.2.1 c hc (heq ▸ member_mem_remain hp e.1 e.2 this.1 this.2)

theorem posOf_some (c j k : Nat) (h : posOf p π₁ π₂ c = some (j, k)) :
    j < p.N ∧ k < p.B ∧ member p π₁ π₂ j k = c := by
  unfold posOf at h
  have h1 := List.mem_of_find?_eq_some h
  have h2 := List.find?_some h
  simp only [beq_iff_eq] at h2
  have := (mem_positions p (j, k)).mp h1
  exact ⟨this.1, this.2, h2⟩

end Positions

/-! ## The re-randomisation -/

/-- The shift of candidate `c` (mod p): a kept reference moves to `moveRef`; the other members of
its bucket move by the opposite amount; every other candidate (the cut) stays. -/
def shiftOf (p : Params) (π₁ π₂ : List Nat) (δ : Nat → Nat) (r : Nat → Nat) (c : Nat) : Nat :=
  match posOf p π₁ π₂ c with
  | some (j, 0) => (moveRef (decide (j < p.bits)) (δ j) (r c) + (P - r c)) % P
  | some (j, _ + 1) =>
    (r (member p π₁ π₂ j 0) + (P - moveRef (decide (j < p.bits)) (δ j) (r (member p π₁ π₂ j 0)))) % P
  | none => 0

/-- The re-randomised candidates for the challenges (π₁, π₂). -/
def reRand2 (p : Params) (π₁ π₂ : List Nat) (δ : Nat → Nat) (r : Nat → Nat) (c : Nat) : Nat :=
  (r c + shiftOf p π₁ π₂ δ r c) % P

/-- **The re-randomisation Σ of plan 7.0** on the honest party's candidates, for the challenges
`ππ` of its run (the identity for a run that did not reach the second challenge). -/
def reRand (p : Params) (ππ : Option (List Nat × List Nat)) (δ : Nat → Nat) (r : Nat → Nat) (c : Nat) : Nat :=
  match ππ with
  | some (π₁, π₂) => reRand2 p π₁ π₂ δ r c
  | none => r c

/-- The amounts that undo `δ`. -/
def negShift (p : Params) (δ : Nat → Nat) (j : Nat) : Nat := negAmt (decide (j < p.bits)) (δ j)

section ReRand

variable {p : Params} {π₁ π₂ : List Nat}

theorem B_pos (hM : 0 < p.M) : 0 < p.B := by
  rcases Nat.eq_zero_or_pos p.B with h | h
  · exfalso
    simp [Params.M, Params.K, h] at hM
  · exact h

theorem shiftOf_ref (hp : Perms p π₁ π₂) (hM : 0 < p.M) (δ r : Nat → Nat) (j : Nat) (hj : j < p.N) :
    shiftOf p π₁ π₂ δ r (member p π₁ π₂ j 0) =
      (moveRef (decide (j < p.bits)) (δ j) (r (member p π₁ π₂ j 0)) + (P - r (member p π₁ π₂ j 0))) % P := by
  unfold shiftOf
  rw [posOf_member hp j 0 hj (B_pos hM)]

theorem shiftOf_mem (hp : Perms p π₁ π₂) (δ r : Nat → Nat) (j k : Nat) (hj : j < p.N) (hk : k + 1 < p.B) :
    shiftOf p π₁ π₂ δ r (member p π₁ π₂ j (k + 1)) =
      (r (member p π₁ π₂ j 0) + (P - moveRef (decide (j < p.bits)) (δ j) (r (member p π₁ π₂ j 0)))) % P := by
  unfold shiftOf
  rw [posOf_member hp j (k + 1) hj hk]

theorem shiftOf_none (δ r : Nat → Nat) (c : Nat) (h : posOf p π₁ π₂ c = none) : shiftOf p π₁ π₂ δ r c = 0 := by
  unfold shiftOf
  rw [h]

/-- The re-randomised candidates are canonical. -/
theorem reRand_lt (ππ : Option (List Nat × List Nat)) (δ r : Nat → Nat) (c : Nat) (hc : r c < P) :
    reRand p ππ δ r c < P := by
  unfold reRand
  split
  · exact Nat.mod_lt _ P_pos
  · exact hc

/-- A kept reference is moved by `δ`. -/
theorem reRand2_ref (hp : Perms p π₁ π₂) (hM : 0 < p.M) (δ r : Nat → Nat) (hr : ∀ c, c < p.M → r c < P)
    (j : Nat) (hj : j < p.N) :
    reRand2 p π₁ π₂ δ r (member p π₁ π₂ j 0) =
      moveRef (decide (j < p.bits)) (δ j) (r (member p π₁ π₂ j 0)) := by
  have ha := hr _ (member_lt p π₁ π₂ hp.h1.2.2 hM j 0)
  have hm := moveRef_lt (decide (j < p.bits)) (δ j) _ ha
  unfold reRand2
  rw [shiftOf_ref hp hM δ r j hj]
  generalize moveRef (decide (j < p.bits)) (δ j) (r (member p π₁ π₂ j 0)) = m at *
  generalize r (member p π₁ π₂ j 0) = a at *
  rw [P_eq] at *
  omega

/-- The cut is untouched. -/
theorem reRand2_cut (hp : Perms p π₁ π₂) (δ r : Nat → Nat) (hr : ∀ c, c < p.M → r c < P) (c : Nat)
    (hc : c ∈ cutOf p π₁) : reRand2 p π₁ π₂ δ r c = r c := by
  unfold reRand2
  rw [shiftOf_none δ r c (posOf_cut hp c hc), Nat.add_zero]
  exact Nat.mod_eq_of_lt (hr c (hp.h1.2.2 c (List.mem_of_mem_take hc)))

/-- In every bucket pair the sum of the reference and the member is unchanged mod p. -/
theorem reRand2_pair (hp : Perms p π₁ π₂) (hM : 0 < p.M) (δ r : Nat → Nat) (hr : ∀ c, c < p.M → r c < P)
    (e : Nat × Nat × Nat) (he : e ∈ pairs p) :
    (reRand2 p π₁ π₂ δ r (member p π₁ π₂ e.2.1 0) + reRand2 p π₁ π₂ δ r (member p π₁ π₂ e.2.1 e.2.2)) % P =
      (r (member p π₁ π₂ e.2.1 0) + r (member p π₁ π₂ e.2.1 e.2.2)) % P := by
  simp only [pairs, List.mem_flatMap, List.mem_map, List.mem_range] at he
  obtain ⟨o, -, j, hj, k, hk, rfl⟩ := he
  have hml := member_lt p π₁ π₂ hp.h1.2.2 hM
  have ha := hr _ (hml j 0)
  have hc := hr _ (hml j (k + 1))
  have hm := moveRef_lt (decide (j < p.bits)) (δ j) _ ha
  show (reRand2 p π₁ π₂ δ r (member p π₁ π₂ j 0) + reRand2 p π₁ π₂ δ r (member p π₁ π₂ j (k + 1))) % P =
    (r (member p π₁ π₂ j 0) + r (member p π₁ π₂ j (k + 1))) % P
  rw [reRand2_ref hp hM δ r hr j hj]
  unfold reRand2
  rw [shiftOf_mem hp δ r j k hj (by omega)]
  generalize moveRef (decide (j < p.bits)) (δ j) (r (member p π₁ π₂ j 0)) = m at *
  generalize r (member p π₁ π₂ j 0) = a at *
  generalize r (member p π₁ π₂ j (k + 1)) = c at *
  rw [P_eq] at *
  omega

/-- **The re-randomisation is undone by `negShift`** (so it is a bijection of the canonical
candidate vectors). -/
theorem reRand2_inverse (hp : Perms p π₁ π₂) (hM : 0 < p.M) (δ r : Nat → Nat) (hr : ∀ c, c < p.M → r c < P)
    (c : Nat) (hc : c < p.M) :
    reRand2 p π₁ π₂ (negShift p δ) (reRand2 p π₁ π₂ δ r) c = r c := by
  have hml := member_lt p π₁ π₂ hp.h1.2.2 hM
  have hr' : ∀ c, c < p.M → reRand2 p π₁ π₂ δ r c < P := fun c _ => Nat.mod_lt _ P_pos
  cases hpos : posOf p π₁ π₂ c with
  | none =>
    unfold reRand2
    rw [shiftOf_none _ _ c hpos, shiftOf_none _ _ c hpos, Nat.add_zero, Nat.add_zero, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (hr c hc)
  | some e =>
    obtain ⟨j, k⟩ := e
    obtain ⟨hj, hk, rfl⟩ := posOf_some _ j k hpos
    have ha := hr _ (hml j 0)
    cases k with
    | zero =>
      rw [reRand2_ref hp hM _ _ hr' j hj, reRand2_ref hp hM δ r hr j hj]
      exact moveRef_neg _ _ _ ha
    | succ k =>
      have hcc := hr _ (hml j (k + 1))
      have hm := moveRef_lt (decide (j < p.bits)) (δ j) _ ha
      have hback : moveRef (decide (j < p.bits)) (negShift p δ j)
          (moveRef (decide (j < p.bits)) (δ j) (r (member p π₁ π₂ j 0))) = r (member p π₁ π₂ j 0) :=
        moveRef_neg _ _ _ ha
      have e1 : reRand2 p π₁ π₂ (negShift p δ) (reRand2 p π₁ π₂ δ r) (member p π₁ π₂ j (k + 1)) =
          (reRand2 p π₁ π₂ δ r (member p π₁ π₂ j (k + 1)) + (reRand2 p π₁ π₂ δ r (member p π₁ π₂ j 0) +
            (P - moveRef (decide (j < p.bits)) (negShift p δ j) (reRand2 p π₁ π₂ δ r (member p π₁ π₂ j 0)))) % P) % P := by
        show (_ + shiftOf p π₁ π₂ (negShift p δ) (reRand2 p π₁ π₂ δ r) (member p π₁ π₂ j (k + 1))) % P = _
        rw [shiftOf_mem hp _ _ j k hj hk]
      rw [e1, reRand2_ref hp hM δ r hr j hj, hback]
      unfold reRand2
      rw [shiftOf_mem hp δ r j k hj hk]
      generalize moveRef (decide (j < p.bits)) (δ j) (r (member p π₁ π₂ j 0)) = m at *
      generalize r (member p π₁ π₂ j 0) = a at *
      generalize r (member p π₁ π₂ j (k + 1)) = c at *
      rw [P_eq] at *
      omega

end ReRand

/-! ## Stores -/

/-- The store `σ` with the candidates `r` in its candidate slots (and `σ`'s challenge randomness
and everything else). -/
def setCands (p : Params) (s : Slots) (σ : Store) (r : Nat → Nat) : Store :=
  { σ with
    bits := fun j => if j = s.bits then ((List.range p.M).map fun c => word (r c)).flatten else σ.bits j
    elems := fun j =>
      if j = s.elems then (List.range p.M).map fun c => TlsMpc.FieldDag.ofNat (r c)
      else if s.coins ≤ j ∧ j < s.coins + p.M then (word (r (j - s.coins))).map X25519.bitValue
      else σ.elems j }

/-- The challenge randomness of a store is in place: 32-byte nonces and values. -/
structure Bytes32 (s : Slots) (σ : Store) : Prop where
  n1 : (σ.bytes s.cutNonce).length = 32
  v1 : (σ.bytes s.cutValue).length = 32
  n2 : (σ.bytes s.bucketNonce).length = 32
  v2 : (σ.bytes s.bucketValue).length = 32

/-- `setCands` gives an honest store (the elements' slot is not one of the coins' slots). -/
theorem setCands_honest (p : Params) (s : Slots) (σ : Store) (r : Nat → Nat)
    (hslots : s.elems < s.coins ∨ s.coins + p.M ≤ s.elems) (h32 : Bytes32 s σ) (hr : ∀ c, c < p.M → r c < P) :
    HonestStore p s (setCands p s σ r) r := by
  refine ⟨by simp [setCands], by simp [setCands], fun c hc => ?_, hr, h32.n1, h32.v1, h32.n2, h32.v2⟩
  show (if s.coins + c = s.elems then _ else if s.coins ≤ s.coins + c ∧ s.coins + c < s.coins + p.M then _ else _) = _
  rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]

/-! ## The theorem -/

section Hides

variable (E : Env) (me : Party) (adv : Adversary) (p : Params) (b f : Nat)

/-- **The two challenge permutations of a run** (when it reached the second challenge). -/
def permsOf (s : Slots) (σ : Store) (I : Ideal) (vD : List Release) : Option (List Nat × List Nat) :=
  (withAdv E me adv (bucketChallenge p b f E.hash me s) σ I vD).result

theorem perms_of_result (s : Slots) (σ : Store) (I : Ideal) (vD : List Release) (π₁ π₂ : List Nat)
    (h : permsOf E me adv p b f s σ I vD = some (π₁, π₂)) : Perms p π₁ π₂ := by
  obtain ⟨h1, h2⟩ := Leaves.result E me adv _ (bucketChallenge_leaves p b f E.hash me s) σ I vD _ h
  exact ⟨h1, h2⟩

/-- A run that reached the second challenge reached the first with the same π₁. -/
theorem cut_of_bucket (s : Slots) (σ : Store) (I : Ideal) (vD : List Release) (π₁ π₂ : List Nat)
    (h : (withAdv E me adv (bucketChallenge p b f E.hash me s) σ I vD).result = some (π₁, π₂)) :
    (withAdv E me adv (cutChallenge p b f E.hash me s) σ I vD).result = some π₁ := by
  rw [bucketChallenge_split, withAdv_bind] at h
  revert h
  cases hc : (withAdv E me adv (cutChallenge p b f E.hash me s) σ I vD).result with
  | none => simp [Outcome.stop]
  | some π =>
    simp only [Outcome.then]
    intro h
    have hl : Leaves (fun ππ : List Nat × List Nat => ππ.1 = π) ((cutPhase p b f π).bind fun _ =>
        (Random.challenge E.hash me s.bucketNonce s.bucketValue (domain p "bucket") p.K).bind fun π₂ =>
        .done (π, π₂)) :=
      Leaves.bind (Q := fun ππ : List Nat × List Nat => ππ.1 = π) _ (fun _ =>
        Leaves.bind (Q := fun ππ : List Nat × List Nat => ππ.1 = π) _ (fun π₂ => Leaves.done (π, π₂) rfl) _) _
    have := Leaves.result E me adv _ hl _ _ _ _ h
    simp only at this
    rw [this]

/-- **The experiment of plan 7.0 for P-CUT (c)**: what the adversary sees of a run of `generate`
whose honest party holds the candidates `r` (in the store `setCands p s σ r`), together with the
honest party's kept references moved by `δ`. -/
def hideView (s : Slots) (σ : Store) (I : Ideal) (vD : List Release) (δ : Nat → Nat) (r : Nat → Nat) :
    List Release × (Nat → Nat) :=
  ((withAdv E me adv (generate p b f E.hash me s) (setCands p s σ r) I vD).viewD,
    fun j =>
      match permsOf E me adv p b f s (setCands p s σ r) I vD with
      | some (π₁, π₂) => if j < p.N then moveRef (decide (j < p.bits)) (δ j) (r (refOf p π₁ π₂ j)) else 0
      | none => 0)

/-- **The runs with `r` and with the re-randomised candidates agree**, and reach the same
challenges. -/
theorem reRand_agree (hh : ∀ m, (E.hash m).length = 32) (hW : WordLoaded E) (hP : ProgsLoaded E)
    (hM : 0 < p.M) (hbits : p.bits ≤ p.N) (s : Slots) (hslots : s.elems < s.coins ∨ s.coins + p.M ≤ s.elems)
    (σ : Store) (h32 : Bytes32 s σ) (I : Ideal) (vD : List Release) (δ : Nat → Nat) (r : Nat → Nat)
    (hr : ∀ c, c < p.M → r c < P) :
    Agree (fun _ _ _ _ _ => True)
      (withAdv E me adv (generate p b f E.hash me s) (setCands p s σ r) I vD)
      (withAdv E me adv (generate p b f E.hash me s)
        (setCands p s σ (reRand p (permsOf E me adv p b f s (setCands p s σ r) I vD) δ r)) I vD) ∧
    permsOf E me adv p b f s (setCands p s σ (reRand p (permsOf E me adv p b f s (setCands p s σ r) I vD) δ r)) I vD =
      permsOf E me adv p b f s (setCands p s σ r) I vD := by
  have hσ := setCands_honest p s σ r hslots h32 hr
  have hσ' := setCands_honest p s σ (reRand p (permsOf E me adv p b f s (setCands p s σ r) I vD) δ r) hslots h32
    (fun c hc => reRand_lt _ δ r c (hr c hc))
  have hcut : ∀ π₁, (withAdv E me adv (cutChallenge p b f E.hash me s) (setCands p s σ r) I vD).result = some π₁ →
      ∀ c ∈ cutOf p π₁, reRand p (permsOf E me adv p b f s (setCands p s σ r) I vD) δ r c = r c := by
    intro π₁ hres c hc
    cases hππ : permsOf E me adv p b f s (setCands p s σ r) I vD with
    | none => rfl
    | some ππ =>
      obtain ⟨π₁', π₂⟩ := ππ
      have e := cut_of_bucket E me adv p b f s _ I vD π₁' π₂ hππ
      rw [hres] at e
      cases e
      exact reRand2_cut (perms_of_result E me adv p b f s _ I vD _ _ hππ) δ r hr c hc
  have hbk : ∀ π₁ π₂,
      (withAdv E me adv (bucketChallenge p b f E.hash me s) (setCands p s σ r) I vD).result = some (π₁, π₂) →
      (∀ e ∈ pairs p,
        (reRand p (permsOf E me adv p b f s (setCands p s σ r) I vD) δ r (member p π₁ π₂ e.2.1 0) +
          reRand p (permsOf E me adv p b f s (setCands p s σ r) I vD) δ r (member p π₁ π₂ e.2.1 e.2.2)) % P =
        (r (member p π₁ π₂ e.2.1 0) + r (member p π₁ π₂ e.2.1 e.2.2)) % P) ∧
      (∀ j, j < p.bits → (32 ≤ reRand p (permsOf E me adv p b f s (setCands p s σ r) I vD) δ r (refOf p π₁ π₂ j) ↔
        32 ≤ r (refOf p π₁ π₂ j))) := by
    intro π₁ π₂ hres
    have hππ : permsOf E me adv p b f s (setCands p s σ r) I vD = some (π₁, π₂) := hres
    have hp := perms_of_result E me adv p b f s _ I vD _ _ hππ
    rw [hππ]
    refine ⟨fun e he => reRand2_pair hp hM δ r hr e he, fun j hj => ?_⟩
    show 32 ≤ reRand2 p π₁ π₂ δ r (member p π₁ π₂ j 0) ↔ _
    rw [reRand2_ref hp hM δ r hr j (by omega), decide_eq_true hj]
    exact moveRef_32 _ _
  refine ⟨generate_agree E me adv p b f hh hW hP hM hbits s _ _ I vD r _ hσ hσ' rfl hcut hbk, ?_⟩
  exact (bucketChallenge_agree E me adv p b f hh s _ _ I vD r _ hσ hσ' rfl hcut).result.symm

/-- **P-CUT (c) in plan 7.0's form.** Against any adversary, from any engine state and adversary
view: the adversary's view of a run of `generate` with the honest candidates `r`, together with
the kept references moved by `δ`, is the adversary's view of the run with the re-randomised
candidates `reRand π δ r` together with ITS kept references (unmoved). `reRand π δ` is a bijection
of the canonical candidate vectors (`reRand_lt`, `reRand_inverse`). -/
theorem generate_hides (hh : ∀ m, (E.hash m).length = 32) (hW : WordLoaded E) (hP : ProgsLoaded E)
    (hM : 0 < p.M) (hbits : p.bits ≤ p.N) (s : Slots) (hslots : s.elems < s.coins ∨ s.coins + p.M ≤ s.elems)
    (σ : Store) (h32 : Bytes32 s σ) (I : Ideal) (vD : List Release) (δ : Nat → Nat) (r : Nat → Nat)
    (hr : ∀ c, c < p.M → r c < P) :
    hideView E me adv p b f s σ I vD δ r =
      hideView E me adv p b f s σ I vD (fun _ => 0)
        (reRand p (permsOf E me adv p b f s (setCands p s σ r) I vD) δ r) := by
  obtain ⟨hA, hB⟩ := reRand_agree E me adv p b f hh hW hP hM hbits s hslots σ h32 I vD δ r hr
  unfold hideView
  rw [hB]
  refine Prod.ext hA.viewD (funext fun j => ?_)
  cases hππ : permsOf E me adv p b f s (setCands p s σ r) I vD with
  | none => rfl
  | some ππ =>
    obtain ⟨π₁, π₂⟩ := ππ
    have hp := perms_of_result E me adv p b f s _ I vD _ _ hππ
    show (if j < p.N then _ else 0) = (if j < p.N then _ else 0)
    split
    · next hj =>
      have hrr : reRand p (some (π₁, π₂)) δ r (refOf p π₁ π₂ j) =
          moveRef (decide (j < p.bits)) (δ j) (r (refOf p π₁ π₂ j)) := reRand2_ref hp hM δ r hr j hj
      rw [hrr]
      exact (moveRef_zero _ _ (moveRef_lt _ _ _ (hr _ (member_lt p π₁ π₂ hp.h1.2.2 hM j 0)))).symm
    · rfl

/-- **The re-randomisation is a bijection**: re-randomising the re-randomised candidates with
`negShift δ` (for the challenges of THEIR run, which are the same) gives back `r`. -/
theorem reRand_inverse (hh : ∀ m, (E.hash m).length = 32) (hW : WordLoaded E) (hP : ProgsLoaded E)
    (hM : 0 < p.M) (hbits : p.bits ≤ p.N) (s : Slots) (hslots : s.elems < s.coins ∨ s.coins + p.M ≤ s.elems)
    (σ : Store) (h32 : Bytes32 s σ) (I : Ideal) (vD : List Release) (δ : Nat → Nat) (r : Nat → Nat)
    (hr : ∀ c, c < p.M → r c < P) (c : Nat) (hc : c < p.M) :
    reRand p (permsOf E me adv p b f s
        (setCands p s σ (reRand p (permsOf E me adv p b f s (setCands p s σ r) I vD) δ r)) I vD) (negShift p δ)
      (reRand p (permsOf E me adv p b f s (setCands p s σ r) I vD) δ r) c = r c := by
  obtain ⟨-, hB⟩ := reRand_agree E me adv p b f hh hW hP hM hbits s hslots σ h32 I vD δ r hr
  rw [hB]
  cases hππ : permsOf E me adv p b f s (setCands p s σ r) I vD with
  | none => rfl
  | some ππ =>
    obtain ⟨π₁, π₂⟩ := ππ
    exact reRand2_inverse (perms_of_result E me adv p b f s _ I vD _ _ hππ) hM δ r hr c hc

end Hides

end TlsMpc.Node.Flows.Masks
