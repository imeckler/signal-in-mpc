import TlsMpc.KernelSpecs.KemEncoding

/-!
# KEM kernels: the compaction sampler at full size

`MlKemFast.sample` (the matrix sampler of `kem-matrix`) keeps the first `count`
candidates below q with a compaction network: every candidate carries the number
of rejected candidates before it (its distance) and, in stage `s`, a valid cell
whose distance has binary digit `s` set moves `2^s` places left.

* `compact_spec` (general, any number `n` of candidates and any number `S` of
  stages with `n ≤ 2^S`, for a start state with the right distances): after the
  stages every accepted candidate `i` sits at `i − distance(i)` (its rank among the
  accepted ones) unchanged, and every other cell is invalid. The invariant is
  "after `s` stages, accepted candidate `i` sits at `i − (distance(i) mod 2^s)`,
  and no other cell is valid"; distinct accepted candidates never collide because
  `i ↦ i − (distance(i) mod 2^s)` is strictly increasing on them (`tgt_lt`).
* `sample_eq`: for `0 < count ≤ n ≤ 512` (the kernels: 448 candidates, nine
  stages, 256 kept), `MlKemFast.sample count` is `firstAccepted count`: the first
  `count` candidates below q and status 1 if there are that many, otherwise zeros
  and status 0. `sample_small` in `MlKemFastProofs` was the six-candidate case.
* `run_refines` / `run_status`: the same against the specification's Word64
  sampler `MlKemSample.run … 256 224` (the serial "accepted-counter" fold, then the
  16-bit serialisation and `decodePoly`), on every byte stream.
-/
namespace TlsMpc.KernelSpecs.KemSample
open TlsMpc.Signal
open TlsMpc.Signal.MlKemFast (Cell)

abbrev KCell := Cell (BitVec 1) (BitVec 12)

local notation "FO" => MlKemFast.concrete
local notation "EC" => MlKemFast.emptyCell MlKemFast.concrete

/-! ### Distances -/

/-- Number of rejected indices below `i`. -/
def rej (v : Nat → Bool) : Nat → Nat
  | 0 => 0
  | i + 1 => rej v i + (if v i then 0 else 1)

theorem rej_le (v : Nat → Bool) : ∀ i, rej v i ≤ i
  | 0 => Nat.le_refl 0
  | i + 1 => by
      have := rej_le v i
      simp only [rej]
      split <;> omega

theorem rej_mono (v : Nat → Bool) (i : Nat) : ∀ k, rej v i ≤ rej v (i + k)
  | 0 => Nat.le_refl _
  | k + 1 => by
      have := rej_mono v i k
      show rej v i ≤ rej v (i + k) + (if v (i + k) then 0 else 1)
      omega

theorem rej_add_le (v : Nat → Bool) (i : Nat) : ∀ k, rej v (i + k) ≤ rej v i + k
  | 0 => Nat.le_refl _
  | k + 1 => by
      have := rej_add_le v i k
      show rej v (i + k) + (if v (i + k) then 0 else 1) ≤ rej v i + (k + 1)
      split <;> omega

theorem rej_congr (v w : Nat → Bool) : ∀ i, (∀ j, j < i → v j = w j) → rej v i = rej w i
  | 0, _ => rfl
  | i + 1, h => by
      simp only [rej, rej_congr v w i (fun j hj => h j (by omega)), h i (by omega)]

theorem rej_front (v : Nat → Bool) : ∀ i,
    rej v (i + 1) = (if v 0 then 0 else 1) + rej (fun j => v (j + 1)) i
  | 0 => by simp [rej]
  | i + 1 => by
      have ih := rej_front v i
      show rej v (i + 1) + (if v (i + 1) then 0 else 1) =
        (if v 0 then 0 else 1) + (rej (fun j => v (j + 1)) i + (if v (i + 1) then 0 else 1))
      rw [ih]
      omega

/-- Where candidate `i` sits after `s` stages. -/
def tgt (v : Nat → Bool) (s i : Nat) : Nat := i - rej v i % 2 ^ s

theorem tgt_lt (v : Nat → Bool) (s i j : Nat) (hi : v i = true) (hij : i < j) : tgt v s i < tgt v s j := by
  have mono : rej v i ≤ rej v j := by
    have := rej_mono v i (j - i); rwa [show i + (j - i) = j by omega] at this
  have gap : rej v j ≤ rej v i + (j - i - 1) := by
    have h1 := rej_add_le v (i + 1) (j - i - 1)
    rw [show i + 1 + (j - i - 1) = j by omega] at h1
    have h2 : rej v (i + 1) = rej v i := by simp [rej, hi]
    omega
  have hle := rej_le v i
  have qi := Nat.div_add_mod (rej v i) (2 ^ s)
  have qj := Nat.div_add_mod (rej v j) (2 ^ s)
  have qq : 2 ^ s * (rej v i / 2 ^ s) ≤ 2 ^ s * (rej v j / 2 ^ s) :=
    Nat.mul_le_mul_left _ (Nat.div_le_div_right mono)
  unfold tgt
  generalize 2 ^ s * (rej v i / 2 ^ s) = X at qi qq
  generalize 2 ^ s * (rej v j / 2 ^ s) = Y at qj qq
  generalize rej v i % 2 ^ s = ri at qi ⊢
  generalize rej v j % 2 ^ s = rj at qj ⊢
  omega

theorem tgt_inj (v : Nat → Bool) (s i j : Nat) (hi : v i = true) (hj : v j = true) (h : tgt v s i = tgt v s j) :
    i = j := by
  rcases Nat.lt_trichotomy i j with c | c | c
  · exact absurd h (Nat.ne_of_lt (tgt_lt v s i j hi c))
  · exact c
  · exact absurd h (Nat.ne_of_gt (tgt_lt v s j i hj c))

theorem tgt_le (v : Nat → Bool) (s i : Nat) : tgt v s i ≤ i := Nat.sub_le _ _

theorem tgt_succ (v : Nat → Bool) (s i : Nat) :
    tgt v (s + 1) i + (if rej v i / 2 ^ s % 2 = 1 then 2 ^ s else 0) = tgt v s i := by
  unfold tgt
  have split := @Nat.mod_pow_succ (rej v i) 2 s
  have hle := rej_le v i
  have hm := Nat.mod_le (rej v i) (2 ^ (s + 1))
  rcases Nat.mod_two_eq_zero_or_one (rej v i / 2 ^ s) with b | b
  · rw [b, Nat.mul_zero] at split
    rw [b, if_neg (by decide), split]
    simp
  · rw [b, Nat.mul_one] at split
    rw [b, if_pos rfl]
    rw [split] at hm ⊢
    generalize rej v i % 2 ^ s = r at hm ⊢
    generalize 2 ^ s = M at hm ⊢
    omega

theorem tgt_zero (v : Nat → Bool) (i : Nat) : tgt v 0 i = i := by
  simp [tgt, Nat.mod_one]

/-! ### One-bit and cell facts -/

theorem bv1 : ∀ b : BitVec 1, b = 0#1 ∨ b = 1#1 := by decide
theorem bv1_one : ∀ b : BitVec 1, b = 1#1 ↔ b.toNat = 1 := by decide
theorem bv1_zero : ∀ b : BitVec 1, b = 0#1 ↔ b.toNat = 0 := by decide
theorem selT_one : ∀ x y : BitVec 1, MlKemFast.selT FO 1#1 x y = x := by decide
theorem selT_zero : ∀ x y : BitVec 1, MlKemFast.selT FO 0#1 x y = y := by decide
theorem and_one : ∀ x y : BitVec 1, MlKemFast.concrete.and x y = 1#1 ↔ x = 1#1 ∧ y = 1#1 := by decide
theorem notT_one : ∀ t : BitVec 1, MlKemFast.notT FO t = 1#1 ↔ t = 0#1 := by decide

theorem select_one (x y : BitVec 12) : MlKemFast.concrete.select 1#1 x y = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [MlKemFast.concrete, MlKemFast.selectValue, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_replicate]
  by_cases hx : x.getLsbD i <;> by_cases hy : y.getLsbD i <;> simp_all [Nat.mod_one]

theorem select_zero (x y : BitVec 12) : MlKemFast.concrete.select 0#1 x y = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [MlKemFast.concrete, MlKemFast.selectValue, BitVec.getLsbD_xor, BitVec.getLsbD_and,
    BitVec.getLsbD_replicate]
  simp

theorem zipWith_selT_one : ∀ (l m : List (BitVec 1)), l.length = m.length →
    List.zipWith (MlKemFast.selT FO 1#1) l m = l
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
      simp only [List.zipWith_cons_cons, selT_one, zipWith_selT_one xs ys (by simpa using h)]
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)

theorem zipWith_selT_zero : ∀ (l m : List (BitVec 1)), l.length = m.length →
    List.zipWith (MlKemFast.selT FO 0#1) l m = m
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
      simp only [List.zipWith_cons_cons, selT_zero, zipWith_selT_zero xs ys (by simpa using h)]
  | [], _ :: _, h => absurd h (by simp)
  | _ :: _, [], h => absurd h (by simp)

/-- The cell a stage writes at a position, from the cell there (`a`) and the one `2^s` to the right (`b`). -/
def comb (s : Nat) (a b : KCell) : KCell :=
  ⟨MlKemFast.selT FO (MlKemFast.concrete.and b.valid (b.dist.getD s MlKemFast.concrete.zero)) b.valid
      (MlKemFast.concrete.and a.valid (MlKemFast.notT FO (a.dist.getD s MlKemFast.concrete.zero))),
    List.zipWith (MlKemFast.selT FO (MlKemFast.concrete.and b.valid (b.dist.getD s MlKemFast.concrete.zero))) b.dist a.dist,
    MlKemFast.concrete.select (MlKemFast.concrete.and b.valid (b.dist.getD s MlKemFast.concrete.zero)) b.data a.data⟩

theorem stage_eq (s : Nat) (st : List KCell) :
    MlKemFast.stage FO s st = List.zipWith (comb s) st (st.drop (2 ^ s) ++ List.replicate (2 ^ s) EC) := rfl

theorem emptyCell_valid : (EC).valid = 0#1 := rfl
theorem emptyCell_dist : (EC).dist.length = MlKemFast.distBits := by simp [MlKemFast.emptyCell]

theorem stage_getElem? (s : Nat) (st : List KCell) (p : Nat) :
    (MlKemFast.stage FO s st)[p]? = st[p]?.map (fun a => comb s a (st.getD (p + 2 ^ s) EC)) := by
  rw [stage_eq, List.getElem?_zipWith]
  by_cases hp : p < st.length
  · rw [List.getElem?_eq_getElem hp]
    by_cases hq : p + 2 ^ s < st.length
    · have hb : (st.drop (2 ^ s) ++ List.replicate (2 ^ s) EC)[p]? = some st[p + 2 ^ s] := by
        rw [List.getElem?_append_left (by simp; omega), List.getElem?_drop,
          show 2 ^ s + p = p + 2 ^ s by omega, List.getElem?_eq_getElem hq]
      rw [hb]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
    · have hb : (st.drop (2 ^ s) ++ List.replicate (2 ^ s) EC)[p]? = some EC := by
        rw [List.getElem?_append_right (by simp; omega), List.getElem?_replicate, if_pos (by simp; omega)]
      rw [hb]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show st.length ≤ p + 2 ^ s by omega)]
  · rw [List.getElem?_eq_none (by omega)]
    simp

theorem stage_length (s : Nat) (st : List KCell) : (MlKemFast.stage FO s st).length = st.length := by
  rw [stage_eq]
  simp only [List.length_zipWith, List.length_append, List.length_drop, List.length_replicate]
  omega

theorem comb_take (s : Nat) (a b : KCell) (hv : b.valid = 1#1) (hd : b.dist.getD s 0#1 = 1#1)
    (hl : b.dist.length = a.dist.length) : comb s a b = b := by
  have ht : MlKemFast.concrete.and b.valid (b.dist.getD s MlKemFast.concrete.zero) = 1#1 :=
    (and_one _ _).mpr ⟨hv, hd⟩
  obtain ⟨bv, bd, bx⟩ := b
  simp only [comb] at ht ⊢
  rw [ht, selT_one, zipWith_selT_one _ _ hl, select_one]

theorem comb_keep (s : Nat) (a b : KCell) (hb : ¬ (b.valid = 1#1 ∧ b.dist.getD s 0#1 = 1#1))
    (hv : a.valid = 1#1) (hd : a.dist.getD s 0#1 = 0#1) (hl : b.dist.length = a.dist.length) : comb s a b = a := by
  have ht : MlKemFast.concrete.and b.valid (b.dist.getD s MlKemFast.concrete.zero) = 0#1 := by
    rcases bv1 (MlKemFast.concrete.and b.valid (b.dist.getD s MlKemFast.concrete.zero)) with h | h
    · exact h
    · exact absurd ((and_one _ _).mp h) hb
  have hk : MlKemFast.concrete.and a.valid (MlKemFast.notT FO (a.dist.getD s MlKemFast.concrete.zero)) = 1#1 :=
    (and_one _ _).mpr ⟨hv, (notT_one _).mpr hd⟩
  obtain ⟨av, ad, ax⟩ := a
  simp only [comb] at ht hk hv ⊢
  rw [ht, hk, selT_zero, zipWith_selT_zero _ _ hl, select_zero, hv]

theorem comb_valid (s : Nat) (a b : KCell) (h : (comb s a b).valid = 1#1) :
    (b.valid = 1#1 ∧ b.dist.getD s 0#1 = 1#1) ∨ (a.valid = 1#1 ∧ a.dist.getD s 0#1 = 0#1) := by
  simp only [comb] at h
  rcases bv1 (MlKemFast.concrete.and b.valid (b.dist.getD s MlKemFast.concrete.zero)) with t | t
  · rw [t, selT_zero] at h
    have := (and_one _ _).mp h
    exact Or.inr ⟨this.1, (notT_one _).mp this.2⟩
  · exact Or.inl ((and_one _ _).mp t)

/-! ### The invariant -/

/-- Validity of the start cell at `i` (out of range: invalid). -/
def vld (init : List KCell) (i : Nat) : Bool := decide ((init.getD i EC).valid = 1#1)

/-- What the start state must satisfy: distance lists of the network's width, and every
valid cell's distance digits are those of the number of invalid cells before it. -/
structure Good (init : List KCell) (S : Nat) : Prop where
  dist : ∀ (p : Nat) (c : KCell), init[p]? = some c → c.dist.length = MlKemFast.distBits
  bits : ∀ i, i < init.length → vld init i = true → ∀ t, t < S →
    ((init.getD i EC).dist.getD t 0#1).toNat = rej (vld init) i / 2 ^ t % 2

/-- After `s` stages: the network's length, distance lists of its width, every valid start
cell at its target unchanged, and no other valid cell. -/
structure Inv (init : List KCell) (s : Nat) (st : List KCell) : Prop where
  len : st.length = init.length
  dist : ∀ (p : Nat) (c : KCell), st[p]? = some c → c.dist.length = MlKemFast.distBits
  at_target : ∀ i, i < init.length → vld init i = true →
    st[tgt (vld init) s i]? = some (init.getD i EC)
  only : ∀ (p : Nat) (c : KCell), st[p]? = some c → c.valid = 1#1 →
    ∃ i, i < init.length ∧ vld init i = true ∧ tgt (vld init) s i = p

theorem getD_eq_of_getElem? {α : Type} (l : List α) (i : Nat) (d x : α) (h : l[i]? = some x) : l.getD i d = x := by
  rw [List.getD_eq_getElem?_getD, h]; rfl

theorem getD_dist (st : List KCell) (h : ∀ (p : Nat) (c : KCell), st[p]? = some c → c.dist.length = MlKemFast.distBits) (q : Nat) :
    (st.getD q EC).dist.length = MlKemFast.distBits := by
  rw [List.getD_eq_getElem?_getD]
  cases hq : st[q]? with
  | none => exact emptyCell_dist
  | some c => exact h q c hq

theorem getD_valid (st : List KCell) (q : Nat) (h : (st.getD q EC).valid = 1#1) :
    st[q]? = some (st.getD q EC) := by
  rw [List.getD_eq_getElem?_getD] at h ⊢
  cases hq : st[q]? with
  | none => rw [hq] at h; exact absurd h (by decide)
  | some c => rfl

theorem init_inv {S : Nat} (init : List KCell) (g : Good init S) : Inv init 0 init where
  len := rfl
  dist := g.dist
  at_target := by
    intro i hi _
    rw [tgt_zero, List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rfl
  only := by
    intro p c hp hc
    have hlt : p < init.length := by
      rcases Nat.lt_or_ge p init.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hp; exact absurd hp (by simp)
    refine ⟨p, hlt, ?_, tgt_zero _ p⟩
    simp only [vld, getD_eq_of_getElem? init p EC c hp, hc, decide_true]

theorem init_bit {S : Nat} (init : List KCell) (g : Good init S) (i : Nat) (hi : i < init.length) (hv : vld init i = true)
    (s : Nat) (hs : s < S) :
    ((init.getD i EC).dist.getD s 0#1 = 1#1 ↔ rej (vld init) i / 2 ^ s % 2 = 1) := by
  rw [bv1_one, g.bits i hi hv s hs]

theorem init_bit_zero {S : Nat} (init : List KCell) (g : Good init S) (i : Nat) (hi : i < init.length) (hv : vld init i = true)
    (s : Nat) (hs : s < S) (h : ¬ rej (vld init) i / 2 ^ s % 2 = 1) :
    (init.getD i EC).dist.getD s 0#1 = 0#1 := by
  rw [bv1_zero, g.bits i hi hv s hs]
  omega

theorem init_valid (init : List KCell) (i : Nat) (hv : vld init i = true) : (init.getD i EC).valid = 1#1 := by
  simpa [vld] using hv

theorem stage_inv (init : List KCell) (S s : Nat) (g : Good init S) (hs : s < S) (st : List KCell)
    (h : Inv init s st) : Inv init (s + 1) (MlKemFast.stage FO s st) := by
  have mem_dist : ∀ (p : Nat) (a : KCell), st[p]? = some a → a.dist.length = MlKemFast.distBits := h.dist
  constructor
  · rw [stage_length, h.len]
  · intro p c hp
    rw [stage_getElem?] at hp
    cases ha : st[p]? with
    | none => rw [ha] at hp; exact absurd hp (by simp)
    | some a =>
        rw [ha] at hp
        simp only [Option.map_some, Option.some.injEq] at hp
        subst hp
        simp only [comb, List.length_zipWith, getD_dist st h.dist, mem_dist p a ha, Nat.min_self]
  · intro i hi hv
    have ci_at := h.at_target i hi hv
    have succ := tgt_succ (vld init) s i
    have hti : tgt (vld init) s i < st.length := by
      have := tgt_le (vld init) s i; rw [h.len]; omega
    by_cases bit : rej (vld init) i / 2 ^ s % 2 = 1
    · -- the cell moves `2^s` to the left
      rw [if_pos bit] at succ
      have hp : tgt (vld init) (s + 1) i < st.length := by
        have := Nat.two_pow_pos s
        generalize 2 ^ s = M at this succ
        omega
      rw [stage_getElem?, List.getElem?_eq_getElem hp, Option.map_some]
      have hb : st.getD (tgt (vld init) (s + 1) i + 2 ^ s) EC = init.getD i EC := by
        rw [succ]; exact getD_eq_of_getElem? _ _ _ _ ci_at
      rw [hb, comb_take s _ _ (init_valid init i hv) ((init_bit init g i hi hv s hs).mpr bit)
        (by rw [mem_dist _ _ ci_at, mem_dist _ _ (List.getElem?_eq_getElem hp)])]
    · -- the cell stays
      rw [if_neg bit, Nat.add_zero] at succ
      rw [succ, stage_getElem?, ci_at, Option.map_some]
      congr 1
      apply comb_keep s _ _ _ (init_valid init i hv) (init_bit_zero init g i hi hv s hs bit)
        (by rw [getD_dist st h.dist, mem_dist _ _ ci_at])
      intro ⟨bv, bd⟩
      have hb := getD_valid st _ bv
      obtain ⟨j, hj, hvj, htj⟩ := h.only _ _ hb bv
      have cj_at := h.at_target j hj hvj
      rw [htj, hb] at cj_at
      simp only [Option.some.injEq] at cj_at
      rw [cj_at] at bd
      have bitj := (init_bit init g j hj hvj s hs).mp bd
      have succj := tgt_succ (vld init) s j
      rw [if_pos bitj, htj] at succj
      have same : tgt (vld init) (s + 1) j = tgt (vld init) (s + 1) i := by
        have := tgt_succ (vld init) s i
        rw [if_neg bit] at this
        omega
      have eq := tgt_inj (vld init) (s + 1) j i hvj hv same
      subst eq
      have := Nat.two_pow_pos s
      omega
  · intro p c hp hc
    rw [stage_getElem?] at hp
    cases ha : st[p]? with
    | none => rw [ha] at hp; exact absurd hp (by simp)
    | some a =>
        rw [ha] at hp
        simp only [Option.map_some, Option.some.injEq] at hp
        subst hp
        rcases comb_valid s _ _ hc with ⟨bv, bd⟩ | ⟨av, ad⟩
        · have hb := getD_valid st _ bv
          obtain ⟨j, hj, hvj, htj⟩ := h.only _ _ hb bv
          have cj_at := h.at_target j hj hvj
          rw [htj, hb] at cj_at
          simp only [Option.some.injEq] at cj_at
          rw [cj_at] at bd
          have bitj := (init_bit init g j hj hvj s hs).mp bd
          have succj := tgt_succ (vld init) s j
          rw [if_pos bitj, htj] at succj
          exact ⟨j, hj, hvj, by omega⟩
        · obtain ⟨j, hj, hvj, htj⟩ := h.only _ _ ha av
          have cj_at := h.at_target j hj hvj
          rw [htj, ha] at cj_at
          simp only [Option.some.injEq] at cj_at
          rw [cj_at] at ad
          have bitj : ¬ rej (vld init) j / 2 ^ s % 2 = 1 := by
            intro b
            have := (init_bit init g j hj hvj s hs).mpr b
            rw [ad] at this
            exact absurd this (by decide)
          have succj := tgt_succ (vld init) s j
          rw [if_neg bitj, Nat.add_zero, htj] at succj
          exact ⟨j, hj, hvj, succj⟩

theorem stages_inv (init : List KCell) (S : Nat) (g : Good init S) :
    ∀ s, s ≤ S → Inv init s ((List.range s).foldl (fun st s => MlKemFast.stage FO s st) init)
  | 0, _ => init_inv init g
  | s + 1, hs => by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact stage_inv init S s g (by omega) _ (stages_inv init S g s (by omega))

/-- The compaction network, for any number of candidates `n ≤ 2^S` and `S` stages: every
accepted candidate ends at its rank (`i − distance`), unchanged, and no other cell is valid. -/
theorem compact_spec (init : List KCell) (S : Nat) (g : Good init S) (hn : init.length ≤ 2 ^ S) :
    ((List.range S).foldl (fun st s => MlKemFast.stage FO s st) init).length = init.length ∧
    (∀ i, i < init.length → vld init i = true →
      ((List.range S).foldl (fun st s => MlKemFast.stage FO s st) init)[i - rej (vld init) i]? =
        some (init.getD i EC)) ∧
    (∀ (p : Nat) (c : KCell), ((List.range S).foldl (fun st s => MlKemFast.stage FO s st) init)[p]? = some c →
      c.valid = 1#1 → ∃ i, i < init.length ∧ vld init i = true ∧ i - rej (vld init) i = p) := by
  have inv := stages_inv init S g S (Nat.le_refl S)
  have full : ∀ i, i < init.length → tgt (vld init) S i = i - rej (vld init) i := by
    intro i hi
    have := rej_le (vld init) i
    simp only [tgt, Nat.mod_eq_of_lt (show rej (vld init) i < 2 ^ S by omega)]
  refine ⟨inv.len, ?_, ?_⟩
  · intro i hi hv
    rw [← full i hi]
    exact inv.at_target i hi hv
  · intro p c hp hc
    obtain ⟨i, hi, hv, ht⟩ := inv.only p c hp hc
    exact ⟨i, hi, hv, by rw [← full i hi]; exact ht⟩

/-! ### The kernels' start state (`cells`): distances are counted by `increment` -/

/-- A little-endian list of bits as a number. -/
def cval : List (BitVec 1) → Nat
  | [] => 0
  | b :: rest => b.toNat + 2 * cval rest

theorem cval_lt : ∀ l : List (BitVec 1), cval l < 2 ^ l.length
  | [] => by decide
  | b :: rest => by
      have := cval_lt rest
      have hb : b.toNat < 2 := b.isLt
      show b.toNat + 2 * cval rest < 2 ^ (rest.length + 1)
      rw [Nat.pow_succ]
      omega

theorem cval_bit : ∀ (l : List (BitVec 1)) (t : Nat), (l.getD t 0#1).toNat = cval l / 2 ^ t % 2
  | [], t => by simp [cval]
  | b :: rest, 0 => by
      have hb : b.toNat < 2 := b.isLt
      show b.toNat = (b.toNat + 2 * cval rest) / 2 ^ 0 % 2
      rw [Nat.pow_zero, Nat.div_one]
      omega
  | b :: rest, t + 1 => by
      have hb : b.toNat < 2 := b.isLt
      rw [List.getD_cons_succ, cval_bit rest t]
      show cval rest / 2 ^ t % 2 = (b.toNat + 2 * cval rest) / 2 ^ (t + 1) % 2
      rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul, show (b.toNat + 2 * cval rest) / 2 = cval rest by omega]

theorem cval_replicate : ∀ n, cval (List.replicate n 0#1) = 0
  | 0 => rfl
  | n + 1 => by
      show (0#1).toNat + 2 * cval (List.replicate n 0#1) = 0
      rw [cval_replicate n]
      rfl

theorem mod_helper (v k M : Nat) (hk : k < 2) (hM : 0 < M) : (2 * v + k) % (2 * M) = 2 * (v % M) + k := by
  have h1 := Nat.div_add_mod v M
  have h2 := Nat.mod_lt v hM
  have e : 2 * v + k = (2 * (v % M) + k) + (2 * M) * (v / M) := by
    rw [Nat.mul_assoc]
    generalize M * (v / M) = X at h1 ⊢
    generalize v % M = r at h1 h2 ⊢
    omega
  have small : 2 * (v % M) + k < 2 * M := by
    generalize v % M = r at h2 ⊢
    omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt small]

theorem half_adder : ∀ b c : BitVec 1,
    (MlKemFast.concrete.xor b c).toNat + 2 * (MlKemFast.concrete.and b c).toNat = b.toNat + c.toNat := by decide

theorem increment_spec : ∀ (l : List (BitVec 1)) (c : BitVec 1),
    (MlKemFast.increment FO l c).length = l.length ∧
      cval (MlKemFast.increment FO l c) = (cval l + c.toNat) % 2 ^ l.length
  | [], c => by
      refine ⟨rfl, ?_⟩
      show 0 = (0 + c.toNat) % 1
      rw [Nat.mod_one]
  | b :: rest, c => by
      obtain ⟨ih1, ih2⟩ := increment_spec rest (MlKemFast.concrete.and b c)
      refine ⟨by simp [MlKemFast.increment, ih1], ?_⟩
      show (MlKemFast.concrete.xor b c).toNat + 2 * cval (MlKemFast.increment FO rest (MlKemFast.concrete.and b c)) =
        (b.toNat + 2 * cval rest + c.toNat) % 2 ^ (rest.length + 1)
      have hadd := half_adder b c
      have hX : (MlKemFast.concrete.xor b c).toNat < 2 := (MlKemFast.concrete.xor b c).isLt
      have e : b.toNat + 2 * cval rest + c.toNat =
          2 * (cval rest + (MlKemFast.concrete.and b c).toNat) + (MlKemFast.concrete.xor b c).toNat := by omega
      rw [ih2, e, Nat.pow_succ, Nat.mul_comm (2 ^ rest.length) 2, mod_helper _ _ _ hX (Nat.two_pow_pos _)]
      omega

/-- Acceptance of a candidate: below q. -/
def accB (c : BitVec 12) : Bool := decide (c.toNat < 3329)

theorem notT_ltQ (c : BitVec 12) :
    (MlKemFast.notT FO (MlKemFast.concrete.ltQ c)).toNat = if accB c then 0 else 1 := by
  show (MlKemFast.notT FO (MlKemFast.ltQValue c)).toNat = _
  rw [MlKemFast.ltQValue_eq]
  by_cases h : c.toNat < 3329
  · rw [if_pos h, show accB c = true by simp [accB, h]]; decide
  · rw [if_neg h, show accB c = false by simp [accB, h]]; decide

theorem cells_spec : ∀ (cs : List (BitVec 12)) (count : List (BitVec 1)) (i : Nat) (hi : i < cs.length),
    ∃ D : List (BitVec 1), (MlKemFast.cells FO cs count)[i]? = some ⟨MlKemFast.concrete.ltQ cs[i], D, cs[i]⟩ ∧
      D.length = count.length ∧ cval D = (cval count + rej (fun j => accB (cs.getD j 0#12)) i) % 2 ^ count.length
  | [], _, i, hi => absurd hi (by simp)
  | c :: rest, count, 0, _ => ⟨count, rfl, rfl, by simp [rej, Nat.mod_eq_of_lt (cval_lt count)]⟩
  | c :: rest, count, i + 1, hi => by
      have hi' : i < rest.length := by simpa using hi
      obtain ⟨len', val'⟩ := increment_spec count (MlKemFast.notT FO (MlKemFast.concrete.ltQ c))
      obtain ⟨D, hD, hlen, hval⟩ := cells_spec rest _ i hi'
      refine ⟨D, ?_, ?_, ?_⟩
      · rw [show MlKemFast.cells FO (c :: rest) count = _ :: MlKemFast.cells FO rest
            (MlKemFast.increment FO count (MlKemFast.notT FO (MlKemFast.concrete.ltQ c))) from rfl,
          List.getElem?_cons_succ, hD]
        rfl
      · rw [hlen, len']
      · rw [hval, len', val', notT_ltQ, Nat.mod_add_mod, rej_front]
        simp only [List.getD_cons_zero, List.getD_cons_succ]
        rw [Nat.add_assoc]

theorem cells_length : ∀ (cs : List (BitVec 12)) (count : List (BitVec 1)),
    (MlKemFast.cells FO cs count).length = cs.length
  | [], _ => rfl
  | c :: rest, count => by
      show (MlKemFast.cells FO rest _).length + 1 = rest.length + 1
      rw [cells_length rest]

theorem ltQ_value (x : BitVec 12) : MlKemFast.concrete.ltQ x = if accB x then 1#1 else 0#1 := by
  show MlKemFast.ltQValue x = _
  rw [MlKemFast.ltQValue_eq]
  by_cases h : x.toNat < 3329
  · rw [if_pos h, show accB x = true by simp [accB, h]]; rfl
  · rw [if_neg h, show accB x = false by simp [accB, h]]; rfl

theorem cells_getD (cs : List (BitVec 12)) (count : List (BitVec 1)) (i : Nat) (hi : i < cs.length) :
    ((MlKemFast.cells FO cs count).getD i EC).valid = MlKemFast.concrete.ltQ cs[i] ∧
      ((MlKemFast.cells FO cs count).getD i EC).data = cs[i] := by
  obtain ⟨D, hD, _, _⟩ := cells_spec cs count i hi
  rw [getD_eq_of_getElem? _ _ _ _ hD]
  exact ⟨rfl, rfl⟩

theorem vld_cells (cs : List (BitVec 12)) (count : List (BitVec 1)) (j : Nat) (hj : j < cs.length) :
    vld (MlKemFast.cells FO cs count) j = accB (cs.getD j 0#12) := by
  unfold vld
  rw [(cells_getD cs count j hj).1, ltQ_value, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
    Option.getD_some]
  cases accB cs[j] <;> decide

theorem rej_cells (cs : List (BitVec 12)) (count : List (BitVec 1)) (i : Nat) (hi : i ≤ cs.length) :
    rej (vld (MlKemFast.cells FO cs count)) i = rej (fun j => accB (cs.getD j 0#12)) i :=
  rej_congr _ _ i (fun j hj => vld_cells cs count j (by omega))

theorem cells_good (cs : List (BitVec 12)) (hn : cs.length ≤ 512) :
    Good (MlKemFast.cells FO cs (List.replicate MlKemFast.distBits MlKemFast.concrete.zero)) 9 where
  dist := by
    intro p c hp
    have hlt : p < cs.length := by
      rcases Nat.lt_or_ge p cs.length with h | h
      · exact h
      · rw [List.getElem?_eq_none (by rw [cells_length]; exact h)] at hp; exact absurd hp (by simp)
    obtain ⟨D, hD, hlen, _⟩ := cells_spec cs _ p hlt
    rw [hD] at hp
    simp only [Option.some.injEq] at hp
    subst hp
    simpa using hlen
  bits := by
    intro i hi _ t _
    rw [cells_length] at hi
    obtain ⟨D, hD, hlen, hval⟩ := cells_spec cs _ i hi
    rw [getD_eq_of_getElem? _ _ _ _ hD, cval_bit, hval, rej_cells cs _ i (by omega)]
    have z : MlKemFast.concrete.zero = 0#1 := rfl
    rw [z, cval_replicate, Nat.zero_add, List.length_replicate]
    have := rej_le (fun j => accB (cs.getD j 0#12)) i
    rw [Nat.mod_eq_of_lt (show rej (fun j => accB (cs.getD j 0#12)) i < 2 ^ MlKemFast.distBits by
      show _ < 512; omega)]

/-! ### Ranks and the filtered list -/

theorem rej_rank (cs : List (BitVec 12)) : ∀ i, i ≤ cs.length →
    rej (fun j => accB (cs.getD j 0#12)) i + ((cs.take i).filter accB).length = i
  | 0, _ => by simp [rej]
  | i + 1, hi => by
      have ih := rej_rank cs i (by omega)
      have hget : cs[i]? = some (cs.getD i 0#12) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
      rw [List.take_add_one, hget, Option.toList_some, List.filter_append, List.length_append]
      simp only [rej]
      by_cases h : accB (cs.getD i 0#12) = true
      · rw [List.filter_cons, if_pos h, if_pos h, List.filter_nil, List.length_singleton]
        omega
      · rw [List.filter_cons, if_neg h, if_neg h, List.filter_nil, List.length_nil]
        omega

theorem filter_surj {α : Type} (P : α → Bool) : ∀ (l : List α) (k : Nat), k < (l.filter P).length →
    ∃ i x, l[i]? = some x ∧ P x = true ∧ ((l.take i).filter P).length = k ∧ (l.filter P)[k]? = some x
  | [], k, h => absurd h (by simp)
  | a :: l, k, h => by
      by_cases ha : P a = true
      · rw [List.filter_cons_of_pos ha] at h ⊢
        cases k with
        | zero => exact ⟨0, a, rfl, ha, by simp, rfl⟩
        | succ k =>
            obtain ⟨i, x, h1, h2, h3, h4⟩ := filter_surj P l k (by simpa using h)
            refine ⟨i + 1, x, by simpa using h1, h2, ?_, by simpa using h4⟩
            rw [List.take_succ_cons, List.filter_cons_of_pos ha, List.length_cons, h3]
      · rw [List.filter_cons_of_neg ha] at h ⊢
        obtain ⟨i, x, h1, h2, h3, h4⟩ := filter_surj P l k h
        refine ⟨i + 1, x, by simpa using h1, h2, ?_, h4⟩
        rw [List.take_succ_cons, List.filter_cons_of_neg ha, h3]

theorem rank_lt (cs : List (BitVec 12)) (i : Nat) (hi : i < cs.length) (hv : accB cs[i] = true) :
    ((cs.take i).filter accB).length < (cs.filter accB).length := by
  have hsub := ((List.take_sublist (i + 1) cs).filter accB).length_le
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.filter_append,
    List.length_append] at hsub
  simp only [List.filter_cons, List.filter_nil, hv, if_true, List.length_cons, List.length_nil] at hsub
  omega

theorem headD_drop {α : Type} (l : List α) (n : Nat) (d : α) : (l.drop n).headD d = l.getD n d := by
  rw [List.headD_eq_head?_getD, List.head?_drop, List.getD_eq_getElem?_getD]

/-- The kernels' network output on candidates `cs`. -/
abbrev finalOf (cs : List (BitVec 12)) : List KCell :=
  (List.range 9).foldl (fun st s => MlKemFast.stage FO s st)
    (MlKemFast.cells FO cs (List.replicate MlKemFast.distBits MlKemFast.concrete.zero))

theorem final_facts (cs : List (BitVec 12)) (h3 : cs.length ≤ 512) :
    (finalOf cs).length = cs.length ∧
    (∀ k, k < (cs.filter accB).length →
      ∃ c : KCell, (finalOf cs)[k]? = some c ∧ c.valid = 1#1 ∧ some c.data = (cs.filter accB)[k]?) ∧
    (∀ k, (cs.filter accB).length ≤ k → k < cs.length →
      ∃ c : KCell, (finalOf cs)[k]? = some c ∧ c.valid = 0#1) := by
  have g := cells_good cs h3
  have hlen := cells_length cs (List.replicate MlKemFast.distBits MlKemFast.concrete.zero)
  obtain ⟨flen, fat, fonly⟩ := compact_spec _ 9 g (by rw [hlen]; exact h3)
  refine ⟨by rw [← hlen]; exact flen, ?_, ?_⟩
  · intro k hk
    obtain ⟨i, x, hx, hpx, hrank, hfk⟩ := filter_surj accB cs k hk
    obtain ⟨hi, hxi⟩ := List.getElem?_eq_some_iff.mp hx
    have hvi : vld (MlKemFast.cells FO cs (List.replicate MlKemFast.distBits MlKemFast.concrete.zero)) i = true := by
      rw [vld_cells cs _ i hi, List.getD_eq_getElem?_getD, hx]; exact hpx
    have hr := rej_rank cs i (by omega)
    rw [← rej_cells cs (List.replicate MlKemFast.distBits MlKemFast.concrete.zero) i (by omega)] at hr
    have at_i := fat i (by rw [hlen]; exact hi) hvi
    rw [show i - rej (vld (MlKemFast.cells FO cs (List.replicate MlKemFast.distBits MlKemFast.concrete.zero))) i = k
      by omega] at at_i
    obtain ⟨hv, hd⟩ := cells_getD cs (List.replicate MlKemFast.distBits MlKemFast.concrete.zero) i hi
    refine ⟨_, at_i, ?_, ?_⟩
    · rw [hv, ltQ_value, hxi, hpx]; rfl
    · rw [hd, hxi, hfk]
  · intro k hmk hkN
    have hk : k < (finalOf cs).length := by
      have : (finalOf cs).length = cs.length := by rw [← hlen]; exact flen
      omega
    refine ⟨(finalOf cs)[k], List.getElem?_eq_getElem hk, ?_⟩
    rcases bv1 ((finalOf cs)[k]).valid with h0 | h1
    · exact h0
    · obtain ⟨i, hi, hvi, hti⟩ := fonly k _ (List.getElem?_eq_getElem hk) h1
      rw [hlen] at hi
      have hacc : accB cs[i] = true := by
        rw [vld_cells cs _ i hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at hvi
        exact hvi
      have hr := rej_rank cs i (by omega)
      rw [← rej_cells cs (List.replicate MlKemFast.distBits MlKemFast.concrete.zero) i (by omega)] at hr
      have := rank_lt cs i hi hacc
      omega

/-- The kernels' sampler keeps the first `count` candidates below q, or returns zeros and status 0:
for any number of candidates up to 512 (the network has nine stages). -/
theorem sample_eq (count : Nat) (cs : List (BitVec 12)) (h1 : 0 < count) (h2 : count ≤ cs.length)
    (h3 : cs.length ≤ 512) : MlKemFast.sample FO count cs = MlKemFast.firstAccepted count cs := by
  obtain ⟨flen, fA, fB⟩ := final_facts cs h3
  have hs : MlKemFast.sample FO count cs = ((((finalOf cs).drop (count - 1)).headD EC).valid,
      ((finalOf cs).take count).map (fun c => MlKemFast.concrete.select (((finalOf cs).drop (count - 1)).headD EC).valid
        c.data (MlKemFast.concrete.const 0))) := rfl
  have hf : MlKemFast.firstAccepted count cs = if count ≤ (cs.filter accB).length then
      (1#1, (cs.filter accB).take count) else (0#1, List.replicate count 0) := rfl
  rw [hs, hf, headD_drop]
  generalize finalOf cs = fin at flen fA fB
  by_cases hc : count ≤ (cs.filter accB).length
  · obtain ⟨c, hc1, hc2, _⟩ := fA (count - 1) (by omega)
    rw [getD_eq_of_getElem? _ _ _ _ hc1, hc2, if_pos hc]
    congr 1
    apply List.ext_getElem?
    intro k
    rw [List.getElem?_map, List.getElem?_take, List.getElem?_take]
    by_cases hk : k < count
    · rw [if_pos hk, if_pos hk]
      obtain ⟨c', h1', _, h3'⟩ := fA k (by omega)
      rw [h1', ← h3', Option.map_some, select_one]
    · rw [if_neg hk, if_neg hk]; rfl
  · obtain ⟨c, hc1, hc2⟩ := fB (count - 1) (by omega) (by omega)
    rw [getD_eq_of_getElem? _ _ _ _ hc1, hc2, if_neg hc]
    congr 1
    apply List.ext_getElem?
    intro k
    rw [List.getElem?_map, List.getElem?_take, List.getElem?_replicate]
    by_cases hk : k < count
    · rw [if_pos hk, if_pos hk, List.getElem?_eq_getElem (by omega), Option.map_some, select_zero]; rfl
    · rw [if_neg hk, if_neg hk]; rfl

/-- At the kernels' size: 448 candidates, 256 kept. -/
theorem sample_448 (cs : List (BitVec 12)) (h : cs.length = 448) :
    MlKemFast.sample FO 256 cs = MlKemFast.firstAccepted 256 cs :=
  sample_eq 256 cs (by decide) (by omega) (by omega)

/-! ### The specification's sampler (`MlKemSample`, 64-bit words) -/

local notation "WO" => Word64.concrete
local notation "BA" => ByteAuth.concrete
local notation "SH" => Sha256.concrete

def acc64 (x : BitVec 64) : Bool := decide (x.toNat < 3329)

/-- The specification's sampler state after the candidates `pre`: the number accepted and the
first `count` accepted ones (zeros after). -/
def specState (count : Nat) (pre : List (BitVec 64)) : MlKemSample.State (BitVec 64) :=
  ⟨BitVec.ofNat 64 (pre.filter acc64).length, (List.range count).map (fun i => (pre.filter acc64).getD i 0#64)⟩

theorem state_eta (s : MlKemSample.State (BitVec 64)) : s = ⟨s.accepted, s.coefficients⟩ := by
  cases s; rfl

theorem bytes64_inj (x y : BitVec 64) (h : Word64.bytes WO x = Word64.bytes WO y) : x = y := by
  have hb : ∀ k, k < 8 → x.extractLsb' (8 * (7 - k)) 8 = y.extractLsb' (8 * (7 - k)) 8 := by
    intro k hk
    have e := congrArg (fun l => l[k]?) h
    simp only [Word64.bytes, List.getElem?_map, List.getElem?_range hk, Option.map_some] at e
    exact Option.some.inj e
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have e := congrArg (fun z => z.getLsbD (j % 8)) (hb (7 - j / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb'] at e
  rw [show 8 * (7 - (7 - j / 8)) + j % 8 = j by omega] at e
  simpa [show j % 8 < 8 by omega] using e

theorem eq_value (m i : Nat) (hm : m < 2 ^ 64) (hi : i < 2 ^ 64) :
    Word64.eq WO BA (BitVec.ofNat 64 m) (Word64.concrete.const i) = if m = i then 255 else 0 := by
  unfold Word64.eq
  rw [ByteAuth.equalMask_value]
  by_cases h : m = i
  · subst h; rw [if_pos rfl]; exact if_pos rfl
  · rw [if_neg h, if_neg]
    intro hb
    have e := congrArg BitVec.toNat (bytes64_inj _ _ hb)
    have e' : (BitVec.ofNat 64 m).toNat = (BitVec.ofNat 64 i).toNat := e
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hi] at e'
    exact h e'

theorem and255 : ByteAuth.concrete.and 255 255 = 255 := by decide
theorem and255l (y : BitVec 8) : ByteAuth.concrete.and 255 y = y := by
  show (255 : BitVec 8) &&& y = y
  rw [show (255 : BitVec 8) = BitVec.allOnes 8 by decide, BitVec.allOnes_and]
theorem and0l (y : BitVec 8) : ByteAuth.concrete.and 0 y = 0 := BitVec.zero_and
theorem and0r (y : BitVec 8) : ByteAuth.concrete.and y 0 = 0 := BitVec.and_zero

theorem getD_append_single (F : List (BitVec 64)) (c : BitVec 64) (k : Nat) :
    (F ++ [c]).getD k 0#64 = if k = F.length then c else F.getD k 0#64 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases h : k < F.length
  · rw [List.getElem?_append_left h, if_neg (by omega)]
  · rw [List.getElem?_append_right (by omega), List.getElem?_singleton, List.getElem?_eq_none (by omega)]
    by_cases hk : k = F.length
    · rw [if_pos (by omega), if_pos hk]; rfl
    · rw [if_neg (by omega), if_neg hk]

theorem ule_3328 (c : BitVec 64) : Word64.concrete.ule c (Word64.concrete.const 3328) = if acc64 c then 255 else 0 := by
  rw [Word64.ule_value]
  have h3 : (Word64.concrete.const 3328).toNat = 3328 := rfl
  rw [h3]
  by_cases h : c.toNat < 3329
  · rw [if_pos (by omega), show acc64 c = true by simp [acc64, h]]; rfl
  · rw [if_neg (by omega), show acc64 c = false by simp [acc64, h]]; rfl

theorem step_spec (count : Nat) (hcount : count ≤ 4096) (pre : List (BitVec 64)) (c : BitVec 64)
    (hpre : pre.length < 4096) :
    MlKemSample.step WO BA (specState count pre) c = specState count (pre ++ [c]) := by
  have hf : (pre ++ [c]).filter acc64 = pre.filter acc64 ++ (if acc64 c then [c] else []) := by
    rw [List.filter_append, List.filter_cons, List.filter_nil]
  have hm : (pre.filter acc64).length ≤ pre.length := List.length_filter_le _ _
  have hacc := MlKemSample.step_count (specState count pre) c
  rw [state_eta (MlKemSample.step WO BA (specState count pre) c), hacc]
  simp only [specState]
  congr 1
  · rw [hf]
    by_cases h : c.toNat < 3329
    · rw [if_pos h, show acc64 c = true by simp [acc64, h], if_pos rfl, List.length_append, List.length_singleton,
        BitVec.ofNat_add]
      rfl
    · rw [if_neg h, show acc64 c = false by simp [acc64, h], if_neg (by decide), List.append_nil]
      exact BitVec.add_zero _
  · apply List.ext_getElem?
    intro k
    simp only [MlKemSample.step, List.getElem?_map, List.getElem?_zipIdx]
    by_cases hk : k < count
    · rw [List.getElem?_range hk]
      simp only [Option.map_some, Nat.zero_add]
      rw [ule_3328, eq_value _ _ (by omega) (by omega), hf]
      congr 1
      by_cases ha : acc64 c = true
      · rw [if_pos ha, if_pos ha, getD_append_single]
        by_cases he : (pre.filter acc64).length = k
        · rw [if_pos he, if_pos he.symm, and255, Word64.select_accept]
        · rw [if_neg he, if_neg (Ne.symm he), and0r, Word64.select_reject]
      · rw [if_neg ha, if_neg ha, and0l, Word64.select_reject, List.append_nil]
    · rw [List.getElem?_eq_none (by simp; omega)]
      rfl

theorem fold_spec (count : Nat) (hcount : count ≤ 4096) : ∀ (rest pre : List (BitVec 64)),
    pre.length + rest.length ≤ 4096 →
    rest.foldl (MlKemSample.step WO BA) (specState count pre) = specState count (pre ++ rest)
  | [], pre, _ => by simp
  | c :: rest, pre, h => by
      simp only [List.length_cons] at h
      rw [List.foldl_cons, step_spec count hcount pre c (by omega),
        fold_spec count hcount rest (pre ++ [c]) (by simp; omega)]
      simp

theorem sample_spec (count : Nat) (hcount : count ≤ 4096) (values : List (BitVec 64)) (h : values.length ≤ 4096) :
    MlKemSample.sample WO BA count values = specState count values := by
  have h0 : (⟨Word64.concrete.const 0, List.replicate count (Word64.concrete.const 0)⟩ : MlKemSample.State (BitVec 64)) =
      specState count [] := by
    simp only [specState, List.filter_nil, List.length_nil, List.getD_nil, List.map_const', List.length_range]
    rfl
  unfold MlKemSample.sample
  rw [h0, fold_spec count hcount values [] (by simpa using h)]
  rfl

/-! The candidates: three bytes give two little-endian 12-bit values, which are `decode12`'s. -/

theorem pack_two (x y : BitVec 8) :
    Word64.concrete.pack (List.replicate 6 (ByteAuth.concrete.const 0) ++ [x, y]) =
      ((0#8 ++ 0#8) ++ (0#8 ++ 0#8)) ++ ((0#8 ++ 0#8) ++ (x ++ y)) := rfl

theorem pack_two_getLsbD (x y : BitVec 8) (j : Nat) :
    (Word64.concrete.pack (List.replicate 6 (ByteAuth.concrete.const 0) ++ [x, y])).getLsbD j =
      (if j < 8 then y.getLsbD j else if j < 16 then x.getLsbD (j - 8) else false) := by
  rw [pack_two]
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_zero]
  by_cases h8 : j < 8
  · simp [h8, show j < 16 by omega, show j < 32 by omega]
  · by_cases h16 : j < 16
    · simp [h8, h16, show j < 32 by omega, show j - 8 < 8 by omega]
    · by_cases h32 : j < 32 <;> simp [h8, h16, h32]

theorem bitAt_idx (raw : List (BitVec 8)) (q r : Nat) (hr : r < 8) (n : Nat) (hn : n = 8 * q + r) :
    KemEncoding.bitAt raw n = (raw[q]?.getD 0#8).getLsbD r := by
  subst hn; exact KemEncoding.bitAt_eq raw q r hr

theorem candidates_eq (pairs : Nat) (raw : List (BitVec 8)) :
    MlKemSample.candidates WO BA pairs raw = (MlKemFast.decode12 FO (2 * pairs) raw).map (BitVec.setWidth 64) := by
  have hg : ∀ k, OpenResult.get BA raw k = raw[k]?.getD 0#8 := fun _ => rfl
  apply List.ext_getElem?
  intro n
  rw [MlKemSample.candidates, KemEncoding.flatMap_getElem? _ 2 (by decide) (fun _ => rfl)]
  simp only [MlKemFast.decode12, List.getElem?_map]
  by_cases hn : n < 2 * pairs
  · rw [List.getElem?_range (show n / 2 < pairs by omega), List.getElem?_range hn]
    simp only [Option.bind_some, Option.map_some]
    obtain ⟨i, hi⟩ : ∃ i, n = 2 * i ∨ n = 2 * i + 1 := ⟨n / 2, by omega⟩
    rcases hi with rfl | rfl
    · rw [show 2 * i / 2 = i by omega, show 2 * i % 2 = 0 by omega]
      simp only [MlKemSample.pair, List.getElem?_cons_zero, hg]
      congr 1
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      rw [BitVec.getLsbD_setWidth, KemEncoding.decode12_coeff_getLsbD]
      show ((Word64.concrete.pack _) &&& BitVec.ofNat 64 4095).getLsbD j = _
      rw [BitVec.getLsbD_and, pack_two_getLsbD, BitVec.getLsbD_ofNat,
        show (4095 : Nat) = 2 ^ 12 - 1 from rfl, Nat.testBit_two_pow_sub_one]
      by_cases h8 : j < 8
      · rw [bitAt_idx raw (3 * i) j h8 _ (by omega)]
        simp [h8, show j < 12 by omega, hj]
      · by_cases h12 : j < 12
        · rw [bitAt_idx raw (3 * i + 1) (j - 8) (by omega) _ (by omega)]
          simp [h8, h12, hj, show j < 16 by omega]
        · simp [h8, h12]
    · rw [show (2 * i + 1) / 2 = i by omega, show (2 * i + 1) % 2 = 1 by omega]
      simp only [MlKemSample.pair, List.getElem?_cons_succ, List.getElem?_cons_zero, hg]
      congr 1
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      rw [BitVec.getLsbD_setWidth, KemEncoding.decode12_coeff_getLsbD]
      show ((Word64.concrete.pack _) >>> 4).getLsbD j = _
      rw [BitVec.getLsbD_ushiftRight, pack_two_getLsbD]
      by_cases h4 : j < 4
      · rw [bitAt_idx raw (3 * i + 1) (4 + j) (by omega) _ (by omega)]
        simp [h4, show j < 12 by omega, hj, show 4 + j < 8 by omega]
      · by_cases h12 : j < 12
        · rw [bitAt_idx raw (3 * i + 2) (j - 4) (by omega) _ (by omega)]
          simp [h12, hj, show ¬ 4 + j < 8 by omega, show 4 + j < 16 by omega, show 4 + j - 8 = j - 4 by omega]
        · simp [h12, show ¬ 4 + j < 8 by omega, show ¬ 4 + j < 16 by omega]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
    rfl

/-! The serialised entry and its status, against the kernels' sampler. -/

theorem pack_low (x : BitVec 64) (hx : x.toNat < 65536) :
    Sha256.concrete.pack (Sha256.concrete.byteConst 0) (Sha256.concrete.byteConst 0) (Word64.concrete.unpack x 6) (Word64.concrete.unpack x 7) = x.setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [Sha256.concrete, Word64.concrete, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ofNat, BitVec.getLsbD_setWidth]
  by_cases h8 : j < 8
  · simp [h8, show j < 16 by omega, hj]
  · by_cases h16 : j < 16
    · simp [h8, h16, hj, show j - 8 < 8 by omega, show 8 + (j - 8) = j by omega]
    · have hz : x.getLsbD j = false := by
        simp only [BitVec.getLsbD]
        exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (by
          have : 2 ^ 16 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
          simpa using this))
      simp [h16, hz, hj]

theorem filter_widen (cs : List (BitVec 12)) :
    (cs.map (BitVec.setWidth 64)).filter acc64 = (cs.filter accB).map (BitVec.setWidth 64) := by
  rw [List.filter_map]
  congr 1

theorem maskByte_value (t : BitVec 1) : MlKemFast.maskByte FO t = if t = 1#1 then 255 else 0 := by
  rcases bv1 t with rfl | rfl <;> decide

theorem firstAccepted_eq (count : Nat) (cs : List (BitVec 12)) :
    MlKemFast.firstAccepted count cs = if count ≤ (cs.filter accB).length then
      (1#1, (cs.filter accB).take count) else (0#1, List.replicate count 0) := rfl

theorem run_parts (raw : List (BitVec 8)) :
    MlKemSample.run WO BA 256 224 raw =
      MlKemSample.finish WO BA 256 (specState 256 ((MlKemFast.decode12 FO 448 raw).map (BitVec.setWidth 64))) := by
  unfold MlKemSample.run
  rw [candidates_eq, show 2 * 224 = 448 from rfl,
    sample_spec 256 (by decide) _ (by simp [KemEncoding.decode12_length])]

theorem success_value (cs : List (BitVec 12)) (hm : (cs.filter accB).length ≤ 448) :
    Word64.concrete.ule (Word64.concrete.const 256) (specState 256 (cs.map (BitVec.setWidth 64))).accepted =
      if 256 ≤ (cs.filter accB).length then 255 else 0 := by
  simp only [specState]
  rw [Word64.ule_value, filter_widen, List.length_map]
  have h1 : (Word64.concrete.const 256).toNat = 256 := rfl
  have h2 : (BitVec.ofNat 64 (cs.filter accB).length).toNat = (cs.filter accB).length := by
    rw [BitVec.toNat_ofNat]; omega
  rw [h1, h2]

/-- The status byte of the specification's sampler is the kernels' `maskByte` of their status bit. -/
theorem run_status (raw : List (BitVec 8)) :
    OpenResult.get BA (MlKemSample.run WO BA 256 224 raw) 0 =
      MlKemFast.maskByte FO (MlKemFast.sample FO 256 (MlKemFast.decode12 FO 448 raw)).1 := by
  rw [run_parts, sample_448 _ (KemEncoding.decode12_length 448 raw), firstAccepted_eq, maskByte_value]
  generalize hcs : MlKemFast.decode12 FO 448 raw = cs
  have hl : cs.length = 448 := by rw [← hcs, KemEncoding.decode12_length]
  have hm : (cs.filter accB).length ≤ 448 := by have := List.length_filter_le accB cs; omega
  show Word64.concrete.ule (Word64.concrete.const 256) (specState 256 (cs.map (BitVec.setWidth 64))).accepted = _
  rw [success_value cs hm]
  by_cases h : 256 ≤ (cs.filter accB).length
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h]; rfl

/-- The specification's sampled polynomial (after its 16-bit serialisation and `decodePoly`) is the
kernels' sampled polynomial, zero-extended: the first 256 candidates below q, or zeros. -/
theorem run_refines (raw : List (BitVec 8)) :
    MlKemNtt.decodePoly SH BA ((MlKemSample.run WO BA 256 224 raw).drop 1) =
      (MlKemFast.sample FO 256 (MlKemFast.decode12 FO 448 raw)).2.map MlKemFast.wide := by
  rw [run_parts, sample_448 _ (KemEncoding.decode12_length 448 raw), firstAccepted_eq]
  generalize hcs : MlKemFast.decode12 FO 448 raw = cs
  have hl : cs.length = 448 := by rw [← hcs, KemEncoding.decode12_length]
  have hm : (cs.filter accB).length ≤ 448 := by have := List.length_filter_le accB cs; omega
  have hsucc := success_value cs hm
  simp only [MlKemSample.finish, List.drop_succ_cons, List.drop_zero]
  generalize Word64.concrete.ule (Word64.concrete.const 256) (specState 256 (cs.map (BitVec.setWidth 64))).accepted
    = succ at hsucc
  have lens : ∀ x : BitVec 64, ([ByteAuth.concrete.and succ (Word64.concrete.unpack x 7),
      ByteAuth.concrete.and succ (Word64.concrete.unpack x 6)] : List (BitVec 8)).length = 2 := fun _ => rfl
  apply List.ext_getElem?
  intro k
  simp only [MlKemNtt.decodePoly, List.getElem?_map]
  by_cases hk : k < 256
  · rw [List.getElem?_range hk, Option.map_some]
    have hc : (specState 256 (cs.map (BitVec.setWidth 64))).coefficients[k]? =
        some (((cs.filter accB).map (BitVec.setWidth 64)).getD k 0#64) := by
      simp only [specState, List.getElem?_map, List.getElem?_range hk, Option.map_some, filter_widen]
    have g0 : OpenResult.get BA ((specState 256 (cs.map (BitVec.setWidth 64))).coefficients.flatMap
        (fun x => [ByteAuth.concrete.and succ (Word64.concrete.unpack x 7),
          ByteAuth.concrete.and succ (Word64.concrete.unpack x 6)])) (2 * k) =
        ByteAuth.concrete.and succ (Word64.concrete.unpack (((cs.filter accB).map (BitVec.setWidth 64)).getD k 0#64) 7) := by
      simp only [OpenResult.get]
      rw [KemEncoding.flatMap_getElem? _ 2 (by decide) lens, show 2 * k / 2 = k by omega,
        show 2 * k % 2 = 0 by omega, hc]
      rfl
    have g1 : OpenResult.get BA ((specState 256 (cs.map (BitVec.setWidth 64))).coefficients.flatMap
        (fun x => [ByteAuth.concrete.and succ (Word64.concrete.unpack x 7),
          ByteAuth.concrete.and succ (Word64.concrete.unpack x 6)])) (2 * k + 1) =
        ByteAuth.concrete.and succ (Word64.concrete.unpack (((cs.filter accB).map (BitVec.setWidth 64)).getD k 0#64) 6) := by
      simp only [OpenResult.get]
      rw [KemEncoding.flatMap_getElem? _ 2 (by decide) lens, show (2 * k + 1) / 2 = k by omega,
        show (2 * k + 1) % 2 = 1 by omega, hc]
      rfl
    rw [g0, g1, hsucc]
    by_cases h : 256 ≤ (cs.filter accB).length
    · rw [if_pos h, if_pos h, and255l, and255l]
      dsimp only
      rw [List.getElem?_take, if_pos hk]
      have hk' : k < (cs.filter accB).length := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk', Option.map_some,
        Option.getD_some, Option.map_some]
      congr 1
      have hx : ((cs.filter accB)[k].setWidth 64).toNat < 65536 := by
        rw [BitVec.toNat_setWidth]
        have := ((cs.filter accB)[k]).isLt
        omega
      rw [pack_low _ hx, BitVec.setWidth_setWidth_of_le _ (by decide)]
      rfl
    · rw [if_neg h, if_neg h, and0l, and0l]
      dsimp only
      rw [List.getElem?_replicate, if_pos hk, Option.map_some]
      rfl
  · rw [List.getElem?_eq_none (by simp; omega)]
    by_cases h : 256 ≤ (cs.filter accB).length
    · rw [if_pos h]
      dsimp only
      rw [List.getElem?_take, if_neg hk]; rfl
    · rw [if_neg h]
      dsimp only
      rw [List.getElem?_replicate, if_neg hk]; rfl

/-- One matrix entry: the specification's `MlKemSample.matrix … 256 224` against the kernels' `entry`
(the same SHAKE128 stream: `3·224 = 672` bytes). -/
theorem entry_refines (seed : List (BitVec 8)) :
    MlKemNtt.decodePoly SH BA ((MlKemSample.matrix WO BA Keccak.concrete 256 224 seed).drop 1) =
      (MlKemFast.entry FO Keccak.concrete seed).2.map MlKemFast.wide := run_refines _

theorem entry_status (seed : List (BitVec 8)) :
    OpenResult.get BA (MlKemSample.matrix WO BA Keccak.concrete 256 224 seed) 0 =
      MlKemFast.maskByte FO (MlKemFast.entry FO Keccak.concrete seed).1 := run_status _

theorem entry_canon (seed : List (BitVec 8)) : MlKemFast.Canon (MlKemFast.entry FO Keccak.concrete seed).2 := by
  unfold MlKemFast.entry
  rw [sample_448 _ (KemEncoding.decode12_length 448 _), firstAccepted_eq]
  intro x hx
  split at hx
  · have := List.mem_of_mem_take hx
    exact of_decide_eq_true (List.mem_filter.mp this).2
  · rw [List.eq_of_mem_replicate hx]; decide

theorem entry_length (seed : List (BitVec 8)) : (MlKemFast.entry FO Keccak.concrete seed).2.length = 256 := by
  unfold MlKemFast.entry
  rw [sample_448 _ (KemEncoding.decode12_length 448 _), firstAccepted_eq]
  split
  · rename_i h
    dsimp only
    rw [List.length_take]
    omega
  · exact List.length_replicate
#print axioms compact_spec
#print axioms sample_eq
#print axioms run_refines
#print axioms run_status

end TlsMpc.KernelSpecs.KemSample
