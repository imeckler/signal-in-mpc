import TlsMpc.Node.Flows.MasksRun
import TlsMpc.Node.Flows.RunAgree

/-!
# `Masks.generate`: the engines' state, phase by phase

Stage S10. What each block of `Masks.generate` does to the ideal state of `Engine/Model.lean`, as
pure statements about `runLocal`, lookups and `runProgram` (no run, no adversary). The run-level
theorems are built on these: hiding (`MasksHiding.lean`), detection by the flags and the bit blocks
and the honest run (`MasksSound.lean`).

`Holds p b f I v x`: the engines hold the candidates `x`: handle `b + 2` is the bundle `v` of both
owners' bits (A ‖ B, 2·M·255 bits) of which `x.bits o c` is candidate `c` of owner `o`, and the
candidate field handles hold `x.elem o c`. True after the input block of any run (the other
party's candidates are whatever it input, independently per engine), and kept by the cut and the
bucket phases.

  * `Holds.cut`, `Holds.bucket`: the cut and the bucket blocks open `cutRel x`, `bucketRel x`
    (the protocol layer's definitions, `MasksProofs.lean`).
  * `outsOf`, `flagsOf`, `Holds.final`: the finalize block: the bundle `b + 10` is, per kept
    reference `j`, the 256 bits of `finalize-bits` (`j < bits`) or `finalize-mask` on the two
    owners' references; the flags `b + 11` are their last bits.
  * `Holds.masks`: the word masks: the Boolean handle `b + 12 + j` holds the first 255 bits of
    kept reference `bits + j`'s output, the field handle `maskBase + j` the sum of the two
    references' elements.
  * `CoinsHold`, `bitZ`, `coins_programs`, `coins_xor`: the bit-block phase's program steps: what
    the recomposition and the bit checks open, and the bit pairs.
-/

namespace TlsMpc.Node.Flows.Masks

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs openThen frees Silent blankWire)
open TlsMpc.Node.Flows.Run
open TlsMpc.Node.Flows.Conv
open TlsMpc.FieldDag (F modulus)

/-! ## Lists -/

theorem map_getD_range {α : Type} (l : List α) (d : α) (lo n : Nat) (h : lo + n ≤ l.length) :
    (List.range n).map (fun i => l.getD (lo + i) d) = (l.drop lo).take n := by
  apply List.ext_getElem
  · simp
    omega
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show lo + i < l.length by omega)]

theorem length_flatten_eq {α : Type} (w : Nat) : ∀ (L : List (List α)), (∀ x ∈ L, x.length = w) →
    L.flatten.length = L.length * w
  | [], _ => by simp
  | x :: L, h => by
    rw [List.flatten_cons, List.length_append, h x (by simp),
      length_flatten_eq w L (fun y hy => h y (by simp [hy])), List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem flatten_drop_take {α : Type} (w : Nat) : ∀ (L : List (List α)) (j : Nat), (∀ x ∈ L, x.length = w) →
    j < L.length → (L.flatten.drop (j * w)).take w = L.getD j []
  | [], j, _, hj => by simp at hj
  | x :: L, 0, h, _ => by
    have hx := h x (by simp)
    simp [List.take_left' hx]
  | x :: L, j + 1, h, hj => by
    have hx := h x (by simp)
    have ih := flatten_drop_take w L j (fun y hy => h y (by simp [hy])) (by simpa using hj)
    rw [List.flatten_cons, show (j + 1) * w = x.length + j * w by rw [hx, Nat.add_mul, Nat.one_mul, Nat.add_comm],
      List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left, ih]
    simp

theorem flatten_getD {α : Type} (w : Nat) (L : List (List α)) (j i : Nat) (d : α) (h : ∀ x ∈ L, x.length = w)
    (hj : j < L.length) (hi : i < w) : L.flatten.getD (j * w + i) d = (L.getD j []).getD i d := by
  rw [← flatten_drop_take w L j h hj]
  simp [List.getD_eq_getElem?_getD, hi]

theorem flatten_map_nil {α β : Type} (l : List α) : (l.map fun _ => ([] : List β)).flatten = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp

theorem mapM_vals {α β : Type} (look : α → Option β) (val : α → β) :
    ∀ (l : List α), (∀ h ∈ l, look h = some (val h)) → l.mapM look = some (l.map val)
  | [], _ => rfl
  | h :: l, hl => by
    simp [List.mapM_cons, hl h (by simp), mapM_vals look val l (fun g hg => hl g (by simp [hg]))]

theorem flatMap_congr' {α β : Type} (l : List α) (g g' : α → List β) (h : ∀ a ∈ l, g a = g' a) :
    l.flatMap g = l.flatMap g' := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem map_range_add (base n : Nat) : (List.range n).map (fun i => base + i) = List.range' base n := by
  apply List.ext_getElem <;> simp

theorem getD_map_range {α : Type} (g : Nat → α) (n i : Nat) (d : α) (hi : i < n) :
    ((List.range n).map g).getD i d = g i := by
  simp [List.getD_eq_getElem?_getD, hi]

/-! ## Field handles set in blocks -/

theorem setFields_spec : ∀ (hs : List FieldH) (vs : List F) (I : Ideal), vs.length = hs.length →
    (hs.map (·.id)).Nodup →
    (I.setFields hs vs).bools = I.bools ∧
    (∀ j, (∀ h ∈ hs, h.id ≠ j) → (I.setFields hs vs).fields j = I.fields j) ∧
    (∀ i, i < hs.length → (I.setFields hs vs).fields (hs.getD i ⟨0⟩).id = some (vs.getD i 0))
  | [], [], I, _, _ => ⟨rfl, fun _ _ => rfl, fun i hi => by simp at hi⟩
  | h :: hs, v :: vs, I, hl, hn => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    obtain ⟨b1, b2, b3⟩ := setFields_spec hs vs (I.setField h v) (by simpa using hl) hn.2
    refine ⟨b1, fun j hj => ?_, fun i hi => ?_⟩
    · show ((I.setField h v).setFields hs vs).fields j = _
      rw [b2 j (fun g hg => hj g (by simp [hg]))]
      simp only [Ideal.setField]
      rw [if_neg (Ne.symm (hj h (by simp)))]
    · cases i with
      | zero =>
        show ((I.setField h v).setFields hs vs).fields h.id = some v
        rw [b2 h.id (fun g hg e => hn.1 ⟨g, hg, e⟩)]
        simp [Ideal.setField]
      | succ i =>
        have := b3 i (by simpa using hi)
        show ((I.setField h v).setFields hs vs).fields ((h :: hs).getD (i + 1) ⟨0⟩).id = some ((v :: vs).getD (i + 1) 0)
        simpa using this
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl

/-- A block of consecutive field handles `base, …, base + n − 1` set to `vs`. -/
theorem setFields_block (I : Ideal) (g : Nat → FieldH) (base n : Nat) (vs : List F)
    (hg : ∀ i, i < n → (g i).id = base + i) (hl : vs.length = n) :
    (I.setFields ((List.range n).map g) vs).bools = I.bools ∧
    (∀ j, (j < base ∨ base + n ≤ j) → (I.setFields ((List.range n).map g) vs).fields j = I.fields j) ∧
    (∀ i, i < n → (I.setFields ((List.range n).map g) vs).fields (base + i) = some (vs.getD i 0)) := by
  have hids : ((List.range n).map g).map (·.id) = List.range' base n := by
    rw [List.map_map, ← map_range_add]
    apply List.map_congr_left
    intro i hi
    exact hg i (List.mem_range.mp hi)
  obtain ⟨b1, b2, b3⟩ := setFields_spec ((List.range n).map g) vs I (by simpa using hl)
    (by rw [hids]; exact List.nodup_range')
  refine ⟨b1, fun j hj => b2 j (fun h hh e => ?_), fun i hi => ?_⟩
  · simp only [List.mem_map, List.mem_range] at hh
    obtain ⟨i, hi, rfl⟩ := hh
    have := hg i hi
    omega
  · have := b3 i (by simpa using hi)
    rw [getD_map_range g n i _ hi, hg i hi] at this
    exact this

/-! ## The candidates in the engines -/

/-- **The engines hold the candidates `x`**: handle `b + 2` is the bundle `v` (A ‖ B) whose words
are `x.bits`, and the candidate field handles hold `x.elem`. -/
structure Holds (p : Params) (b f : Nat) (I : Ideal) (v : Bits) (x : Vals) : Prop where
  hv : I.bools (b + 2) = some v
  hlen : v.length = 2 * (p.M * W)
  hbits : ∀ o c, x.bits o c = (wordAt p o c).map (v.getD · false)
  hfld : ∀ o, o < 2 → ∀ c, c < p.M → I.fields (fOf p f o c).id = some (x.elem o c)

theorem bitAt_lt (p : Params) (o c i : Nat) (ho : o < 2) (hc : c < p.M) (hi : i < W) :
    bitAt p o c i < 2 * (p.M * W) := by
  have hW : (c + 1) * W ≤ p.M * W := Nat.mul_le_mul_right _ hc
  have h1 : o * (p.M * W) ≤ 1 * (p.M * W) := Nat.mul_le_mul_right _ (by omega)
  simp only [Nat.succ_mul] at hW
  unfold bitAt
  omega

theorem fOf_id_lt (p : Params) (f o c : Nat) (ho : o < 2) (hc : c < p.M) : (fOf p f o c).id < f + 2 * p.M := by
  have h1 : o * p.M ≤ 1 * p.M := Nat.mul_le_mul_right _ (by omega)
  simp only [fOf]
  omega

namespace Holds

variable {p : Params} {b f : Nat} {I : Ideal} {v : Bits} {x : Vals}

theorem wide (h : Holds p b f I v x) : x.Wide := by
  intro o c
  rw [h.hbits]
  simp [wordAt]

/-- A state with the same candidate bundle and the same candidate field handles holds them too. -/
theorem frame (h : Holds p b f I v x) {I' : Ideal} (hb : I'.bools (b + 2) = I.bools (b + 2))
    (hf : ∀ j, j < f + 2 * p.M → I'.fields j = I.fields j) : Holds p b f I' v x :=
  ⟨by rw [hb]; exact h.hv, h.hlen, h.hbits, fun o ho c hc => by
    rw [hf _ (fOf_id_lt p f o c ho hc)]; exact h.hfld o ho c hc⟩

/-- A word of the bundle, read through `pick`. -/
theorem word_idx (h : Holds p b f I v x) (o c : Nat) (ho : o < 2) (hc : c < p.M) :
    ∀ i ∈ wordAt p o c, i < v.length := by
  intro i hi
  simp only [wordAt, List.mem_map, List.mem_range] at hi
  obtain ⟨k, hk, rfl⟩ := hi
  rw [h.hlen]
  exact bitAt_lt p o c k ho hc hk

end Holds

theorem owners_lt {o : Nat} (ho : o ∈ owners) : o < 2 := by
  simp only [owners, List.mem_cons, List.not_mem_nil, or_false] at ho
  omega

/-! ## The cut block -/

section CutBlock

variable (E : Env) {p : Params} {b f : Nat} {I : Ideal} {v : Bits} {x : Vals}

theorem cutBits_map (h : Holds p b f I v x) (π₁ : List Nat) :
    (cutBits p π₁).map (v.getD · false) = ((cutRel x (cutOf p π₁)).map Prod.fst).flatten := by
  simp only [cutBits, cutRel, List.map_flatMap, List.map_map, Function.comp_def, flatten_flatMap',
    flatten_map', h.hbits]

/-- **The cut block**: the pick `b + 3` holds the cut candidates' words, and the cut's field
handles their elements: exactly `cutRel x`. -/
theorem Holds.cut (h : Holds p b f I v x) (π₁ : List Nat) (hπ : ∀ c ∈ cutOf p π₁, c < p.M) :
    runLocal E [.pick ⟨b + 3⟩ ⟨b + 2⟩ (cutBits p π₁)] I =
        some (I.setBool ⟨b + 3⟩ ((cutRel x (cutOf p π₁)).map Prod.fst).flatten) ∧
      (cutFields p f π₁).mapM (fun g => I.fields g.id) = some ((cutRel x (cutOf p π₁)).map Prod.snd) := by
  have hidx : (cutBits p π₁).all (· < v.length) = true := by
    simp only [List.all_eq_true, decide_eq_true_eq, cutBits, List.mem_flatMap]
    rintro i ⟨o, ho, c, hc, hi⟩
    exact h.word_idx o c (owners_lt ho) (hπ c hc) i hi
  constructor
  · rw [← cutBits_map h π₁]
    simp [runLocal, localStep, idealStep, blankWire, InstrP.map, h.hv, hidx]
  · rw [mapM_lookups _ _ (fun g hg => ?_)]
    · congr 1
      simp only [cutFields, cutRel, List.map_flatMap, List.map_map, Function.comp_def]
      apply flatMap_congr'
      intro o ho
      apply List.map_congr_left
      intro c hc
      rw [h.hfld o (owners_lt ho) c (hπ c hc)]
      rfl
    · simp only [cutFields, List.mem_flatMap, List.mem_map] at hg
      obtain ⟨o, ho, c, hc, rfl⟩ := hg
      rw [h.hfld o (owners_lt ho) c (hπ c hc)]
      rfl

end CutBlock

/-! ## The bucket block -/

section BucketBlock

variable (E : Env) {p : Params} {b f : Nat} {I : Ideal} {v : Bits} {x : Vals}

theorem bucketBits_map (h : Holds p b f I v x) (π₁ π₂ : List Nat) :
    (bucketBits p π₁ π₂).map (v.getD · false) =
      ((pairs p).map fun e => x.bits e.1 (member p π₁ π₂ e.2.1 0) ++ x.bits e.1 (member p π₁ π₂ e.2.1 e.2.2)).flatten := by
  simp only [bucketBits, List.map_flatMap, List.map_append, flatten_map', h.hbits]

/-- **The bucket block**: `b + 5` holds the `modAdd` words and the sum handles the field sums of
every (reference, member) pair: exactly `bucketRel x`; the candidates are untouched. -/
theorem Holds.bucket (hW : WordLoaded E) (h : Holds p b f I v x) (π₁ π₂ : List Nat)
    (hπ₁ : ∀ c ∈ π₁, c < p.M) (hM : 0 < p.M) :
    ∃ I3, runLocal E (bucketBlock p b f π₁ π₂) I = some I3 ∧
      I3.bools (b + 5) = some ((bucketRel x (member p π₁ π₂) (pairs p)).map Prod.fst).flatten ∧
      (sums p f).mapM (fun g => I3.fields g.id) = some ((bucketRel x (member p π₁ π₂) (pairs p)).map Prod.snd) ∧
      I3.bools (b + 2) = I.bools (b + 2) ∧ (∀ j, j < f + 2 * p.M → I3.fields j = I.fields j) := by
  have hml := member_lt p π₁ π₂ hπ₁ hM
  have hwide := h.wide
  have hidx : (bucketBits p π₁ π₂).all (· < v.length) = true := by
    simp only [List.all_eq_true, decide_eq_true_eq, bucketBits, List.mem_flatMap, List.mem_append]
    rintro i ⟨e, he, hi | hi⟩
    · exact h.word_idx _ _ (mem_pairs p e he) (hml _ _) i hi
    · exact h.word_idx _ _ (mem_pairs p e he) (hml _ _) i hi
  have hL : ∀ y ∈ (pairs p).map (fun e => x.bits e.1 (member p π₁ π₂ e.2.1 0) ++
      x.bits e.1 (member p π₁ π₂ e.2.1 e.2.2)), y.length = 510 := by
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨e, -, rfl⟩ := hy
    rw [List.length_append, hwide, hwide]
    rfl
  have hpl : ((bucketBits p π₁ π₂).map (v.getD · false)).length = p.D * 510 := by
    rw [bucketBits_map h π₁ π₂, length_flatten_eq 510 _ hL, List.length_map, length_pairs]
  rw [bucketBlock, sumAdds_eq, runLocal_append]
  have hrun : runLocal E [(.pick ⟨b + 4⟩ ⟨b + 2⟩ (bucketBits p π₁ π₂) : Instr), .run ⟨b + 5⟩ modaddOpenName p.D ⟨b + 4⟩] I =
      some ((I.setBool ⟨b + 4⟩ ((bucketBits p π₁ π₂).map (v.getD · false))).setBool ⟨b + 5⟩
        (runCopies modaddOpenC p.D ((bucketBits p π₁ π₂).map (v.getD · false)))) := by
    have hpl' : (bucketBits p π₁ π₂).length = p.D * 510 := by simpa using hpl
    simp [runLocal, localStep, idealStep, blankWire, InstrP.map, h.hv, hidx, hW.modaddOpen, Ideal.setBool,
      hpl', modaddOpenC]
  rw [hrun]
  simp only [Option.bind_some]
  generalize hI2 : (I.setBool ⟨b + 4⟩ ((bucketBits p π₁ π₂).map (v.getD · false))).setBool ⟨b + 5⟩
        (runCopies modaddOpenC p.D ((bucketBits p π₁ π₂).map (v.getD · false))) = I2
  have hfI2 : I2.fields = I.fields := by rw [← hI2]; rfl
  have hn : ((sumTriples p f π₁ π₂).map (·.1.id)).Nodup := by
    simp only [sumTriples, List.map_map, Function.comp_def, sumH]
    have : ((pairs p).zipIdx.map fun e => f + 2 * p.M + e.2) = (List.range' (f + 2 * p.M) (pairs p).length) := by
      rw [List.zipIdx_eq_zip_range']
      apply List.ext_getElem <;> simp
    rw [this]
    exact List.nodup_range'
  have hd : ∀ t ∈ sumTriples p f π₁ π₂, ∀ t' ∈ sumTriples p f π₁ π₂, t.1.id ≠ t'.2.1.id ∧ t.1.id ≠ t'.2.2.id := by
    intro t ht t' ht'
    simp only [sumTriples, List.mem_map] at ht ht'
    obtain ⟨e, -, rfl⟩ := ht
    obtain ⟨e', he', rfl⟩ := ht'
    have ho := mem_pairs p e'.1 (mem_zipIdx_fst he')
    have h1 := fOf_lt p f _ _ ho (hml e'.1.2.1 0)
    have h2 := fOf_lt p f _ _ ho (hml e'.1.2.1 e'.1.2.2)
    simp only [sumH]
    omega
  have hs : ∀ t ∈ sumTriples p f π₁ π₂, (I2.fields t.2.1.id).isSome ∧ (I2.fields t.2.2.id).isSome := by
    intro t ht
    simp only [sumTriples, List.mem_map] at ht
    obtain ⟨e, he, rfl⟩ := ht
    have ho := mem_pairs p e.1 (mem_zipIdx_fst he)
    rw [hfI2, h.hfld _ ho _ (hml _ _), h.hfld _ ho _ (hml _ _)]
    exact ⟨rfl, rfl⟩
  obtain ⟨I3, g1, g2, g3, g4⟩ := runLocal_adds E (sumTriples p f π₁ π₂) I2 hn hd hs
  refine ⟨I3, g1, ?_, ?_, ?_, ?_⟩
  · rw [g2, ← hI2]
    simp only [Ideal.setBool, if_true]
    rw [bucketBits_map h π₁ π₂]
    have e1 := runCopies_flatten modaddOpenC _ hL
    rw [List.length_map, length_pairs] at e1
    rw [e1]
    simp only [bucketRel, List.map_map, Function.comp_def, modaddOpenC]
    congr 2
    apply List.map_congr_left
    intro e _
    rw [modaddEval_pair _ _ (hwide _ _) (hwide _ _)]
    rfl
  · have hval : ∀ e ∈ (pairs p).zipIdx, I3.fields (sumH p f e.2).id =
        some (x.elem e.1.1 (member p π₁ π₂ e.1.2.1 0) + x.elem e.1.1 (member p π₁ π₂ e.1.2.1 e.1.2.2)) := by
      intro e he
      have := g3 (sumH p f e.2, fOf p f e.1.1 (member p π₁ π₂ e.1.2.1 0),
        fOf p f e.1.1 (member p π₁ π₂ e.1.2.1 e.1.2.2)) (by simp only [sumTriples, List.mem_map]; exact ⟨e, he, rfl⟩)
      have ho := mem_pairs p e.1 (mem_zipIdx_fst he)
      rw [this, hfI2, h.hfld _ ho _ (hml _ _), h.hfld _ ho _ (hml _ _)]
      rfl
    have hm : (sums p f).mapM (fun g => I3.fields g.id) =
        some (((pairs p).zipIdx).map fun e =>
          x.elem e.1.1 (member p π₁ π₂ e.1.2.1 0) + x.elem e.1.1 (member p π₁ π₂ e.1.2.1 e.1.2.2)) := by
      unfold sums
      rw [List.mapM_map]
      exact mapM_vals _ _ _ hval
    rw [hm]
    congr 1
    have : ((pairs p).zipIdx).map (fun e =>
        x.elem e.1.1 (member p π₁ π₂ e.1.2.1 0) + x.elem e.1.1 (member p π₁ π₂ e.1.2.1 e.1.2.2)) =
        (((pairs p).zipIdx).map Prod.fst).map (fun e =>
          x.elem e.1 (member p π₁ π₂ e.2.1 0) + x.elem e.1 (member p π₁ π₂ e.2.1 e.2.2)) := by
      rw [List.map_map]
      rfl
    rw [this, zipIdx_map_fst]
    simp only [bucketRel, List.map_map, Function.comp_def]
  · rw [g2, ← hI2]
    simp [Ideal.setBool]
  · intro j hj
    rw [g4 j (fun t ht => ?_), hfI2]
    simp only [sumTriples, List.mem_map] at ht
    obtain ⟨e, -, rfl⟩ := ht
    simp only [sumH]
    omega

end BucketBlock

/-! ## Local steps, by lookup -/

theorem localStep_pick (E : Env) (out h : BoolH) (idx : List Nat) (I : Ideal) (v : Bits)
    (hv : I.bools h.id = some v) (hidx : idx.all (· < v.length) = true) :
    localStep E (.pick out h idx) I = some (I.setBool out (idx.map (v.getD · false))) := by
  simp [localStep, idealStep, blankWire, InstrP.map, hv, hidx]

theorem localStep_run (E : Env) (out inp : BoolH) (name : Bytes) (copies : Nat) (c : Circuit) (I : Ideal) (v : Bits)
    (hc : E.circuits name = some c) (hv : I.bools inp.id = some v) (hl : v.length = copies * c.inWidth) :
    localStep E (.run out name copies inp) I = some (I.setBool out (runCopies c copies v)) := by
  simp [localStep, idealStep, blankWire, InstrP.map, hc, hv, hl]

theorem localStep_slice (E : Env) (out h : BoolH) (lo hi : Nat) (I : Ideal) (v : Bits)
    (hv : I.bools h.id = some v) (hb : lo ≤ hi ∧ hi ≤ v.length) :
    localStep E (.slice out h lo hi) I = some (I.setBool out ((v.drop lo).take (hi - lo))) := by
  simp [localStep, idealStep, blankWire, InstrP.map, hv, hb]

theorem localStep_free (E : Env) (h : BoolH) (I : Ideal) : localStep E (.freeBool h) I = some (I.dropBool h) := by
  simp [localStep, idealStep, blankWire, InstrP.map]

theorem localStep_concat (E : Env) (out : BoolH) (parts : List BoolH) (I : Ideal) (vs : List Bits)
    (hm : parts.mapM (fun g => I.bools g.id) = some vs) :
    localStep E (.concat out parts) I = some (I.setBool out vs.flatten) := by
  simp [localStep, idealStep, blankWire, InstrP.map, hm]

/-- Frees never fail in the model; they touch no field and no other Boolean handle. -/
theorem runLocal_frees (E : Env) : ∀ (hs : List BoolH) (I : Ideal),
    ∃ I', runLocal E (frees hs) I = some I' ∧ I'.fields = I.fields ∧
      ∀ j, (∀ h ∈ hs, h.id ≠ j) → I'.bools j = I.bools j
  | [], I => ⟨I, rfl, rfl, fun _ _ => rfl⟩
  | h :: hs, I => by
    obtain ⟨I', h1, h2, h3⟩ := runLocal_frees E hs (I.dropBool h)
    refine ⟨I', ?_, h2, fun j hj => ?_⟩
    · show runLocal E (.freeBool h :: frees hs) I = some I'
      simp only [runLocal, localStep_free]
      exact h1
    · rw [h3 j (fun g hg => hj g (by simp [hg]))]
      simp only [Ideal.dropBool]
      rw [if_neg (Ne.symm (hj h (by simp)))]

/-- **A block of slices of one bundle** into distinct fresh handles: each holds its slice; nothing
else changes. -/
theorem runLocal_slices (E : Env) (src : BoolH) (bundle : Bits) : ∀ (ts : List (Nat × Nat × Nat)) (I : Ideal),
    I.bools src.id = some bundle → (∀ t ∈ ts, t.1 ≠ src.id ∧ t.2.1 ≤ t.2.2 ∧ t.2.2 ≤ bundle.length) →
    (ts.map (·.1)).Nodup →
    ∃ I', runLocal E (ts.map fun t => (.slice ⟨t.1⟩ src t.2.1 t.2.2 : Instr)) I = some I' ∧ I'.fields = I.fields ∧
      (∀ j, (∀ t ∈ ts, t.1 ≠ j) → I'.bools j = I.bools j) ∧
      (∀ t ∈ ts, I'.bools t.1 = some ((bundle.drop t.2.1).take (t.2.2 - t.2.1)))
  | [], I, _, _, _ => ⟨I, rfl, rfl, fun _ _ => rfl, by simp⟩
  | t :: ts, I, hb, ht, hn => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    have h0 := ht t (by simp)
    have hb' : (I.setBool ⟨t.1⟩ ((bundle.drop t.2.1).take (t.2.2 - t.2.1))).bools src.id = some bundle := by
      simp only [Ideal.setBool]
      rw [if_neg (Ne.symm h0.1)]
      exact hb
    obtain ⟨I', h1, h2, h3, h4⟩ := runLocal_slices E src bundle ts _ hb' (fun u hu => ht u (by simp [hu])) hn.2
    refine ⟨I', ?_, h2, fun j hj => ?_, fun u hu => ?_⟩
    · simp only [List.map_cons, runLocal, localStep_slice E ⟨t.1⟩ src t.2.1 t.2.2 I bundle hb ⟨h0.2.1, h0.2.2⟩]
      exact h1
    · rw [h3 j (fun u hu => hj u (by simp [hu]))]
      simp only [Ideal.setBool]
      rw [if_neg (Ne.symm (hj t (by simp)))]
    · simp only [List.mem_cons] at hu
      rcases hu with hu | hu
      · subst hu
        rw [h3 _ (fun u' hu' e => hn.1 ⟨u', hu', e⟩)]
        simp [Ideal.setBool]
      · exact h4 u hu

/-! ## More lists: lookups in bulk, ranges -/

theorem mapM_append_vals {α β : Type} (look : α → Option β) : ∀ (l₁ l₂ : List α) (v₁ v₂ : List β),
    l₁.mapM look = some v₁ → l₂.mapM look = some v₂ → (l₁ ++ l₂).mapM look = some (v₁ ++ v₂)
  | [], l₂, v₁, v₂, h1, h2 => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h1
    subst h1
    exact h2
  | a :: l₁, l₂, v₁, v₂, h1, h2 => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h1
    obtain ⟨c, hc, cs, hcs, rfl⟩ := h1
    have ih := mapM_append_vals look l₁ l₂ cs v₂ hcs h2
    simp [List.mapM_cons, hc, ih]

theorem mapM_flatMap_vals {α β γ : Type} (look : β → Option γ) (g : α → List β) (val : α → List γ) :
    ∀ (l : List α), (∀ a ∈ l, (g a).mapM look = some (val a)) → (l.flatMap g).mapM look = some (l.flatMap val)
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact mapM_append_vals look _ _ _ _ (h a (by simp))
      (mapM_flatMap_vals look g val l (fun y hy => h y (by simp [hy])))

theorem mapM_map_vals {α β γ : Type} (look : β → Option γ) (g : α → β) (val : α → γ) (l : List α)
    (h : ∀ a ∈ l, look (g a) = some (val a)) : (l.map g).mapM look = some (l.map val) := by
  rw [List.mapM_map]
  exact mapM_vals _ _ l h

theorem mapM_congr' {α β : Type} (f g : α → Option β) : ∀ (l : List α), (∀ a ∈ l, f a = g a) → l.mapM f = l.mapM g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.mapM_cons]
    rw [h a (by simp), mapM_congr' f g l (fun y hy => h y (by simp [hy]))]

theorem map_getD_all {α : Type} (l : List α) (d : α) : (List.range l.length).map (fun i => l.getD i d) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, h2]

theorem map_range_getD {α β : Type} (L : List α) (d : α) (G : α → β) :
    (List.range L.length).map (fun j => G (L.getD j d)) = L.map G := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map] at h2
    simp [List.getD_eq_getElem?_getD, h2]

theorem flatten_map_singleton' {α β : Type} (g : α → β) (l : List α) : (l.map fun a => [g a]).flatten = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem range_split (a n : Nat) : List.range (a + n) = List.range a ++ List.range' a n := by
  rw [List.range_add, map_range_add]

theorem flatMap_range_mul {α : Type} (g : Nat → α) (w : Nat) : ∀ n,
    (List.range n).flatMap (fun j => (List.range w).map fun i => g (j * w + i)) = (List.range (n * w)).map g
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_range_mul g w n, Nat.succ_mul, List.range_add,
      List.map_append, List.map_map]
    simp [Function.comp_def]

theorem owners_flatMap {α : Type} (g : Nat → List α) : owners.flatMap g = g 0 ++ g 1 := by
  simp [owners]

/-- Two blocks of `n`, one per owner, as one block of `2n`. -/
theorem owners_range {α : Type} (g : Nat → Nat → α) (n : Nat) :
    owners.flatMap (fun o => (List.range n).map (g o)) =
      (List.range (2 * n)).map (fun q => if q < n then g 0 q else g 1 (q - n)) := by
  rw [owners_flatMap, Nat.two_mul, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro j hj
    simp [List.mem_range.mp hj]
  · apply List.map_congr_left
    intro j _
    have e : (if n + j < n then g 0 (n + j) else g 1 (n + j - n)) = g 1 j := by
      rw [if_neg (by omega), Nat.add_sub_cancel_left]
    exact e.symm

/-- A consecutive block of field handles, all set: their lookups are the values. -/
theorem mapM_block (J : Ideal) (g : Nat → FieldH) (base n : Nat) (vs : List F)
    (hg : ∀ i, i < n → (g i).id = base + i) (hl : vs.length = n)
    (hJ : ∀ i, i < n → J.fields (base + i) = some (vs.getD i 0)) :
    ((List.range n).map g).mapM (fun h => J.fields h.id) = some vs := by
  rw [mapM_map_vals _ g (fun i => vs.getD i 0) _ (fun i hi => by
    rw [hg i (List.mem_range.mp hi)]; exact hJ i (List.mem_range.mp hi))]
  subst hl
  rw [map_getD_all]

/-! ## Programs without masks on instances given as chunks -/

open TlsMpc.FieldDag.V3 (Program OMark) in
theorem instanceAt_flatten (n : Nat) (chunks : List (List F)) (hl : ∀ c ∈ chunks, c.length = n) (q : Nat)
    (hq : q < chunks.length) : instanceAt chunks.flatten n q = fun i => (chunks.getD q []).getD i 0 := by
  funext i
  unfold instanceAt
  split
  · next hi => exact flatten_getD n chunks q i 0 hl hq hi
  · next hi =>
    have hmem : chunks.getD q [] ∈ chunks := by simp [List.getD_eq_getElem?_getD, hq]
    have hc := hl _ hmem
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

open TlsMpc.FieldDag.V3 (Program OMark) in
/-- **A mask-free program on `chunks.length` instances**: instance `q` reads chunk `q`; the outputs
are the concatenation of `g` on each chunk, and nothing is opened. -/
theorem runProgram_chunks (pr : Program) (n : Nat) (marks : List OMark) (g : (Nat → F) → List F)
    (hc : Computes pr n marks g) (chunks : List (List F)) (hl : ∀ c ∈ chunks, c.length = n) :
    runProgram pr chunks.length chunks.flatten [] =
      some ((chunks.map fun c => g (fun i => c.getD i 0)).flatten, []) := by
  obtain ⟨h1, h2, -, h4⟩ := hc
  subst h1
  have hm : (List.range chunks.length).mapM (fun j =>
      TlsMpc.FieldDag.V3.eval pr (instanceAt chunks.flatten pr.inputs j) (instanceAt [] pr.masks j)) =
      some ((List.range chunks.length).map fun j => (g (fun i => (chunks.getD j []).getD i 0), ([] : List F))) := by
    apply mapM_vals
    intro j hj
    rw [h4, instanceAt_flatten pr.inputs chunks hl j (List.mem_range.mp hj)]
  unfold runProgram
  rw [if_pos ⟨length_flatten_eq pr.inputs chunks hl, by rw [h2]; simp⟩, hm]
  simp only [Option.map_some, List.map_map, Function.comp_def]
  rw [flatten_map_nil, map_range_getD chunks [] (fun c => g fun i => c.getD i 0)]

/-! ## The finalize block -/

/-- The two owners' words of candidate `c`, A's then B's: the input of a finalize circuit. -/
def pairOf (x : Vals) (c : Nat) : Bits := x.bits 0 c ++ x.bits 1 c

/-- Kept reference `j`: member 0 of bucket `j`. -/
def refOf (p : Params) (π₁ π₂ : List Nat) (j : Nat) : Nat := member p π₁ π₂ j 0

/-- The finalize circuit's 256 output bits for kept reference `j`: `finalize-bits` for the first
`bits` references, `finalize-mask` for the others. -/
def outOf (p : Params) (π₁ π₂ : List Nat) (x : Vals) (j : Nat) : Bits :=
  if j < p.bits then finalizeBitsEval (pairOf x (refOf p π₁ π₂ j)) else finalizeMaskEval (pairOf x (refOf p π₁ π₂ j))

def outsOf (p : Params) (π₁ π₂ : List Nat) (x : Vals) : List Bits := (List.range p.N).map (outOf p π₁ π₂ x)

/-- **The reference flags** the flag phase opens: per kept reference, the last bit of its output. -/
def flagsOf (p : Params) (π₁ π₂ : List Nat) (x : Vals) : Bits :=
  (List.range p.N).map fun j => (outOf p π₁ π₂ x j).getD 255 false

theorem pairOf_length {x : Vals} (hw : x.Wide) (c : Nat) : (pairOf x c).length = 510 := by
  rw [pairOf, List.length_append, hw, hw]
  rfl

theorem outOf_length {x : Vals} (hw : x.Wide) (p : Params) (π₁ π₂ : List Nat) (j : Nat) :
    (outOf p π₁ π₂ x j).length = 256 := by
  have := pairOf_length hw (refOf p π₁ π₂ j)
  unfold outOf
  split
  · simp [finalizeBitsEval, this]
  · simp [finalizeMaskEval, modaddEval]

theorem outsOf_length_each {x : Vals} (hw : x.Wide) (p : Params) (π₁ π₂ : List Nat) :
    ∀ y ∈ outsOf p π₁ π₂ x, y.length = 256 := by
  intro y hy
  simp only [outsOf, List.mem_map] at hy
  obtain ⟨j, -, rfl⟩ := hy
  exact outOf_length hw p π₁ π₂ j

def refs6 (p : Params) (π₁ π₂ : List Nat) (x : Vals) : List Bits :=
  (List.range p.bits).map fun j => pairOf x (refOf p π₁ π₂ j)
def refs7 (p : Params) (π₁ π₂ : List Nat) (x : Vals) : List Bits :=
  (List.range' p.bits p.words).map fun j => pairOf x (refOf p π₁ π₂ j)

theorem outsOf_split (p : Params) (π₁ π₂ : List Nat) (x : Vals) (hbits : p.bits ≤ p.N) :
    outsOf p π₁ π₂ x = (refs6 p π₁ π₂ x).map finalizeBitsEval ++ (refs7 p π₁ π₂ x).map finalizeMaskEval := by
  have hN : p.N = p.bits + p.words := by unfold Params.words; omega
  unfold outsOf
  rw [hN, range_split, List.map_append]
  simp only [refs6, refs7, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro j hj
    simp [outOf, List.mem_range.mp hj]
  · apply List.map_congr_left
    intro j hj
    have := (List.mem_range'_1.mp hj).1
    simp [outOf, Nat.not_lt.mpr this]

theorem runLocal_optRun (E : Env) (c : Circuit) (name : Bytes) (hc : E.circuits name = some c) (out inp : BoolH)
    (n : Nat) (L : List Bits) (hn : L.length = n) (hL : ∀ y ∈ L, y.length = c.inWidth) (I : Ideal)
    (hv : I.bools inp.id = some L.flatten) :
    ∃ I', runLocal E (if n = 0 then [] else [.run out name n inp]) I = some I' ∧ I'.fields = I.fields ∧
      (∀ j, j ≠ out.id → I'.bools j = I.bools j) ∧
      (if n = 0 then [] else [out]).mapM (fun g => I'.bools g.id) =
        some (if n = 0 then [] else [(L.map c.eval).flatten]) := by
  by_cases h0 : n = 0
  · exact ⟨I, by simp [h0, runLocal], rfl, fun _ _ => rfl, by simp [h0]⟩
  · have e := runCopies_flatten c L hL
    rw [hn] at e
    have r := localStep_run E out inp name n c I L.flatten hc hv (by rw [length_flatten_eq c.inWidth L hL, hn])
    rw [e] at r
    refine ⟨I.setBool out (L.map c.eval).flatten, ?_, rfl, fun j hj => ?_, ?_⟩
    · simp only [if_neg h0, runLocal, r]
    · simp only [Ideal.setBool]
      rw [if_neg hj]
    · simp [h0, Ideal.setBool]

theorem opt_flatten (n : Nat) (L : List Bits) (g : Bits → Bits) (hn : L.length = n) :
    (if n = 0 then [] else [(L.map g).flatten] : List Bits).flatten = (L.map g).flatten := by
  by_cases h0 : n = 0
  · subst hn
    have : L = [] := List.length_eq_zero_iff.mp h0
    subst this
    simp
  · simp [h0]

theorem final_tail (E : Env) (J : Ideal) (b : Nat) (parts : List BoolH) (vs : List Bits) (outs : List Bits)
    (hm : parts.mapM (fun g => J.bools g.id) = some vs) (hfl : vs.flatten = outs.flatten)
    (hl : ∀ y ∈ outs, y.length = 256) :
    runLocal E [.concat ⟨b + 10⟩ parts, .pick ⟨b + 11⟩ ⟨b + 10⟩ ((List.range outs.length).map fun j => 256 * j + 255)] J =
      some ((J.setBool ⟨b + 10⟩ outs.flatten).setBool ⟨b + 11⟩
        ((List.range outs.length).map fun j => (outs.getD j []).getD 255 false)) := by
  have c1 : localStep E (.concat ⟨b + 10⟩ parts) J = some (J.setBool ⟨b + 10⟩ outs.flatten) := by
    rw [← hfl]
    exact localStep_concat E _ _ J vs hm
  have hlen := length_flatten_eq 256 outs hl
  have hidx : ((List.range outs.length).map fun j => 256 * j + 255).all (· < outs.flatten.length) = true := by
    simp only [List.all_eq_true, decide_eq_true_eq, List.mem_map, List.mem_range]
    rintro i ⟨j, hj, rfl⟩
    rw [hlen]
    omega
  have c2 := localStep_pick E ⟨b + 11⟩ ⟨b + 10⟩ _ (J.setBool ⟨b + 10⟩ outs.flatten) outs.flatten
    (by simp [Ideal.setBool]) hidx
  have hv : ((List.range outs.length).map fun j => 256 * j + 255).map (outs.flatten.getD · false) =
      (List.range outs.length).map fun j => (outs.getD j []).getD 255 false := by
    rw [List.map_map]
    apply List.map_congr_left
    intro j hj
    have := flatten_getD 256 outs j 255 false hl (List.mem_range.mp hj) (by omega)
    simp only [Function.comp_apply]
    rw [Nat.mul_comm 256 j]
    exact this
  rw [hv] at c2
  simp only [runLocal, c1, c2]

section FinalBlock

variable (E : Env) {p : Params} {b f : Nat} {I : Ideal} {v : Bits} {x : Vals}

theorem refPair_map (h : Holds p b f I v x) (π₁ π₂ : List Nat) (j : Nat) :
    (refPair p π₁ π₂ j).map (v.getD · false) = pairOf x (refOf p π₁ π₂ j) := by
  simp only [refPair, List.map_append, pairOf, refOf, h.hbits]

theorem refPairs_idx (h : Holds p b f I v x) (π₁ π₂ : List Nat) (hπ₁ : ∀ c ∈ π₁, c < p.M) (hM : 0 < p.M)
    (js : List Nat) : (js.flatMap (refPair p π₁ π₂)).all (· < v.length) = true := by
  have hml := member_lt p π₁ π₂ hπ₁ hM
  simp only [List.all_eq_true, decide_eq_true_eq, List.mem_flatMap, refPair, List.mem_append]
  rintro i ⟨j, -, hi | hi⟩
  · exact h.word_idx 0 _ (by omega) (hml j 0) i hi
  · exact h.word_idx 1 _ (by omega) (hml j 0) i hi

theorem refPairs_map (h : Holds p b f I v x) (π₁ π₂ : List Nat) (js : List Nat) :
    (js.flatMap (refPair p π₁ π₂)).map (v.getD · false) = (js.map fun j => pairOf x (refOf p π₁ π₂ j)).flatten := by
  simp only [List.map_flatMap, flatten_map', refPair_map h]

/-- **The finalize block**: the bundle `b + 10` is the kept references' finalize outputs (256 bits
each), the handle `b + 11` their flags; no field handle changes. -/
theorem Holds.final (hW : WordLoaded E) (h : Holds p b f I v x) (π₁ π₂ : List Nat)
    (hπ₁ : ∀ c ∈ π₁, c < p.M) (hM : 0 < p.M) (hbits : p.bits ≤ p.N) :
    ∃ I4, runLocal E (finalBlock p b π₁ π₂) I = some I4 ∧ I4.fields = I.fields ∧
      I4.bools (b + 10) = some (outsOf p π₁ π₂ x).flatten ∧ I4.bools (b + 11) = some (flagsOf p π₁ π₂ x) := by
  have hwide := h.wide
  have s1 := localStep_pick E ⟨b + 6⟩ ⟨b + 2⟩ _ I v h.hv (refPairs_idx h π₁ π₂ hπ₁ hM (List.range p.bits))
  rw [refPairs_map h π₁ π₂] at s1
  change _ = some (I.setBool ⟨b + 6⟩ (refs6 p π₁ π₂ x).flatten) at s1
  have s2 := localStep_pick E ⟨b + 7⟩ ⟨b + 2⟩ _ (I.setBool ⟨b + 6⟩ (refs6 p π₁ π₂ x).flatten) v
    (by simp [Ideal.setBool, h.hv]) (refPairs_idx h π₁ π₂ hπ₁ hM (List.range' p.bits p.words))
  rw [refPairs_map h π₁ π₂] at s2
  change _ = some ((I.setBool ⟨b + 6⟩ (refs6 p π₁ π₂ x).flatten).setBool ⟨b + 7⟩ (refs7 p π₁ π₂ x).flatten) at s2
  have hpre : runLocal E [(.pick ⟨b + 6⟩ ⟨b + 2⟩ ((List.range p.bits).flatMap (refPair p π₁ π₂)) : Instr),
      .pick ⟨b + 7⟩ ⟨b + 2⟩ ((List.range' p.bits p.words).flatMap (refPair p π₁ π₂))] I =
      some ((I.setBool ⟨b + 6⟩ (refs6 p π₁ π₂ x).flatten).setBool ⟨b + 7⟩ (refs7 p π₁ π₂ x).flatten) := by
    simp only [runLocal, s1, s2]
  have hL6 : ∀ y ∈ refs6 p π₁ π₂ x, y.length = finalizeBitsC.inWidth := by
    intro y hy
    simp only [refs6, List.mem_map] at hy
    obtain ⟨j, -, rfl⟩ := hy
    exact pairOf_length hwide _
  have hL7 : ∀ y ∈ refs7 p π₁ π₂ x, y.length = finalizeMaskC.inWidth := by
    intro y hy
    simp only [refs7, List.mem_map] at hy
    obtain ⟨j, -, rfl⟩ := hy
    exact pairOf_length hwide _
  obtain ⟨I3, a1, a2, a3, a4⟩ := runLocal_optRun E finalizeBitsC finalizeBitsName hW.finalizeBits ⟨b + 8⟩ ⟨b + 6⟩
    p.bits (refs6 p π₁ π₂ x) (by simp [refs6]) hL6
    ((I.setBool ⟨b + 6⟩ (refs6 p π₁ π₂ x).flatten).setBool ⟨b + 7⟩ (refs7 p π₁ π₂ x).flatten)
    (by simp [Ideal.setBool])
  obtain ⟨I4, c1, c2, c3, c4⟩ := runLocal_optRun E finalizeMaskC finalizeMaskName hW.finalizeMask ⟨b + 9⟩ ⟨b + 7⟩
    p.words (refs7 p π₁ π₂ x) (by simp [refs7]) hL7 I3
    (by rw [a3 (b + 7) (by simp)]; simp [Ideal.setBool])
  have hparts : ((if p.bits = 0 then [] else [(⟨b + 8⟩ : BoolH)]) ++ (if p.words = 0 then [] else [(⟨b + 9⟩ : BoolH)])).mapM
      (fun g => I4.bools g.id) =
      some ((if p.bits = 0 then [] else [((refs6 p π₁ π₂ x).map finalizeBitsC.eval).flatten]) ++
        (if p.words = 0 then [] else [((refs7 p π₁ π₂ x).map finalizeMaskC.eval).flatten])) := by
    refine mapM_append_vals _ _ _ _ _ ?_ c4
    rw [← a4]
    apply mapM_congr'
    intro g hg
    have := mem_ite_nil hg
    simp only [List.mem_singleton] at this
    subst this
    exact c3 (b + 8) (by simp)
  have hfl : ((if p.bits = 0 then [] else [((refs6 p π₁ π₂ x).map finalizeBitsC.eval).flatten]) ++
        (if p.words = 0 then [] else [((refs7 p π₁ π₂ x).map finalizeMaskC.eval).flatten]) : List Bits).flatten =
      (outsOf p π₁ π₂ x).flatten := by
    rw [List.flatten_append, opt_flatten p.bits _ _ (by simp [refs6]), opt_flatten p.words _ _ (by simp [refs7]),
      outsOf_split p π₁ π₂ x hbits, List.flatten_append]
    rfl
  have htail := final_tail E I4 b _ _ (outsOf p π₁ π₂ x) hparts hfl (outsOf_length_each hwide p π₁ π₂)
  have hN : (outsOf p π₁ π₂ x).length = p.N := by simp [outsOf]
  rw [hN] at htail
  refine ⟨(I4.setBool ⟨b + 10⟩ (outsOf p π₁ π₂ x).flatten).setBool ⟨b + 11⟩
    ((List.range p.N).map fun j => ((outsOf p π₁ π₂ x).getD j []).getD 255 false), ?_, ?_, ?_, ?_⟩
  · rw [finalBlock, runLocal_append, runLocal_append, runLocal_append, hpre]
    simp only [Option.bind_some]
    rw [a1]
    simp only [Option.bind_some]
    rw [c1]
    simp only [Option.bind_some]
    exact htail
  · show I4.fields = I.fields
    rw [c2, a2]
    rfl
  · simp [Ideal.setBool]
  · simp only [Ideal.setBool, if_true]
    congr 1
    unfold flagsOf
    apply List.map_congr_left
    intro j hj
    rw [show (outsOf p π₁ π₂ x).getD j [] = outOf p π₁ π₂ x j from
      getD_map_range _ _ _ _ (List.mem_range.mp hj)]

end FinalBlock

/-! ## The word masks -/

/-- **The mask block**: the word masks' Boolean handles hold the first 255 bits of their finalize
outputs, their field handles the sums of the two references' elements; the bundle `b + 10` and the
candidate field handles stay. -/
theorem masks_block (E : Env) (p : Params) (b f : Nat) (π₁ π₂ : List Nat) (I4 : Ideal) (x : Vals) (bundle : Bits)
    (hb10 : I4.bools (b + 10) = some bundle) (hlen : bundle.length = p.N * 256) (hbits : p.bits ≤ p.N)
    (hfld : ∀ o, o < 2 → ∀ c, c < p.M → I4.fields (fOf p f o c).id = some (x.elem o c))
    (hπ₁ : ∀ c ∈ π₁, c < p.M) (hM : 0 < p.M) :
    ∃ I5, runLocal E (maskBlock p b f π₁ π₂) I4 = some I5 ∧ I5.bools (b + 10) = some bundle ∧
      (∀ j, j < p.words → I5.bools (b + 12 + j) = some ((bundle.drop (256 * (p.bits + j))).take 255)) ∧
      (∀ j, j < p.words → I5.fields (maskBase p f + j) =
        some (x.elem 0 (refOf p π₁ π₂ (p.bits + j)) + x.elem 1 (refOf p π₁ π₂ (p.bits + j)))) ∧
      (∀ j, j < maskBase p f → I5.fields j = I4.fields j) ∧
      (∀ j, maskBase p f + p.words ≤ j → I5.fields j = I4.fields j) ∧
      (∀ j, b + 12 + p.words ≤ j → I5.bools j = I4.bools j) := by
  have hml := member_lt p π₁ π₂ hπ₁ hM
  have hwords : p.words = p.N - p.bits := rfl
  -- the slices
  have hsl : (List.range p.words).map (fun j =>
      (.slice ⟨b + 12 + j⟩ ⟨b + 10⟩ (256 * (p.bits + j)) (256 * (p.bits + j) + W) : Instr)) =
      ((List.range p.words).map fun j => (b + 12 + j, 256 * (p.bits + j), 256 * (p.bits + j) + W)).map
        fun t => (.slice ⟨t.1⟩ ⟨b + 10⟩ t.2.1 t.2.2 : Instr) := by
    rw [List.map_map]
    rfl
  obtain ⟨Ia, a1, a2, a3, a4⟩ := runLocal_slices E ⟨b + 10⟩ bundle
    ((List.range p.words).map fun j => (b + 12 + j, 256 * (p.bits + j), 256 * (p.bits + j) + W)) I4 hb10
    (by
      intro t ht
      simp only [List.mem_map, List.mem_range] at ht
      obtain ⟨j, hj, rfl⟩ := ht
      refine ⟨by show b + 12 + j ≠ b + 10; omega, by show 256 * (p.bits + j) ≤ 256 * (p.bits + j) + W; omega, ?_⟩
      show 256 * (p.bits + j) + W ≤ bundle.length
      rw [hlen]
      show 256 * (p.bits + j) + 255 ≤ p.N * 256
      omega)
    (by
      rw [List.map_map]
      show ((List.range p.words).map fun j => b + 12 + j).Nodup
      rw [map_range_add]
      exact List.nodup_range')
  -- the sums
  have had : (List.range p.words).map (fun j =>
      (.fieldAdd ⟨maskBase p f + j⟩ (fOf p f 0 (member p π₁ π₂ (p.bits + j) 0))
        (fOf p f 1 (member p π₁ π₂ (p.bits + j) 0)) : Instr)) =
      ((List.range p.words).map fun j => ((⟨maskBase p f + j⟩, fOf p f 0 (member p π₁ π₂ (p.bits + j) 0),
        fOf p f 1 (member p π₁ π₂ (p.bits + j) 0)) : FieldH × FieldH × FieldH)).map
        fun t => (.fieldAdd t.1 t.2.1 t.2.2 : Instr) := by
    rw [List.map_map]
    rfl
  have hfa : ∀ o, o < 2 → ∀ c, c < p.M → Ia.fields (fOf p f o c).id = some (x.elem o c) := by
    intro o ho c hc
    rw [a2]
    exact hfld o ho c hc
  obtain ⟨Ib, c1, c2, c3, c4⟩ := runLocal_adds E
    ((List.range p.words).map fun j => ((⟨maskBase p f + j⟩, fOf p f 0 (member p π₁ π₂ (p.bits + j) 0),
        fOf p f 1 (member p π₁ π₂ (p.bits + j) 0)) : FieldH × FieldH × FieldH)) Ia
    (by
      rw [List.map_map]
      show ((List.range p.words).map fun j => maskBase p f + j).Nodup
      rw [map_range_add]
      exact List.nodup_range')
    (by
      intro t ht t' ht'
      simp only [List.mem_map, List.mem_range] at ht ht'
      obtain ⟨j, -, rfl⟩ := ht
      obtain ⟨j', -, rfl⟩ := ht'
      have h1 := fOf_id_lt p f 0 _ (by omega) (hml (p.bits + j') 0)
      have h2 := fOf_id_lt p f 1 _ (by omega) (hml (p.bits + j') 0)
      simp only [maskBase]
      omega)
    (by
      intro t ht
      simp only [List.mem_map, List.mem_range] at ht
      obtain ⟨j, -, rfl⟩ := ht
      rw [hfa 0 (by omega) _ (hml _ _), hfa 1 (by omega) _ (hml _ _)]
      exact ⟨rfl, rfl⟩)
  -- the frees
  obtain ⟨Ic, d1, d2, d3⟩ := runLocal_frees E ([⟨b⟩, ⟨b + 1⟩, ⟨b + 2⟩, ⟨b + 6⟩, ⟨b + 7⟩, ⟨b + 11⟩] ++
    (if p.bits = 0 then [] else [⟨b + 8⟩]) ++ (if p.words = 0 then [] else [⟨b + 9⟩])) Ib
  have hfree : ∀ j, (j = b + 10 ∨ b + 12 ≤ j) → ∀ g ∈ ([⟨b⟩, ⟨b + 1⟩, ⟨b + 2⟩, ⟨b + 6⟩, ⟨b + 7⟩, ⟨b + 11⟩] ++
      (if p.bits = 0 then [] else [⟨b + 8⟩]) ++ (if p.words = 0 then [] else [⟨b + 9⟩]) : List BoolH), g.id ≠ j := by
    intro j hj g hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (hg | hg) | hg
    · rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; omega)
    · have := mem_ite_nil hg
      simp only [List.mem_singleton] at this
      subst this
      show b + 8 ≠ j
      omega
    · have := mem_ite_nil hg
      simp only [List.mem_singleton] at this
      subst this
      show b + 9 ≠ j
      omega
  refine ⟨Ic, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [maskBlock, runLocal_append, runLocal_append, hsl, a1]
    simp only [Option.bind_some]
    rw [had, c1]
    simp only [Option.bind_some]
    exact d1
  · rw [d3 _ (hfree _ (Or.inl rfl)), c2, a3 _ (fun t ht => ?_)]
    · exact hb10
    · simp only [List.mem_map, List.mem_range] at ht
      obtain ⟨j, -, rfl⟩ := ht
      show b + 12 + j ≠ b + 10
      omega
  · intro j hj
    rw [d3 _ (hfree _ (Or.inr (by omega))), c2]
    have := a4 (b + 12 + j, 256 * (p.bits + j), 256 * (p.bits + j) + W)
      (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
    rw [this]
    simp [W]
  · intro j hj
    rw [d2]
    have := c3 (⟨maskBase p f + j⟩, fOf p f 0 (member p π₁ π₂ (p.bits + j) 0),
        fOf p f 1 (member p π₁ π₂ (p.bits + j) 0)) (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
    rw [this, hfa 0 (by omega) _ (hml _ _), hfa 1 (by omega) _ (hml _ _)]
    rfl
  · intro j hj
    rw [d2, c4 j (fun t ht => ?_), a2]
    simp only [List.mem_map, List.mem_range] at ht
    obtain ⟨j', -, rfl⟩ := ht
    show maskBase p f + j' ≠ j
    omega
  · intro j hj
    rw [d2, c4 j (fun t ht => ?_), a2]
    simp only [List.mem_map, List.mem_range] at ht
    obtain ⟨j', hj', rfl⟩ := ht
    show maskBase p f + j' ≠ j
    omega
  · intro j hj
    rw [d3 _ (hfree _ (Or.inr (by omega))), c2, a3 _ (fun t ht => ?_)]
    simp only [List.mem_map, List.mem_range] at ht
    obtain ⟨j', hj', rfl⟩ := ht
    show b + 12 + j' ≠ j
    omega

/-! ## The bit blocks: the program steps -/

/-- **The coins in the engines**: owner `o`, block `j`, bit `i` holds `κ o j i` (whatever each
party input as its reference's bits). -/
def CoinsHold (p : Params) (f : Nat) (I : Ideal) (κ : Nat → Nat → Nat → F) : Prop :=
  ∀ o, o < 2 → ∀ j, j < p.bits → ∀ i, i < W → I.fields (coinH p f o j i).id = some (κ o j i)

/-- What `field-recompose` gives for owner `o`'s block `j`: its coins recomposed, minus its
reference's field value. -/
def recVal (p : Params) (π₁ π₂ : List Nat) (κ : Nat → Nat → Nat → F) (x : Vals) (o j : Nat) : F :=
  TlsMpc.FieldBits.hornerValue ((List.range 255).map (κ o j)) - x.elem o (refOf p π₁ π₂ j)

/-- What `field-bit-check` gives for one coin. -/
def chkVal (κ : Nat → Nat → Nat → F) (o j i : Nat) : F := κ o j i * (κ o j i - TlsMpc.FieldDag.ofNat 1)

/-- **What the bit-block phase opens**: both owners' recompositions, then both owners' bit checks. -/
def bitZ (p : Params) (π₁ π₂ : List Nat) (κ : Nat → Nat → Nat → F) (x : Vals) : List F :=
  (owners.flatMap fun o => (List.range p.bits).map (recVal p π₁ π₂ κ x o)) ++
  (owners.flatMap fun o => (List.range p.bits).flatMap fun j => (List.range W).map (chkVal κ o j))

/-- A bit pair's field value: the field XOR of the two parties' coins. -/
def xorVal (κ : Nat → Nat → Nat → F) (j i : Nat) : F := bitXorValue (κ 0 j i) (κ 1 j i)

def recChunk (p : Params) (π₁ π₂ : List Nat) (κ : Nat → Nat → Nat → F) (x : Vals) (o j : Nat) : List F :=
  (List.range W).map (κ o j) ++ [x.elem o (refOf p π₁ π₂ j)]

def recChunks (p : Params) (π₁ π₂ : List Nat) (κ : Nat → Nat → Nat → F) (x : Vals) : List (List F) :=
  owners.flatMap fun o => (List.range p.bits).map (recChunk p π₁ π₂ κ x o)

def allVals (p : Params) (κ : Nat → Nat → Nat → F) : List F :=
  owners.flatMap fun o => (List.range p.bits).flatMap fun j => (List.range W).map (κ o j)

theorem recChunk_lt (p : Params) (π₁ π₂ : List Nat) (κ : Nat → Nat → Nat → F) (x : Vals) (o j i : Nat)
    (hi : i < 255) : (recChunk p π₁ π₂ κ x o j).getD i 0 = κ o j i := by
  simp [recChunk, List.getD_eq_getElem?_getD, List.getElem?_append_left, hi]

theorem recChunk_last (p : Params) (π₁ π₂ : List Nat) (κ : Nat → Nat → Nat → F) (x : Vals) (o j : Nat) :
    (recChunk p π₁ π₂ κ x o j).getD 255 0 = x.elem o (refOf p π₁ π₂ j) := by
  simp [recChunk, List.getD_eq_getElem?_getD]

theorem length_flatMap_const {α β : Type} (g : α → List β) (n : Nat) : ∀ (l : List α),
    (∀ a ∈ l, (g a).length = n) → (l.flatMap g).length = l.length * n
  | [], _ => by simp
  | a :: l, h => by
    rw [List.flatMap_cons, List.length_append, h a (by simp),
      length_flatMap_const g n l (fun y hy => h y (by simp [hy])), List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem flatten_singletons {α : Type} (l : List α) : (l.map fun a => [a]).flatten = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem allVals_length (p : Params) (κ : Nat → Nat → Nat → F) : (allVals p κ).length = 2 * (p.bits * W) := by
  unfold allVals
  rw [length_flatMap_const _ (p.bits * W) owners (fun o _ => by
    rw [length_flatMap_const _ W _ (fun j _ => by simp), List.length_range])]
  rfl

theorem coin_lt (p : Params) (o j i : Nat) (ho : o < 2) (hj : j < p.bits) (hi : i < W) :
    o * (p.bits * W) + j * W + i < 2 * (p.bits * W) := by
  have h1 : (j + 1) * W ≤ p.bits * W := Nat.mul_le_mul_right _ hj
  have h2 : o * (p.bits * W) ≤ 1 * (p.bits * W) := Nat.mul_le_mul_right _ (by omega)
  simp only [Nat.succ_mul] at h1
  omega

theorem block_lt (n j i : Nat) (hj : j < n) (hi : i < W) : j * W + i < n * W := by
  have h1 : (j + 1) * W ≤ n * W := Nat.mul_le_mul_right _ hj
  simp only [Nat.succ_mul] at h1
  omega

theorem recOuts_block (p : Params) (f : Nat) :
    recOuts p f = (List.range (2 * p.bits)).map (fun q => (⟨coinBase p f + 2 * (p.bits * W) + q⟩ : FieldH)) := by
  unfold recOuts
  rw [owners_range]
  apply List.map_congr_left
  intro q _
  split
  · simp [recH]
  · simp only [recH, FieldH.mk.injEq]
    omega

/-- **The recomposition and the bit checks**: with the coins `κ` and the references' field values
in the engines, the two program steps succeed, open nothing themselves, and the handles the
script then opens hold `bitZ`; the coins and everything below them stay. -/
theorem coins_programs (E : Env) (hP : ProgsLoaded E) (p : Params) (f : Nat) (π₁ π₂ : List Nat) (I : Ideal)
    (κ : Nat → Nat → Nat → F) (x : Vals) (hc : CoinsHold p f I κ)
    (hfld : ∀ o, o < 2 → ∀ j, j < p.bits →
      I.fields (fOf p f o (refOf p π₁ π₂ j)).id = some (x.elem o (refOf p π₁ π₂ j))) :
    ∃ pr vi vo pc vi2 vo2,
      E.programs recomposeName = some pr ∧ (recIns p f π₁ π₂).mapM (fun g => I.fields g.id) = some vi ∧
      runProgram pr (2 * p.bits) vi [] = some (vo, []) ∧ vo.length = (recOuts p f).length ∧
      E.programs bitCheckName = some pc ∧
      (allCoins p f).mapM (fun g => (I.setFields (recOuts p f) vo).fields g.id) = some vi2 ∧
      runProgram pc (2 * (p.bits * W)) vi2 [] = some (vo2, []) ∧ vo2.length = (chkOuts p f).length ∧
      (recOuts p f ++ chkOuts p f).mapM
        (fun g => ((I.setFields (recOuts p f) vo).setFields (chkOuts p f) vo2).fields g.id) =
          some (bitZ p π₁ π₂ κ x) ∧
      ((I.setFields (recOuts p f) vo).setFields (chkOuts p f) vo2).bools = I.bools ∧
      (∀ j, j < coinBase p f + 2 * (p.bits * W) →
        ((I.setFields (recOuts p f) vo).setFields (chkOuts p f) vo2).fields j = I.fields j) := by
  obtain ⟨pr, hpr, hcr⟩ := hP.recompose
  obtain ⟨pc, hpc, hcc⟩ := hP.bitCheck
  -- the recomposition's inputs and outputs
  have hins : (recIns p f π₁ π₂).mapM (fun g => I.fields g.id) = some (recChunks p π₁ π₂ κ x).flatten := by
    unfold recIns recChunks
    rw [flatten_flatMap']
    simp only [flatten_map']
    apply mapM_flatMap_vals
    intro o ho
    apply mapM_flatMap_vals
    intro j hj
    unfold recChunk
    refine mapM_append_vals _ _ _ _ _ ?_ ?_
    · exact mapM_map_vals _ _ _ _ (fun i hi =>
        hc o (owners_lt ho) j (List.mem_range.mp hj) i (List.mem_range.mp hi))
    · have e := hfld o (owners_lt ho) j (List.mem_range.mp hj)
      unfold refOf at e ⊢
      simp [e]
  have hlenC : ∀ c ∈ recChunks p π₁ π₂ κ x, c.length = 256 := by
    intro c hc'
    simp only [recChunks, List.mem_flatMap, List.mem_map] at hc'
    obtain ⟨o, -, j, -, rfl⟩ := hc'
    rw [recChunk, List.length_append, List.length_map, List.length_range]
    rfl
  have hnC : (recChunks p π₁ π₂ κ x).length = 2 * p.bits := by
    rw [recChunks, owners_flatMap, List.length_append, List.length_map, List.length_map, List.length_range]
    omega
  have hrun := runProgram_chunks pr 256 [.pub] _ hcr (recChunks p π₁ π₂ κ x) hlenC
  rw [hnC] at hrun
  have hvo : ((recChunks p π₁ π₂ κ x).map fun c =>
      [TlsMpc.FieldBits.hornerValue ((List.range 255).map fun i => c.getD i 0) - c.getD 255 0]).flatten =
      owners.flatMap fun o => (List.range p.bits).map (recVal p π₁ π₂ κ x o) := by
    rw [flatten_map_singleton' (fun c : List F =>
      TlsMpc.FieldBits.hornerValue ((List.range 255).map fun i => c.getD i 0) - c.getD 255 0)]
    simp only [recChunks, List.map_flatMap, List.map_map, Function.comp_def]
    apply flatMap_congr'
    intro o _
    apply List.map_congr_left
    intro j _
    have e : (List.range 255).map (fun i => (recChunk p π₁ π₂ κ x o j).getD i 0) = (List.range 255).map (κ o j) := by
      apply List.map_congr_left
      intro i hi
      exact recChunk_lt p π₁ π₂ κ x o j i (List.mem_range.mp hi)
    rw [recChunk_last, e]
    rfl
  have hvolen : (owners.flatMap fun o => (List.range p.bits).map (recVal p π₁ π₂ κ x o)).length = 2 * p.bits := by
    rw [owners_flatMap, List.length_append, List.length_map, List.length_map, List.length_range]
    omega
  obtain ⟨r1, r2, r3⟩ := setFields_block I (fun q => (⟨coinBase p f + 2 * (p.bits * W) + q⟩ : FieldH))
    (coinBase p f + 2 * (p.bits * W)) (2 * p.bits)
    (owners.flatMap fun o => (List.range p.bits).map (recVal p π₁ π₂ κ x o)) (fun _ _ => rfl) hvolen
  rw [← recOuts_block] at r1 r2 r3
  -- the bit checks' inputs and outputs
  have hcoinI : ∀ o, o < 2 → ∀ j, j < p.bits → ∀ i, i < W →
      (I.setFields (recOuts p f) (owners.flatMap fun o => (List.range p.bits).map (recVal p π₁ π₂ κ x o))).fields
        (coinH p f o j i).id = some (κ o j i) := by
    intro o ho j hj i hi
    rw [r2 _ (Or.inl ?_)]
    · exact hc o ho j hj i hi
    · have := coin_lt p o j i ho hj hi
      show coinBase p f + o * (p.bits * W) + j * W + i < _
      omega
  have hall : (allCoins p f).mapM (fun g =>
      (I.setFields (recOuts p f) (owners.flatMap fun o => (List.range p.bits).map (recVal p π₁ π₂ κ x o))).fields g.id) =
      some (allVals p κ) := by
    unfold allCoins allVals
    apply mapM_flatMap_vals
    intro o ho
    apply mapM_flatMap_vals
    intro j hj
    exact mapM_map_vals _ _ _ _ (fun i hi =>
      hcoinI o (owners_lt ho) j (List.mem_range.mp hj) i (List.mem_range.mp hi))
  have hrun2 := runProgram_chunks pc 1 [.pub] _ hcc ((allVals p κ).map fun a => [a]) (by
    intro c hc'
    simp only [List.mem_map] at hc'
    obtain ⟨a, -, rfl⟩ := hc'
    rfl)
  rw [List.length_map, allVals_length, flatten_singletons, List.map_map] at hrun2
  have hvo2 : ((allVals p κ).map ((fun c : List F =>
      [c.getD 0 0 * (c.getD 0 0 - TlsMpc.FieldDag.ofNat 1)]) ∘ fun a => [a])).flatten =
      (allVals p κ).map (fun a => a * (a - TlsMpc.FieldDag.ofNat 1)) :=
    flatten_map_singleton' (fun a : F => a * (a - TlsMpc.FieldDag.ofNat 1)) (allVals p κ)
  have hvo2len : ((allVals p κ).map (fun a => a * (a - TlsMpc.FieldDag.ofNat 1))).length = 2 * (p.bits * W) := by
    rw [List.length_map, allVals_length]
  obtain ⟨k1, k2, k3⟩ := setFields_block
    (I.setFields (recOuts p f) (owners.flatMap fun o => (List.range p.bits).map (recVal p π₁ π₂ κ x o)))
    (chkH p f) (coinBase p f + 2 * (p.bits * W) + 2 * p.bits) (2 * (p.bits * W))
    ((allVals p κ).map (fun a => a * (a - TlsMpc.FieldDag.ofNat 1))) (fun _ _ => rfl) hvo2len
  refine ⟨pr, (recChunks p π₁ π₂ κ x).flatten,
    owners.flatMap fun o => (List.range p.bits).map (recVal p π₁ π₂ κ x o), pc, allVals p κ,
    (allVals p κ).map (fun a => a * (a - TlsMpc.FieldDag.ofNat 1)), hpr, hins, ?_, ?_, hpc, hall, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hvo]
    exact hrun
  · rw [hvolen, recOuts_block]
    simp
  · rw [← hvo2]
    exact hrun2
  · rw [hvo2len]
    simp [chkOuts]
  · unfold bitZ
    refine mapM_append_vals _ _ _ _ _ ?_ ?_
    · rw [recOuts_block]
      refine mapM_block _ _ (coinBase p f + 2 * (p.bits * W)) (2 * p.bits) _ (fun _ _ => rfl) hvolen
        (fun i hi => ?_)
      have := k2 (coinBase p f + 2 * (p.bits * W) + i) (Or.inl (by omega))
      rw [← recOuts_block]
      show ((I.setFields (recOuts p f) _).setFields ((List.range (2 * (p.bits * W))).map (chkH p f)) _).fields _ = _
      rw [this]
      exact r3 i hi
    · have e : (owners.flatMap fun o => (List.range p.bits).flatMap fun j => (List.range W).map (chkVal κ o j)) =
          (allVals p κ).map (fun a => a * (a - TlsMpc.FieldDag.ofNat 1)) := by
        simp only [allVals, List.map_flatMap, List.map_map]
        rfl
      rw [e]
      exact mapM_block _ (chkH p f) (coinBase p f + 2 * (p.bits * W) + 2 * p.bits) (2 * (p.bits * W)) _
        (fun _ _ => rfl) hvo2len k3
  · show ((I.setFields (recOuts p f) _).setFields ((List.range (2 * (p.bits * W))).map (chkH p f)) _).bools = _
    rw [k1, r1]
  · intro j hj
    show ((I.setFields (recOuts p f) _).setFields ((List.range (2 * (p.bits * W))).map (chkH p f)) _).fields j = _
    rw [k2 j (Or.inl (by omega)), r2 j (Or.inl hj)]

/-- **The field XOR of the coins**: the program step succeeds, opens nothing, and bit pair
(j, i)'s field handle holds `xorVal κ j i`. -/
theorem coins_xor (E : Env) (hP : ProgsLoaded E) (p : Params) (f : Nat) (J : Ideal) (κ : Nat → Nat → Nat → F)
    (hc : CoinsHold p f J κ) :
    ∃ px vi vo, E.programs bitXorName = some px ∧ (xorIns p f).mapM (fun g => J.fields g.id) = some vi ∧
      runProgram px (p.bits * W) vi [] = some (vo, []) ∧ vo.length = (xorOuts p f).length ∧
      (J.setFields (xorOuts p f) vo).bools = J.bools ∧
      (∀ j, j < p.bits → ∀ i, i < W →
        (J.setFields (xorOuts p f) vo).fields (xorH p f (j * W + i)).id = some (xorVal κ j i)) ∧
      (∀ id, id < coinBase p f + 4 * (p.bits * W) + 2 * p.bits →
        (J.setFields (xorOuts p f) vo).fields id = J.fields id) := by
  obtain ⟨px, hpx, hcx⟩ := hP.bitXor
  have hins : (xorIns p f).mapM (fun g => J.fields g.id) =
      some ((List.range p.bits).flatMap fun j => (List.range W).map fun i => [κ 0 j i, κ 1 j i]).flatten := by
    unfold xorIns
    rw [flatten_flatMap']
    simp only [flatten_map']
    apply mapM_flatMap_vals
    intro j hj
    apply mapM_flatMap_vals
    intro i hi
    simp [hc 0 (by omega) j (List.mem_range.mp hj) i (List.mem_range.mp hi),
      hc 1 (by omega) j (List.mem_range.mp hj) i (List.mem_range.mp hi)]
  have hrun := runProgram_chunks px 2 [.never] _ hcx
    ((List.range p.bits).flatMap fun j => (List.range W).map fun i => [κ 0 j i, κ 1 j i]) (by
      intro c hc'
      simp only [List.mem_flatMap, List.mem_map] at hc'
      obtain ⟨j, -, i, -, rfl⟩ := hc'
      rfl)
  rw [length_flatMap_const _ W _ (fun j _ => by simp), List.length_range] at hrun
  have hvo : (((List.range p.bits).flatMap fun j => (List.range W).map fun i => [κ 0 j i, κ 1 j i]).map
      fun c => [bitXorValue (c.getD 0 0) (c.getD 1 0)]).flatten =
      ((List.range p.bits).map fun j => (List.range W).map (xorVal κ j)).flatten := by
    rw [flatten_map_singleton' (fun c : List F => bitXorValue (c.getD 0 0) (c.getD 1 0)), flatten_map']
    simp only [List.map_flatMap, List.map_map]
    rfl
  have hvolen : (((List.range p.bits).map fun j => (List.range W).map (xorVal κ j)).flatten).length = p.bits * W := by
    rw [length_flatten_eq W _ (by
      intro y hy
      simp only [List.mem_map] at hy
      obtain ⟨j, -, rfl⟩ := hy
      simp), List.length_map, List.length_range]
  obtain ⟨k1, k2, k3⟩ := setFields_block J (xorH p f) (coinBase p f + 4 * (p.bits * W) + 2 * p.bits) (p.bits * W)
    ((List.range p.bits).map fun j => (List.range W).map (xorVal κ j)).flatten (fun _ _ => rfl) hvolen
  refine ⟨px, ((List.range p.bits).flatMap fun j => (List.range W).map fun i => [κ 0 j i, κ 1 j i]).flatten,
    ((List.range p.bits).map fun j => (List.range W).map (xorVal κ j)).flatten,
    hpx, hins, ?_, ?_, k1, fun j hj i hi => ?_, fun id hid => k2 id (Or.inl hid)⟩
  · rw [← hvo]
    exact hrun
  · rw [hvolen]
    simp [xorOuts]
  · have := k3 (j * W + i) (block_lt p.bits j i hj hi)
    show (J.setFields ((List.range (p.bits * W)).map (xorH p f)) _).fields
      (coinBase p f + 4 * (p.bits * W) + 2 * p.bits + (j * W + i)) = _
    rw [this, flatten_getD W _ j i 0 (by
      intro y hy
      simp only [List.mem_map] at hy
      obtain ⟨j', -, rfl⟩ := hy
      simp) (by simpa using hj) hi, getD_map_range _ _ _ _ hj, getD_map_range _ _ _ _ hi]

/-- **The bit pairs' Boolean handles**: one-bit slices of the bundle. -/
theorem pairSlices_block (E : Env) (p : Params) (b : Nat) (J : Ideal) (bundle : Bits)
    (hb10 : J.bools (b + 10) = some bundle) (hlen : bundle.length = p.N * 256) (hbits : p.bits ≤ p.N) :
    ∃ J', runLocal E (pairSlices p b) J = some J' ∧ J'.fields = J.fields ∧
      (∀ j, j < p.bits → ∀ i, i < W →
        J'.bools (bitBase p b + j * W + i) = some ((bundle.drop (256 * j + i)).take 1)) ∧
      (∀ id, id < bitBase p b → J'.bools id = J.bools id) := by
  have hts : pairSlices p b =
      ((List.range p.bits).flatMap fun j => (List.range W).map fun i =>
        (bitBase p b + j * W + i, 256 * j + i, 256 * j + i + 1)).map
        fun t => (.slice ⟨t.1⟩ ⟨b + 10⟩ t.2.1 t.2.2 : Instr) := by
    simp only [pairSlices, List.map_flatMap, List.map_map]
    rfl
  obtain ⟨J', a1, a2, a3, a4⟩ := runLocal_slices E ⟨b + 10⟩ bundle
    ((List.range p.bits).flatMap fun j => (List.range W).map fun i =>
        (bitBase p b + j * W + i, 256 * j + i, 256 * j + i + 1)) J hb10
    (by
      intro t ht
      simp only [List.mem_flatMap, List.mem_map, List.mem_range] at ht
      obtain ⟨j, hj, i, hi, rfl⟩ := ht
      refine ⟨by show bitBase p b + j * W + i ≠ b + 10; unfold bitBase; omega,
        by show 256 * j + i ≤ 256 * j + i + 1; omega, ?_⟩
      show 256 * j + i + 1 ≤ bundle.length
      rw [hlen]
      have : i < 255 := hi
      omega)
    (by
      simp only [List.map_flatMap, List.map_map, Function.comp_def]
      have := flatMap_range_mul (fun q => bitBase p b + q) W p.bits
      simp only [Nat.add_assoc] at this ⊢
      rw [this, map_range_add]
      exact List.nodup_range')
  refine ⟨J', by rw [hts]; exact a1, a2, fun j hj i hi => ?_, fun id hid => a3 id (fun t ht => ?_)⟩
  · have := a4 (bitBase p b + j * W + i, 256 * j + i, 256 * j + i + 1) (by
      simp only [List.mem_flatMap, List.mem_map, List.mem_range]
      exact ⟨j, hj, i, hi, rfl⟩)
    rw [this]
    simp
  · simp only [List.mem_flatMap, List.mem_map, List.mem_range] at ht
    obtain ⟨j, -, i, -, rfl⟩ := ht
    show bitBase p b + j * W + i ≠ id
    omega

end TlsMpc.Node.Flows.Masks
