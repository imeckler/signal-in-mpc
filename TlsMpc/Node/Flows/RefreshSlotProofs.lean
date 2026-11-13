import TlsMpc.Node.Flows.RefreshFlowProofs
import TlsMpc.KernelSpecs.BundleSlotWhole

/-!
# T4-REFRESH, the parse: `bundle-slot` fed by the script computes `BundleResponse.device`

REORGANIZATION_PLAN.md stage S15. No I/O; no emitter imports this module.

PROVED (ideal model; the circuit under `bundle-slot FIRST LAST ONETIME` computes its Lean kernel,
the trusted correspondence of T2 as `Contacts.Loaded` states it for the contact kernels):

  * `slotInput_value`: from the held body `X` (the bytes the server sent, collected unopened), the
    five instructions of `slotInput` leave in handle `n + 4` exactly the bits of
    `slotBytes X start w first last ++ widthsOf w`: the header, the byte before the item, the item
    SPLICED by `BundleSlots.spliced w … slotFiller`, the byte after it, the body's last two bytes —
    and the digit counts of the SAME `w`. This is the one-source property at the model level: the
    splice and the declared counts cannot disagree (`BundleSlotWhole.inconsistent_width_accepts`
    needs them to).
  * `slot_inputs`: on those bytes, the kernel's named inputs are exactly the hypotheses `inputs`
    and `widths` of `BundleSlotWhole.bundleSlot_device` (and of `bundleSlot_parses_or_refuses`,
    `bundleSlot_any_widths`).
  * `parse_device`: so, for the body the server sent and an item placed as `layout?` places it
    with its true counts `w`, the fields handle `n + 5` holds the bits of
    `BundleResponse.device` on the body at `start` with `w` (`bundleSlot_device`);
    `parse_parses_or_refuses`: for counts `w` that are not the item's, every field the kernel
    outputs is zero (`bundleSlot_wrong_counts` / `bundleSlot_parses_or_refuses`): the device is
    refused.
-/

namespace TlsMpc.Node.Flows.Refresh

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open TlsMpc.Node.Flows.TlsBase
open TlsMpc.Signal.BundleResponse (Widths)
open TlsMpc.KernelSpecs
open Std.Tactic.BVDecide

abbrev Byte := BitVec 8

/-! ## Bits of bytes, read back by `pick` -/

theorem bitsOfByte_getD (x : Byte) : ∀ j, j < 8 → (bitsOfByte x).getD j false = x.getLsbD j
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl
  | 7, _ => rfl
  | j + 8, h => absurd h (by omega)

theorem getD_bitsOf : ∀ (X : B8) (p j : Nat), p < X.length → j < 8 →
    (bitsOf X).getD (8 * p + j) false = (X.getD p 0).getLsbD j
  | [], _, _, h, _ => absurd h (by simp)
  | x :: X, 0, j, _, hj => by
    rw [bitsOf_cons, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
      ← List.getD_eq_getElem?_getD, Nat.mul_zero, Nat.zero_add, bitsOfByte_getD x j hj]
    rfl
  | x :: X, p + 1, j, hp, hj => by
    rw [bitsOf_cons, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega),
      ← List.getD_eq_getElem?_getD, length_bitsOfByte, show 8 * (p + 1) + j - 8 = 8 * p + j by omega,
      getD_bitsOf X p j (by simp at hp; omega) hj]
    rfl

theorem pick_byte (Y : B8) (p : Nat) (hp : p < Y.length) :
    (List.range' (8 * p) 8).map ((bitsOf Y).getD · false) = bitsOfByte (Y.getD p 0) := by
  simp only [List.range'_succ, List.range'_zero, List.map_cons, List.map_nil]
  have e : ∀ j, j < 8 → (bitsOf Y).getD (8 * p + j) false = (Y.getD p 0).getLsbD j :=
    fun j hj => getD_bitsOf Y p j hp hj
  have e0 := e 0 (by omega)
  simp only [Nat.add_zero] at e0
  rw [e0, e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega), e 6 (by omega),
    e 7 (by omega)]
  rfl

/-- **`pick` of byte positions reads those bytes.** -/
theorem pick_bytes (Y : B8) : ∀ (ps : List Nat), (∀ p ∈ ps, p < Y.length) →
    (byteBits ps).map ((bitsOf Y).getD · false) = bitsOf (ps.map (Y.getD · 0))
  | [], _ => rfl
  | p :: ps, h => by
    simp only [byteBits, List.flatMap_cons, List.map_append, List.map_cons, bitsOf_cons]
    rw [pick_byte Y p (h p (by simp))]
    exact congrArg _ (pick_bytes Y ps (fun q hq => h q (by simp [hq])))

theorem byteBits_lt (ps : List Nat) (m : Nat) (h : ∀ p ∈ ps, p < m) : ∀ i ∈ byteBits ps, i < 8 * m := by
  intro i hi
  simp only [byteBits, List.mem_flatMap, List.mem_range'_1] at hi
  obtain ⟨p, hp, h1, h2⟩ := hi
  have := h p hp
  omega

theorem length_byteBits (ps : List Nat) : (byteBits ps).length = 8 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [byteBits, List.flatMap_cons] at ih ⊢; omega

/-! ## The positions of the cut and the splice -/

theorem take_succ_drop (Y : B8) (p c : Nat) (h : p < Y.length) :
    (Y.drop p).take (c + 1) = Y[p] :: (Y.drop (p + 1)).take c := by
  rw [List.drop_eq_getElem_cons h, List.take_succ_cons]

theorem range'_map' (Y : B8) : ∀ (p c : Nat), p + c ≤ Y.length → (List.range' p c).map (Y.getD · 0) = (Y.drop p).take c
  | p, 0, _ => by simp
  | p, c + 1, h => by
    rw [List.range'_succ, List.map_cons, range'_map' Y (p + 1) c (by omega), take_succ_drop Y p c (by omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

/-- The runs' copies, added. -/
def copies (rs : List (Nat × Nat)) : Nat := (rs.map Prod.snd).sum

theorem runPositions_map (X : B8) (z : Byte) : ∀ (rs : List (Nat × Nat)) (p : Nat), p + copies rs ≤ X.length →
    (runPositions X.length p rs).map ((X ++ [z]).getD · 0) = BundleSlotWhole.applyRuns z rs (X.drop p)
  | [], _, _ => rfl
  | (k, c) :: rs, p, h => by
    simp only [copies, List.map_cons, List.sum_cons] at h
    simp only [runPositions, List.map_append, BundleSlotWhole.applyRuns]
    have hz : (X ++ [z]).getD X.length 0 = z := by simp
    rw [List.map_replicate, hz, range'_map' (X ++ [z]) p c (by simp; omega),
      runPositions_map X z rs (p + c) (by simp only [copies]; omega), List.drop_drop]
    rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

theorem applyRuns_take (z : Byte) : ∀ (rs : List (Nat × Nat)) (bytes : B8) (m : Nat), copies rs ≤ m →
    BundleSlotWhole.applyRuns z rs bytes = BundleSlotWhole.applyRuns z rs (bytes.take m)
  | [], _, _, _ => rfl
  | (k, c) :: rs, bytes, m, h => by
    simp only [copies, List.map_cons, List.sum_cons] at h
    simp only [BundleSlotWhole.applyRuns]
    rw [List.take_take, Nat.min_eq_left (by omega), List.drop_take,
      applyRuns_take z rs (bytes.drop c) (m - c) (by simp only [copies]; omega)]

theorem copies_merge (rs : List (Nat × Nat)) : copies (TlsMpc.Signal.BundleSlots.merge rs) = copies rs := by
  induction rs using TlsMpc.Signal.BundleSlots.merge.induct with
  | case1 k c c' rest ih =>
    rw [TlsMpc.Signal.BundleSlots.merge.eq_1, ih]
    simp only [copies, List.map_cons, List.sum_cons]
    omega
  | case2 r rest h ih =>
    rw [TlsMpc.Signal.BundleSlots.merge.eq_2 r rest h]
    simp only [copies, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
  | case3 => rw [TlsMpc.Signal.BundleSlots.merge.eq_3]

open TlsMpc.Signal.BundleResponse (Piece) in
theorem copies_runs : ∀ (P Q : List Piece), BundleSlotWhole.Fits P Q →
    copies (TlsMpc.Signal.BundleSlots.runs P Q) = TlsMpc.Signal.BundleResponse.size P
  | [], [], _ => rfl
  | .text t :: P, .text t' :: Q, ⟨_, hf⟩ => by
    have := copies_runs P Q hf
    simp only [copies, TlsMpc.Signal.BundleSlots.runs, List.map_cons, List.sum_cons] at this ⊢
    rw [this, BundleSlotWhole.size_text]
    rfl
  | .field n :: P, .field m :: Q, ⟨_, hf⟩ => by
    have := copies_runs P Q hf
    simp only [copies, TlsMpc.Signal.BundleSlots.runs, List.map_cons, List.sum_cons] at this ⊢
    rw [this, BundleSlotWhole.size_field]
  | [], _ :: _, h => by simp [BundleSlotWhole.Fits] at h
  | _ :: _, [], h => by simp [BundleSlotWhole.Fits] at h
  | .text _ :: _, .field _ :: _, h => by simp [BundleSlotWhole.Fits] at h
  | .field _ :: _, .text _ :: _, h => by simp [BundleSlotWhole.Fits] at h

theorem copies_splice (w : Widths) (ok : w.ok = true) : copies (TlsMpc.Signal.BundleSlots.splice w) = itemSize w := by
  rw [TlsMpc.Signal.BundleSlots.splice, copies_merge, copies_runs _ _ (BundleSlotWhole.fits_item w ok)]
  rfl

/-- **What `bundle-slot`'s byte inputs are, for the body `X`**: header, the byte before the item
(unless first), the item spliced by `BundleSlots.spliced w` with `slotFiller`, the byte after it
(unless last), the last two bytes. Exactly the right side of `bundleSlot_device`'s `inputs`. -/
def slotBytes (X : B8) (start : Nat) (w : Widths) (first last : Bool) : B8 :=
  TlsMpc.Signal.Establish.part X 0 TlsMpc.Signal.BundleResponse.firstItem ++ (if first then [] else TlsMpc.Signal.Establish.part X (start - 1) 1) ++
    TlsMpc.Signal.BundleSlots.spliced w (TlsMpc.Signal.Establish.part X start (itemSize w)) slotFiller ++
    (if last then [] else TlsMpc.Signal.Establish.part X (start + itemSize w) 1) ++ TlsMpc.Signal.Establish.part X (X.length - 2) 2

theorem placedOk_spec {total start : Nat} {w : Widths} {first last : Bool} (h : placedOk total start w first last = true) :
    w.ok = true ∧ TlsMpc.Signal.BundleResponse.firstItem ≤ start ∧ start + itemSize w + 2 ≤ total ∧
      (first = true ↔ start = TlsMpc.Signal.BundleResponse.firstItem) ∧ (last = true ↔ start + itemSize w + 2 = total) := by
  simp only [placedOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · cases first <;> simp_all
  · cases last <;> simp_all

theorem singleton_part (X : B8) (p : Nat) (h : p < X.length) : [X.getD p 0] = TlsMpc.Signal.Establish.part X p 1 := by
  simp only [TlsMpc.Signal.Establish.part, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  rw [List.drop_eq_getElem_cons h]
  rfl

/-- **The cut's positions read the cut, with the item spliced.** -/
theorem cutPositions_map (X : B8) (start : Nat) (w : Widths) (first last : Bool)
    (h : placedOk X.length start w first last = true) :
    (cutPositions X.length start w first last).map ((X ++ [slotFiller]).getD · 0) = slotBytes X start w first last := by
  obtain ⟨ok, h1, h2, _, _⟩ := placedOk_spec h
  have fi : TlsMpc.Signal.BundleResponse.firstItem = 73 := rfl
  have hY : ∀ p, p < X.length → (X ++ [slotFiller]).getD p 0 = X.getD p 0 := by
    intro p hp
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hp]
  simp only [cutPositions, List.map_append]
  rw [range'_map' (X ++ [slotFiller]) 0 _ (by simp; omega), List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp; omega), runPositions_map X slotFiller _ start
      (by rw [copies_splice w ok]; omega)]
  have e1 : (if first = true then ([] : List Nat) else [start - 1]).map ((X ++ [slotFiller]).getD · 0) =
      if first = true then [] else TlsMpc.Signal.Establish.part X (start - 1) 1 := by
    cases first
    · simp only [Bool.false_eq_true, if_false, List.map_cons, List.map_nil]
      rw [hY _ (by omega), singleton_part X _ (by omega)]
    · rfl
  have e2 : (if last = true then ([] : List Nat) else [start + itemSize w]).map ((X ++ [slotFiller]).getD · 0) =
      if last = true then [] else TlsMpc.Signal.Establish.part X (start + itemSize w) 1 := by
    cases last
    · simp only [Bool.false_eq_true, if_false, List.map_cons, List.map_nil]
      rw [hY _ (by omega), singleton_part X _ (by omega)]
    · rfl
  have e3 : [X.length - 2, X.length - 1].map ((X ++ [slotFiller]).getD · 0) = TlsMpc.Signal.Establish.part X (X.length - 2) 2 := by
    simp only [List.map_cons, List.map_nil, TlsMpc.Signal.Establish.part]
    rw [hY _ (by omega), hY _ (by omega), ← range'_map' X (X.length - 2) 2 (by omega)]
    simp only [List.range'_succ, List.range'_zero, List.map_cons, List.map_nil]
    rw [show X.length - 2 + 1 = X.length - 1 by omega]
  rw [e1, e2, e3]
  simp only [slotBytes]
  rw [applyRuns_take slotFiller _ (X.drop start) (itemSize w) (by rw [copies_splice w ok]; exact Nat.le_refl _),
    TlsMpc.Signal.BundleSlots.splice, BundleSlotWhole.applyRuns_merge, ← BundleSlotWhole.spliced_eq]
  rfl

/-! ## The model: plain steps one at a time -/

theorem bools_set (I : Ideal) (o : BoolH) (v : Bits) (j : Nat) :
    (I.setBool o v).bools j = if j = o.id then some v else I.bools j := rfl

theorem runPlain_step {E : Env} {i : Instr} {is : List Instr} {I I1 : Ideal} (h : plainStep E i I = some I1) :
    runPlain E (i :: is) I = runPlain E is I1 := by
  simp [runPlain, h]

theorem runPlain_append_some {E : Env} : ∀ {is js : List Instr} {I I1 : Ideal}, runPlain E is I = some I1 →
    runPlain E (is ++ js) I = runPlain E js I1
  | [], _, I, I1, h => by simp only [runPlain, Option.some.injEq] at h; subst h; rfl
  | i :: is, js, I, I1, h => by
    simp only [runPlain] at h
    simp only [List.cons_append, runPlain]
    split at h
    · next I' hI' => exact runPlain_append_some h
    · cases h

theorem plainStep_public (E : Env) (o : BoolH) (v : Bits) (I : Ideal) :
    plainStep E (.boolPublic o v) I = some (I.setBool o v) := rfl

theorem plainStep_concat (E : Env) (o : BoolH) (I : Ideal) (parts : List BoolH) (vs : List Bits) (v : Bits)
    (h : parts.mapM (fun h => I.bools h.id) = some vs) (hv : vs.flatten = v) :
    plainStep E (.concat o parts) I = some (I.setBool o v) := by
  subst hv
  simp [plainStep, idealStep, blankWire, InstrP.map, h]

theorem plainStep_pick (E : Env) (o : BoolH) (I : Ideal) (h : BoolH) (idx : List Nat) (v : Bits)
    (hv : I.bools h.id = some v) (hall : idx.all (· < v.length) = true) :
    plainStep E (.pick o h idx) I = some (I.setBool o (idx.map (v.getD · false))) := by
  simp only [plainStep, idealStep, blankWire, InstrP.map, hv, hall, if_true]

theorem plainStep_slice (E : Env) (o : BoolH) (I : Ideal) (h : BoolH) (lo hi : Nat) (v : Bits)
    (hv : I.bools h.id = some v) (hl : lo ≤ hi ∧ hi ≤ v.length) :
    plainStep E (.slice o h lo hi) I = some (I.setBool o ((v.drop lo).take (hi - lo))) := by
  simp only [plainStep, idealStep, blankWire, InstrP.map, hv, if_pos hl]

theorem plainStep_run (E : Env) (o : BoolH) (I : Ideal) (name : Bytes) (c : Circuit) (h : BoolH) (v : Bits)
    (hc : E.circuits name = some c) (hv : I.bools h.id = some v) (hl : v.length = c.inWidth) :
    plainStep E (.run o name 1 h) I = some (I.setBool o (c.eval v)) := by
  simp only [plainStep, idealStep, blankWire, InstrP.map, hc, hv, Nat.one_mul, if_pos hl]
  rw [runCopies_one' c v hl]

theorem plainStep_free (E : Env) (h : BoolH) (I : Ideal) :
    plainStep E (.freeBool h) I = some (I.dropBool h) := rfl

/-! ## The model: what `slotInput` leaves -/

theorem cutPositions_lt (X : B8) (start : Nat) (w : Widths) (first last : Bool)
    (h : placedOk X.length start w first last = true) :
    ∀ p ∈ cutPositions X.length start w first last, p < X.length + 1 := by
  obtain ⟨ok, h1, h2, _, _⟩ := placedOk_spec h
  intro p hp
  have fi : TlsMpc.Signal.BundleResponse.firstItem = 73 := rfl
  simp only [cutPositions, List.mem_append, List.mem_range'_1] at hp
  rcases hp with (((h | h) | h) | h) | h
  · omega
  · split at h <;> simp at h; omega
  · -- the splice's positions: the filler, or the item's bytes
    have key : ∀ (rs : List (Nat × Nat)) (q : Nat), q + copies rs ≤ X.length →
        ∀ r ∈ runPositions X.length q rs, r < X.length + 1 := by
      intro rs
      induction rs with
      | nil => intro q _ r hr; simp [runPositions] at hr
      | cons a rs ih =>
        intro q hq r hr
        obtain ⟨k, c⟩ := a
        simp only [copies, List.map_cons, List.sum_cons] at hq
        simp only [runPositions, List.mem_append, List.mem_replicate, List.mem_range'_1] at hr
        rcases hr with (hr | hr) | hr
        · omega
        · omega
        · exact ih (q + c) (by simp only [copies]; omega) r hr
    exact key _ start (by rw [copies_splice w ok]; omega) p h
  · split at h <;> simp at h; omega
  · simp at h; omega

theorem slotIndices_lt (X : B8) (start : Nat) (w : Widths) (first last : Bool)
    (h : placedOk X.length start w first last = true) :
    ∀ i ∈ slotIndices X.length start w first last, i < 8 * (X.length + 1) :=
  byteBits_lt _ _ (cutPositions_lt X start w first last h)

theorem bitsOf_length_cut (X : B8) (start : Nat) (w : Widths) (first last : Bool) :
    (slotIndices X.length start w first last).length = 8 * (cutPositions X.length start w first last).length :=
  length_byteBits _

/-- **The one-source property in the model.** From the held body `X` (handle `body`), the five
instructions of `slotInput` leave in handle `n + 4` exactly the bits of the cut with the item
spliced by `BundleSlots.spliced w` followed by `widthsOf w`: one `w` for both. -/
theorem slotInput_value (E : Env) (n : Nat) (body : BoolH) (X : B8) (start : Nat) (w : Widths) (first last : Bool)
    (I : Ideal) (hb : I.bools body.id = some (bitsOf X)) (hbn : body.id < n)
    (hp : placedOk X.length start w first last = true) :
    ∃ I', runPlain E (slotInput n body X.length start w first last) I = some I' ∧
      I'.bools (n + 4) = some (bitsOf (slotBytes X start w first last ++ widthsOf w)) ∧
      ∀ j, j < n → I'.bools j = I.bools j := by
  have hlt := slotIndices_lt X start w first last hp
  have hne : body.id ≠ n := by omega
  have hall : (slotIndices X.length start w first last).all (· < ([bitsOf X, bitsOf [slotFiller]].flatten).length) =
      true := by
    simp only [List.all_eq_true, decide_eq_true_eq, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.length_append, length_bitsOf, List.length_cons, List.length_nil]
    intro i hi
    have := hlt i hi
    omega
  let V : Bits := [bitsOf X, bitsOf [slotFiller]].flatten
  have hV : V = bitsOf (X ++ [slotFiller]) := by simp [V]
  let P : Bits := (slotIndices X.length start w first last).map (V.getD · false)
  let Wd : Bits := bitsOf (widthsOf w)
  let I1 : Ideal := I.setBool ⟨n⟩ (bitsOf [slotFiller])
  let I2 : Ideal := I1.setBool ⟨n + 1⟩ V
  let I3 : Ideal := I2.setBool ⟨n + 2⟩ P
  let I4 : Ideal := I3.setBool ⟨n + 3⟩ Wd
  let I5 : Ideal := I4.setBool ⟨n + 4⟩ (P ++ Wd)
  have s1 : plainStep E (.boolPublic ⟨n⟩ (bitsOf [slotFiller])) I = some I1 := plainStep_public E _ _ I
  have s2 : plainStep E (.concat ⟨n + 1⟩ [body, ⟨n⟩]) I1 = some I2 :=
    plainStep_concat E ⟨n + 1⟩ I1 [body, ⟨n⟩] [bitsOf X, bitsOf [slotFiller]] V (by
      simp only [List.mapM_cons, List.mapM_nil, I1, bools_set, if_neg hne, hb, if_true]; rfl) rfl
  have s3 : plainStep E (.pick ⟨n + 2⟩ ⟨n + 1⟩ (slotIndices X.length start w first last)) I2 = some I3 :=
    plainStep_pick E ⟨n + 2⟩ I2 ⟨n + 1⟩ _ V (by simp only [I2, bools_set, if_true]) hall
  have s4 : plainStep E (.boolPublic ⟨n + 3⟩ (bitsOf (widthsOf w))) I3 = some I4 := plainStep_public E _ _ I3
  have s5 : plainStep E (.concat ⟨n + 4⟩ [⟨n + 2⟩, ⟨n + 3⟩]) I4 = some I5 :=
    plainStep_concat E ⟨n + 4⟩ I4 [⟨n + 2⟩, ⟨n + 3⟩] [P, Wd] (P ++ Wd) (by
      simp only [List.mapM_cons, List.mapM_nil, I4, I3, bools_set, if_true, show n + 2 ≠ n + 3 by omega, if_false]
      rfl) (by simp)
  refine ⟨I5, ?_, ?_, ?_⟩
  · rw [slotInput, runPlain_step s1, runPlain_step s2, runPlain_step s3, runPlain_step s4, runPlain_step s5]
    rfl
  · simp only [I5, bools_set, if_true, Option.some.injEq]
    show (byteBits (cutPositions X.length start w first last)).map (V.getD · false) ++ Wd = _
    rw [hV, pick_bytes (X ++ [slotFiller]) _ (fun p hq => by
      have := cutPositions_lt X start w first last hp p hq
      simp; omega), cutPositions_map X start w first last hp, ← bitsOf_append]
  · intro j hj
    simp only [I5, I4, I3, I2, I1, bools_set]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-! ## The kernel on those bytes -/

theorem bytes_assignOf (L : B8) (s c : Nat) (h : s + c ≤ L.length) :
    (ByteCircuit.inputBytes s c).map (BVExpr.eval (assignOf L)) = (L.drop s).take c :=
  inputValue_assignOf L s c h

theorem take_merge (L : B8) (a b a' c : Nat) (h : a' = a + b) :
    (L.drop a).take b ++ (L.drop a').take c = (L.drop a).take (b + c) := by
  subst h
  rw [List.take_add, List.drop_drop]

theorem slotSize (o : Bool) : itemSize (TlsMpc.Signal.BundleSlots.slots o) =
    TlsMpc.Signal.BundleResponse.size (TlsMpc.Signal.BundleResponse.item (TlsMpc.Signal.BundleSlots.slots o)) := rfl

theorem slotBytes_length (X : B8) (start : Nat) (w : Widths) (first last : Bool)
    (hp : placedOk X.length start w first last = true) :
    (slotBytes X start w first last).length = 73 + (if first then 0 else 1) +
      TlsMpc.Signal.BundleResponse.size (TlsMpc.Signal.BundleResponse.item (TlsMpc.Signal.BundleSlots.slots (w.oneTime != 0))) +
      (if last then 0 else 1) + 2 := by
  obtain ⟨ok, h1, h2, _, _⟩ := placedOk_spec hp
  have fi : TlsMpc.Signal.BundleResponse.firstItem = 73 := rfl
  have hsz : itemSize w = TlsMpc.Signal.BundleResponse.size (TlsMpc.Signal.BundleResponse.item w) := rfl
  have hI : (TlsMpc.Signal.Establish.part X start (itemSize w)).length =
      TlsMpc.Signal.BundleResponse.size (TlsMpc.Signal.BundleResponse.item w) :=
    by rw [BundleItemWhole.part_length X _ _ (by omega), hsz]
  have hs := (BundleSlotWhole.spliced_layout TlsMpc.ByteAuth.concrete slotFiller w ok _ hI).1
  simp only [slotBytes, List.length_append, hs]
  rw [BundleItemWhole.part_length X 0 _ (by omega), BundleItemWhole.part_length X _ 2 (by omega)]
  cases first <;> cases last <;>
    simp only [Bool.false_eq_true, if_false, if_true, List.length_nil] <;>
    (try rw [BundleItemWhole.part_length X _ 1 (by omega)]) <;> (try rw [BundleItemWhole.part_length X _ 1 (by omega)]) <;>
    omega

open TlsMpc.HybridKernel (lookup) in
/-- **The kernel's named inputs on the script's bytes** are those of `bundleSlot_device`. -/
theorem slot_inputs (X : B8) (start : Nat) (w : Widths) (first last : Bool)
    (hp : placedOk X.length start w first last = true) :
    let get := fun name => (lookup (TlsMpc.BundleSlotKernel.slotInputs first last (w.oneTime != 0)) name).map
      (BVExpr.eval (assignOf (slotBytes X start w first last ++ widthsOf w)))
    (get "head" ++ get "before" ++ get "item" ++ get "after" ++ get "end" = slotBytes X start w first last) ∧
      get "widths" = BundleSlotWhole.widthBytes w := by
  have hl := slotBytes_length X start w first last hp
  generalize hL : slotBytes X start w first last ++ widthsOf w = L
  have hLl : L.length = (slotBytes X start w first last).length + 5 := by rw [← hL]; simp [widthsOf]
  have hpre : (L.drop 0).take (slotBytes X start w first last).length = slotBytes X start w first last := by
    rw [← hL]; simp
  have hw : (L.drop (slotBytes X start w first last).length).take 5 = BundleSlotWhole.widthBytes w := by
    rw [← hL]; simp [widthsOf]; rfl
  dsimp only
  have fi : TlsMpc.Signal.BundleResponse.firstItem = 73 := rfl
  cases first <;> cases last <;>
    simp only [TlsMpc.BundleSlotKernel.slotInputs, lookup, TlsMpc.HybridKernel.lookupFrom, List.append_assoc,
      List.cons_append, List.nil_append, Bool.false_eq_true, if_false, if_true, List.singleton_append,
      TlsMpc.HybridKernel.Shape.variables, fi] at hl ⊢ <;>
    simp (config := { decide := true }) only [beq_iff_eq, String.reduceEq, if_false, if_true, List.map_nil,
      List.append_nil, List.nil_append, Nat.zero_add] <;>
    (rw [bytes_assignOf L _ _ (by omega)]) <;> (try rw [bytes_assignOf L _ _ (by omega)]) <;>
    (try rw [bytes_assignOf L _ _ (by omega)]) <;> (try rw [bytes_assignOf L _ _ (by omega)]) <;>
    (try rw [bytes_assignOf L _ _ (by omega)]) <;> (try rw [bytes_assignOf L _ _ (by omega)]) <;>
    (refine ⟨?_, ?_⟩) <;>
    (try simp only [← List.append_assoc]) <;>
    (try simp (disch := omega) only [take_merge]) <;>
    first
      | (rw [← hpre]; congr 2; omega)
      | (rw [← hw]; congr 2; omega)

theorem placed_of (X : B8) (start : Nat) (w : Widths) (first last : Bool)
    (hp : placedOk X.length start w first last = true) :
    BundleItemWhole.Placed X.length first last start (TlsMpc.Signal.BundleResponse.size (TlsMpc.Signal.BundleResponse.item w)) := by
  obtain ⟨_, h1, h2, h3, h4⟩ := placedOk_spec hp
  exact ⟨h1, h2, h3, h4⟩

/-- The assignment of `bundle-slot`'s input variables to the bytes the script feeds it. -/
def slotAssign (X : B8) (start : Nat) (w : Widths) (first last : Bool) : BVExpr.Assignment :=
  assignOf (slotBytes X start w first last ++ widthsOf w)

open TlsMpc.ReceiveKernel (values) in
/-- **T4, the parse, true counts.** For the body `X` the server sent and the item placed at
`start` with its digit counts `w` (as `layout?` reads them off the opened flags), the kernel the
script runs outputs exactly `BundleResponse.device` on `X` at `start` with `w`
(`BundleSlotWhole.bundleSlot_device`, its two input hypotheses discharged by `slot_inputs`). -/
theorem parse_device (X : B8) (start : Nat) (w : Widths) (first last : Bool)
    (hp : placedOk X.length start w first last = true) :
    let out := TlsMpc.Signal.BundleResponse.device TlsMpc.ByteAuth.concrete X.length start w X
    values (TlsMpc.BundleSlotKernel.bundleSlot first last (w.oneTime != 0)) (slotAssign X start w first last) =
      [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 [], out.getD 4 [], out.getD 5 [], out.getD 6 [],
        out.getD 7 [], out.getD 8 [], out.getD 9 []] ++
      (if w.oneTime = 0 then [] else [out.getD 10 [], out.getD 11 []]) :=
  BundleSlotWhole.bundleSlot_device first last w (placedOk_spec hp).1 _ X start (placed_of X start w first last hp)
    (by have h := (slot_inputs X start w first last hp).1; dsimp only at h ⊢; exact h)
    (slot_inputs X start w first last hp).2

open TlsMpc.ReceiveKernel (values) in
/-- **T4, the parse, whatever counts the script was given.** Either `device` accepts the item with
those counts, they are the only ones it accepts, and the kernel's outputs are `device`'s; or every
output of the kernel (validity included) is zero: the device is refused and nothing of it is
released (`BundleSlotWhole.bundleSlot_parses_or_refuses`; a splice and declared counts that
disagree, the `inconsistent_width_*` combination, cannot be formed by the script). -/
theorem parse_parses_or_refuses (X : B8) (start : Nat) (w : Widths) (first last : Bool)
    (hp : placedOk X.length start w first last = true) :
    ((TlsMpc.Signal.BundleResponse.device TlsMpc.ByteAuth.concrete X.length start w X).getD 0 [] = [255] ∧
      (∀ w', (TlsMpc.Signal.BundleResponse.device TlsMpc.ByteAuth.concrete X.length start w' X).getD 0 [] = [255] →
        w' = w) ∧
      let out := TlsMpc.Signal.BundleResponse.device TlsMpc.ByteAuth.concrete X.length start w X
      values (TlsMpc.BundleSlotKernel.bundleSlot first last (w.oneTime != 0)) (slotAssign X start w first last) =
        [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 [], out.getD 4 [], out.getD 5 [], out.getD 6 [],
          out.getD 7 [], out.getD 8 [], out.getD 9 []] ++
        (if w.oneTime = 0 then [] else [out.getD 10 [], out.getD 11 []])) ∨
    (∀ field ∈ values (TlsMpc.BundleSlotKernel.bundleSlot first last (w.oneTime != 0)) (slotAssign X start w first last),
      ∀ byte ∈ field, byte = 0) :=
  BundleSlotWhole.bundleSlot_parses_or_refuses first last w (placedOk_spec hp).1 _ X start
    (placed_of X start w first last hp)
    (by have h := (slot_inputs X start w first last hp).1; dsimp only at h ⊢; exact h)
    (slot_inputs X start w first last hp).2

theorem slot_inWidth (X : B8) (start : Nat) (w : Widths) (first last : Bool)
    (hp : placedOk X.length start w first last = true) :
    (bitsOf (slotBytes X start w first last ++ widthsOf w)).length =
      (circuitOf (TlsMpc.BundleSlotKernel.bundleSlot first last (w.oneTime != 0))).inWidth := by
  have hl := slotBytes_length X start w first last hp
  have fi : TlsMpc.Signal.BundleResponse.firstItem = 73 := rfl
  simp only [length_bitsOf, List.length_append, circuitOf, kernelCircuit, kernelInBytes,
    TlsMpc.BundleSlotKernel.bundleSlot]
  cases first <;> cases last <;>
    simp [TlsMpc.BundleSlotKernel.slotInputs, TlsMpc.HybridKernel.Shape.variables, widthsOf, fi] at hl ⊢ <;> omega

/-- **T4, the parse, in the model.** With the circuit under `bundle-slot FIRST LAST ONETIME` the
Lean kernel's (T2), the six instructions from the held body leave in handle `n + 5` the bits of the
kernel's outputs on exactly the bytes of `parse_device` (so, by `parse_device` and
`parse_parses_or_refuses`, `device`'s fields or nothing). -/
theorem parse_fields (E : Env) (n : Nat) (body : BoolH) (X : B8) (start : Nat) (w : Widths) (first last : Bool)
    (I : Ideal) (hb : I.bools body.id = some (bitsOf X)) (hbn : body.id < n)
    (hp : placedOk X.length start w first last = true)
    (hc : E.circuits (slotName first last (w.oneTime != 0)) =
      some (circuitOf (TlsMpc.BundleSlotKernel.bundleSlot first last (w.oneTime != 0)))) :
    ∃ I', runPlain E (slotInput n body X.length start w first last ++
        [.run ⟨n + 5⟩ (slotName first last (w.oneTime != 0)) 1 ⟨n + 4⟩]) I = some I' ∧
      I'.bools (n + 5) = some (bitsOf (TlsMpc.ReceiveKernel.values
        (TlsMpc.BundleSlotKernel.bundleSlot first last (w.oneTime != 0)) (slotAssign X start w first last)).flatten) := by
  obtain ⟨I1, h1, h2, _⟩ := slotInput_value E n body X start w first last I hb hbn hp
  refine ⟨I1.setBool ⟨n + 5⟩ ((circuitOf (TlsMpc.BundleSlotKernel.bundleSlot first last (w.oneTime != 0))).eval
    (bitsOf (slotBytes X start w first last ++ widthsOf w))), ?_, ?_⟩
  · rw [runPlain_append_some h1, runPlain_step (plainStep_run E ⟨n + 5⟩ I1 _ _ ⟨n + 4⟩ _ hc h2
      (slot_inWidth X start w first last hp))]
    rfl
  · simp only [bools_set, if_true, circuitOf, kernelCircuit, bytesOf_bitsOf]
    rfl

end TlsMpc.Node.Flows.Refresh
