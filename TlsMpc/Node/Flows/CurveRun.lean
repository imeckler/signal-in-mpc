import TlsMpc.Node.Flows.CurveHonest
import TlsMpc.Node.Flows.ConvertRun

/-!
# Honest curve runs with n instances: the masked quotient of many pairs, X25519 agreements

Stage S11, PROOF_GAPS F22. Two honest parties through `jointRun` (`Engine/Model.lean`), with the
S10 tool `JRet` (`Flows/RunAgree.lean`). Ideal states are described pointwise (`Ideal.fields` is
a function), so no proof enumerates a block: every statement is "for every index below n".

  * `quotientMany_honest` (the block-level ideal-state lemma): n masked quotients in one round.
    With each pair's values `x_j`, `z_j` in the engines (handles below `f`), both parties' mask
    contributions in their store slot, every mask sum nonzero, and `field-quotient` loaded: both
    return `(quotResult f n j, z_j = 0)` for every `j`, their stores are unchanged, handle
    `f + 3n + 2j` holds `x_j · z_j⁻¹`, and nothing below `f` or from `f + 5n` on changes.
  * `x25519_inverse_eq`: `X25519.inverse` (square-and-multiply on the bits of p − 2) is
    `FieldDag.inverse` (in the main package; `proofs/` has the same theorem over `ZMod`).
  * `agree_honest`: n X25519 agreements (`Curve.agree`) on shared swap bits. With the swap-bit
    handles of job `j` holding `swapBitSpec bits_j t` (t = 2 … 253) and its point handle `u_j`,
    `x25519-fast` loaded and computing its expressions (`Conv.Computes`, the hypothesis form of
    `splitAgree_honest`): handle `f0 + 1 + 5n + 2j` holds `X25519.spec bits_j u_j`
    (`X25519Fast.spec_eq_quotient`).
-/

namespace TlsMpc.Node.Flows.Curve

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs seqs_cons seqs_nil seqs_append)
open TlsMpc.Node.Flows.Run
open TlsMpc.Node.Flows.Masks (setFields_block mapM_block mapM_append_vals mapM_flatMap_vals mapM_map_vals
  mapM_vals flatten_getD length_flatten_eq instanceAt_flatten getD_map_range map_getD_all flatten_map_singleton'
  runLocal_adds runProgram_chunks)
open TlsMpc.FieldDag (F modulus ofNat inverse)
open TlsMpc.FieldDag.V3 (FieldInverse quotient)

/-! ## Lists of handles -/

theorem mem_hs {h : FieldH} {a k : Nat} (hm : h ∈ hs a k) : ∃ i, i < k ∧ h.id = a + i := by
  simp only [hs, List.mem_map, List.mem_range] at hm
  obtain ⟨i, hi, rfl⟩ := hm
  exact ⟨i, hi, rfl⟩

theorem mem_quotFlags {h : FieldH} {f n : Nat} (hm : h ∈ quotFlags f n) :
    ∃ j, j < n ∧ h.id = f + 3 * n + 2 * j + 1 := by
  simp only [quotFlags, List.mem_map, List.mem_range] at hm
  obtain ⟨j, hj, rfl⟩ := hm
  exact ⟨j, hj, rfl⟩

theorem flatMap_getD {α β : Type} (l : List α) (d : α) (g : α → List β) :
    l.flatMap g = (List.range l.length).flatMap (fun j => g (l.getD j d)) := by
  conv => lhs; rw [← map_getD_all l d]
  rw [List.flatMap_map]

theorem hs_eq (a k : Nat) : hs a k = (List.range k).map fun i => (⟨a + i⟩ : FieldH) := rfl

/-- A block `hs a k` set to `vs`: the values, and nothing else changes. -/
theorem setFields_hs (I : Ideal) (a k : Nat) (vs : List F) (hl : vs.length = k) :
    (∀ j, (j < a ∨ a + k ≤ j) → (I.setFields (hs a k) vs).fields j = I.fields j) ∧
    (∀ i, i < k → (I.setFields (hs a k) vs).fields (a + i) = some (vs.getD i 0)) := by
  obtain ⟨-, h2, h3⟩ := setFields_block I (fun i => (⟨a + i⟩ : FieldH)) a k vs (fun _ _ => rfl) hl
  exact ⟨h2, h3⟩

theorem mapM_hs (J : Ideal) (a k : Nat) (vs : List F) (hl : vs.length = k)
    (hJ : ∀ i, i < k → J.fields (a + i) = some (vs.getD i 0)) :
    (hs a k).mapM (fun h => J.fields h.id) = some vs :=
  mapM_block J (fun i => (⟨a + i⟩ : FieldH)) a k vs (fun _ _ => rfl) hl hJ

theorem freeFs_local (l : List FieldH) : ∀ i ∈ freeFs l, isLocal i = true := by
  intro i hi
  simp only [freeFs, List.mem_map] at hi
  obtain ⟨_, _, rfl⟩ := hi
  rfl

theorem freeFs_append (a b : List FieldH) : freeFs a ++ freeFs b = (a ++ b).map fun h => (.freeField h : Instr) := by
  simp [freeFs]

/-! ## `field-quotient` on n instances -/

/-- The zero flag of `field-quotient` (`FieldDagV3.quotient_spec`). -/
def zflag (z : F) : F := if z = 0 then ofNat 1 else ofNat 0

theorem zflag_beq (z : F) : (zflag z == ofNat 1) = decide (z = 0) := by
  unfold zflag
  by_cases h : z = 0 <;> simp [h] <;> decide

theorem runProgram_quotient (hinv : FieldInverse) (n : Nat) (x z m : Nat → F) (hm : ∀ j, j < n → m j ≠ 0) :
    runProgram quotient n ((List.range n).map fun j => [x j, z j]).flatten ((List.range n).map m) =
      some (((List.range n).map fun j => [x j * inverse (z j), zflag (z j)]).flatten,
        (List.range n).map fun j => z j * m j) := by
  have hl : ∀ c ∈ (List.range n).map (fun j => [x j, z j]), c.length = quotient.inputs := by
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨j, -, rfl⟩ := hc
    rfl
  have hl1 : ∀ c ∈ (List.range n).map (fun j => [m j]), c.length = quotient.masks := by
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨j, -, rfl⟩ := hc
    rfl
  have hvm : (List.range n).map m = ((List.range n).map fun j => [m j]).flatten := (flatten_map_singleton' m _).symm
  have hev : ∀ j ∈ List.range n,
      TlsMpc.FieldDag.V3.eval quotient (instanceAt ((List.range n).map fun j => [x j, z j]).flatten quotient.inputs j)
        (instanceAt ((List.range n).map m) quotient.masks j) =
      some ([x j * inverse (z j), zflag (z j)], [z j * m j]) := by
    intro j hj
    have hj' := List.mem_range.mp hj
    rw [instanceAt_flatten quotient.inputs _ hl j (by simpa using hj'), hvm,
      instanceAt_flatten quotient.masks _ hl1 j (by simpa using hj')]
    simp only [getD_map_range _ n j [] hj']
    rw [TlsMpc.FieldDag.V3.quotient_spec hinv _ _ (by simpa using hm j hj')]
    simp only [List.getD_cons_zero, List.getD_cons_succ, zflag]
  unfold runProgram
  rw [if_pos ⟨by rw [length_flatten_eq quotient.inputs _ hl]; simp, by simp [quotient]⟩,
    mapM_vals _ (fun j => ([x j * inverse (z j), zflag (z j)], [z j * m j])) _ hev]
  simp only [Option.map_some, List.map_map, Function.comp_def]
  rw [flatten_map_singleton' (fun j => z j * m j)]

/-! ## The block-level lemma: `quotientMany` -/

section Quotients

variable (E : Env)

/-- **`quotientMany` for two honest parties** (the block-level ideal-state lemma). For `n` pairs
whose handles lie below `f` and hold `x_j`, `z_j`; both parties' slot `slot` holding their `n`
mask contributions `mA_j`, `mB_j` with every sum nonzero (the honest masks: zero with probability
`n/p`); `field-quotient` loaded. Both parties return `(quotResult f n j, z_j = 0)` for `j < n`,
their stores are unchanged, `quotResult f n j` (handle `f + 3n + 2j`) holds `x_j · z_j⁻¹`
(`0` for `z_j = 0`), and every handle below `f` or from `f + 5n` on is as before. -/
theorem quotientMany_honest (hinv : FieldInverse) (hq : E.programs Inversion.quotientName = some quotient)
    (σA σB : Store) (I : Ideal) (f slot : Nat) (pairs : List (FieldH × FieldH)) (x z mA mB : Nat → F)
    (hx : ∀ j, j < pairs.length → I.fields (pairs.getD j (⟨0⟩, ⟨0⟩)).1.id = some (x j))
    (hz : ∀ j, j < pairs.length → I.fields (pairs.getD j (⟨0⟩, ⟨0⟩)).2.id = some (z j))
    (hlo : ∀ p ∈ pairs, p.1.id < f ∧ p.2.id < f)
    (hA : σA.elems slot = (List.range pairs.length).map mA) (hB : σB.elems slot = (List.range pairs.length).map mB)
    (hm : ∀ j, j < pairs.length → mA j + mB j ≠ 0) :
    ∃ J, JRet (jointRun E (quotientMany f slot pairs) (quotientMany f slot pairs) σA σB I)
        ((List.range pairs.length).map fun j => (quotResult f pairs.length j, decide (z j = 0)))
        ((List.range pairs.length).map fun j => (quotResult f pairs.length j, decide (z j = 0))) J σA σB ∧
      (∀ j, j < pairs.length → J.fields (f + 3 * pairs.length + 2 * j) = some (x j * inverse (z j))) ∧
      (∀ k, (k < f ∨ f + 5 * pairs.length ≤ k) → J.fields k = I.fields k) := by
  by_cases h0 : pairs.length = 0
  · have hp : pairs = [] := List.length_eq_zero_iff.mp h0
    subst hp
    refine ⟨I, ?_, fun j hj => by simp at hj, fun _ _ => rfl⟩
    unfold quotientMany
    simp only [List.length_nil, ↓reduceIte, List.range_zero, List.map_nil]
    exact jret_done E _ _ σA σB I
  have hflat : pairs.flatMap (fun p => [p.1, p.2]) =
      (List.range pairs.length).flatMap (fun j => [(pairs.getD j (⟨0⟩, ⟨0⟩)).1, (pairs.getD j (⟨0⟩, ⟨0⟩)).2]) :=
    flatMap_getD pairs (⟨0⟩, ⟨0⟩) _
  have hlo' : ∀ j, j < pairs.length → (pairs.getD j (⟨0⟩, ⟨0⟩)).1.id < f ∧ (pairs.getD j (⟨0⟩, ⟨0⟩)).2.id < f := by
    intro j hj
    apply hlo
    simp [List.getD_eq_getElem?_getD, hj]
  unfold quotientMany
  simp only [if_neg h0]
  rw [hflat]
  generalize pairs.length = n at hx hz hA hB hm h0 hlo' ⊢
  -- the inputs
  have hlA : (σA.elems slot).length = n := by rw [hA]; simp
  have hlB : (σB.elems slot).length = n := by rw [hB]; simp
  let I1 := (I.setFields (hs f n) ((List.range n).map mA)).setFields (hs (f + n) n) ((List.range n).map mB)
  have hI1 : bothFields .a I (hs f n) (hs (f + n) n) (σA.elems slot) (σB.elems slot) = I1 := by
    simp [bothFields, hA, hB, I1]
  obtain ⟨a2, a3⟩ := setFields_hs I f n ((List.range n).map mA) (by simp)
  obtain ⟨b2, b3⟩ := setFields_hs (I.setFields (hs f n) ((List.range n).map mA)) (f + n) n ((List.range n).map mB)
    (by simp)
  have i1a : ∀ i, i < n → I1.fields (f + i) = some (mA i) := by
    intro i hi
    show ((I.setFields (hs f n) _).setFields (hs (f + n) n) _).fields _ = _
    rw [b2 _ (Or.inl (by omega)), a3 i hi, getD_map_range _ _ _ _ hi]
  have i1b : ∀ i, i < n → I1.fields (f + n + i) = some (mB i) := by
    intro i hi
    show ((I.setFields (hs f n) _).setFields (hs (f + n) n) _).fields _ = _
    rw [b3 i hi, getD_map_range _ _ _ _ hi]
  have i1o : ∀ k, (k < f ∨ f + 2 * n ≤ k) → I1.fields k = I.fields k := by
    intro k hk
    show ((I.setFields (hs f n) _).setFields (hs (f + n) n) _).fields _ = _
    rw [b2 _ (by omega), a2 _ (by omega)]
  -- the mask sums
  let ts : List (FieldH × FieldH × FieldH) := (List.range n).map fun i => (⟨f + 2 * n + i⟩, ⟨f + i⟩, ⟨f + n + i⟩)
  have hts : (List.range n).map (fun i => (.fieldAdd ⟨f + 2 * n + i⟩ ⟨f + i⟩ ⟨f + n + i⟩ : Instr)) =
      ts.map fun t => (.fieldAdd t.1 t.2.1 t.2.2 : Instr) := by
    simp only [ts, List.map_map]
    rfl
  have memts : ∀ t ∈ ts, ∃ i, i < n ∧ t = (⟨f + 2 * n + i⟩, ⟨f + i⟩, ⟨f + n + i⟩) := by
    intro t ht
    simp only [ts, List.mem_map, List.mem_range] at ht
    obtain ⟨i, hi, rfl⟩ := ht
    exact ⟨i, hi, rfl⟩
  obtain ⟨I2, g1, -, g3, g4⟩ := runLocal_adds E ts I1
    (by
      have e : ts.map (·.1.id) = List.range' (f + 2 * n) n := by
        simp only [ts, List.map_map]
        rw [← TlsMpc.Node.Flows.Masks.map_range_add]
        rfl
      rw [e]
      exact List.nodup_range')
    (fun t ht t' ht' => by
      obtain ⟨i, hi, rfl⟩ := memts t ht
      obtain ⟨i', hi', rfl⟩ := memts t' ht'
      exact ⟨by dsimp only; omega, by dsimp only; omega⟩)
    (fun t ht => by
      obtain ⟨i, hi, rfl⟩ := memts t ht
      exact ⟨by rw [i1a i hi]; rfl, by rw [i1b i hi]; rfl⟩)
  have i2s : ∀ i, i < n → I2.fields (f + 2 * n + i) = some (mA i + mB i) := by
    intro i hi
    have := g3 (⟨f + 2 * n + i⟩, ⟨f + i⟩, ⟨f + n + i⟩) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    rw [this, i1a i hi, i1b i hi]
    rfl
  have i2o : ∀ k, (k < f + 2 * n ∨ f + 3 * n ≤ k) → I2.fields k = I1.fields k := by
    intro k hk
    apply g4
    intro t ht
    obtain ⟨i, hi, rfl⟩ := memts t ht
    dsimp only
    omega
  have hadd : runLocal E ((List.range n).map fun i => (.fieldAdd ⟨f + 2 * n + i⟩ ⟨f + i⟩ ⟨f + n + i⟩ : Instr)) I1 =
      some I2 := by rw [hts]; exact g1
  -- the program
  let vo := ((List.range n).map fun j => [x j * inverse (z j), zflag (z j)]).flatten
  have hvol : vo.length = 2 * n := by
    rw [length_flatten_eq 2 _ (by intro c hc; simp only [List.mem_map] at hc; obtain ⟨j, -, rfl⟩ := hc; rfl)]
    simp [Nat.mul_comm]
  have hins : ((List.range n).flatMap (fun j => [(pairs.getD j (⟨0⟩, ⟨0⟩)).1, (pairs.getD j (⟨0⟩, ⟨0⟩)).2])).mapM
      (fun h => I2.fields h.id) = some ((List.range n).map fun j => [x j, z j]).flatten := by
    rw [TlsMpc.Node.Flows.Masks.flatten_map']
    apply mapM_flatMap_vals
    intro j hj
    have hj' := List.mem_range.mp hj
    obtain ⟨l1, l2⟩ := hlo' j hj'
    have e1 : I2.fields (pairs.getD j (⟨0⟩, ⟨0⟩)).1.id = some (x j) := by
      rw [i2o _ (Or.inl (by omega)), i1o _ (Or.inl l1), hx j hj']
    have e2 : I2.fields (pairs.getD j (⟨0⟩, ⟨0⟩)).2.id = some (z j) := by
      rw [i2o _ (Or.inl (by omega)), i1o _ (Or.inl l2), hz j hj']
    simp only [List.mapM_cons, List.mapM_nil, e1, e2]
    rfl
  have hmask : (sharedOut f n).mapM (fun h => I2.fields h.id) = some ((List.range n).map fun j => mA j + mB j) :=
    mapM_hs I2 (f + 2 * n) n _ (by simp) (fun i hi => by rw [i2s i hi, getD_map_range _ _ _ _ hi])
  have hrun := runProgram_quotient hinv n x z (fun j => mA j + mB j) hm
  let I3 := I2.setFields (quotOuts f n) vo
  obtain ⟨c2, c3⟩ := setFields_hs I2 (f + 3 * n) (2 * n) vo hvol
  have hvl : ∀ c ∈ (List.range n).map (fun j => [x j * inverse (z j), zflag (z j)]), c.length = 2 := by
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨j, -, rfl⟩ := hc
    rfl
  have i3q : ∀ j, j < n → I3.fields (f + 3 * n + 2 * j) = some (x j * inverse (z j)) := by
    intro j hj
    show (I2.setFields (hs (f + 3 * n) (2 * n)) vo).fields _ = _
    rw [c3 (2 * j) (by omega)]
    have := flatten_getD 2 _ j 0 (0 : F) hvl (by simpa using hj) (by decide)
    rw [show j * 2 + 0 = 2 * j by omega, getD_map_range _ _ _ _ hj] at this
    rw [this, List.getD_cons_zero]
  have i3f : ∀ j, j < n → I3.fields (f + 3 * n + 2 * j + 1) = some (zflag (z j)) := by
    intro j hj
    show (I2.setFields (hs (f + 3 * n) (2 * n)) vo).fields _ = _
    rw [show f + 3 * n + 2 * j + 1 = f + 3 * n + (2 * j + 1) by omega, c3 (2 * j + 1) (by omega)]
    have := flatten_getD 2 _ j 1 (0 : F) hvl (by simpa using hj) (by decide)
    rw [show j * 2 + 1 = 2 * j + 1 by omega, getD_map_range _ _ _ _ hj] at this
    rw [this]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
  have i3o : ∀ k, (k < f + 3 * n ∨ f + 5 * n ≤ k) → I3.fields k = I2.fields k := by
    intro k hk
    show (I2.setFields (hs (f + 3 * n) (2 * n)) vo).fields _ = _
    rw [c2 _ (by omega)]
  -- the flags
  let fl := (List.range n).map fun j => zflag (z j)
  have hfl : (quotFlags f n).mapM (fun h => I3.fields h.id) = some fl :=
    mapM_map_vals _ (quotFlag f n) (fun j => zflag (z j)) _ (fun j hj => i3f j (List.mem_range.mp hj))
  -- the frees
  obtain ⟨I4, r1, r2⟩ := TlsMpc.Node.Flows.Convert.runLocal_freeFields E (sharedIns f n ++ quotFlags f n) I3
  have notFreed : ∀ k, (k < f ∨ f + 2 * n ≤ k) → (∀ j, j < n → k ≠ f + 3 * n + 2 * j + 1) →
      ∀ h ∈ sharedIns f n ++ quotFlags f n, h.id ≠ k := by
    intro k hk hk' h hh
    rcases List.mem_append.mp hh with hh | hh
    · obtain ⟨i, hi, e⟩ := mem_hs hh
      rw [e]
      omega
    · obtain ⟨j, hj, e⟩ := mem_quotFlags hh
      rw [e]
      exact fun h' => hk' j hj h'.symm
  have hres : (List.range n).map (fun j => (quotResult f n j, fl.getD j 0 == ofNat 1)) =
      (List.range n).map fun j => (quotResult f n j, decide (z j = 0)) := by
    apply List.map_congr_left
    intro j hj
    rw [getD_map_range _ _ _ _ (List.mem_range.mp hj), zflag_beq]
  refine ⟨I4, ?_, fun j hj => ?_, fun k hk => ?_⟩
  · rw [sharedBlock, List.cons_append, seqs_cons, ← seqs_append, seqs_cons, seqs_nil]
    refine jret_fieldInput E _ _ _ _ _ _ _ _ σA σB I _ _ I4 σA σB (by simp [hs])
      (by rw [hlA]; simp [hs]) rfl (by rw [hlB]; simp [hs]) rfl ?_
    rw [hI1]
    refine jret_locals E _ _ σA σB _ _ I4 σA σB _ (fun i hi => by
      simp only [List.mem_map] at hi
      obtain ⟨_, _, rfl⟩ := hi
      rfl) I1 I2 hadd ?_
    refine jret_program E _ _ _ _ _ _ _ _ σA σB I2 quotient _ _ vo _ _ _ I4 σA σB hq hins hmask hrun
      (by rw [hvol]; simp [quotOuts, hs]) ?_
    refine jret_openFieldThen E _ _ _ _ σA σB I3 fl _ _ I4 σA σB hfl ?_
    rw [if_pos (by simp [fl]), freeFs_append]
    refine jret_locals E _ _ σA σB _ _ I4 σA σB _ (fun i hi => by
      simp only [List.mem_map] at hi
      obtain ⟨_, _, rfl⟩ := hi
      rfl) I3 I4 r1 ?_
    rw [hres]
    exact jret_done E _ _ σA σB I4
  · rw [r2 _ (notFreed _ (Or.inr (by omega)) (fun j' _ => by omega)), i3q j hj]
  · rw [r2 _ (notFreed _ (by omega) (fun j' hj' => by omega)), i3o _ (by omega), i2o _ (by omega),
      i1o _ (by omega)]

end Quotients

end TlsMpc.Node.Flows.Curve
