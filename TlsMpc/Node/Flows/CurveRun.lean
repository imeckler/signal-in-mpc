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

/-! ## `X25519.inverse` is `FieldDag.inverse` -/

/-- Big-endian value of a bit list, from the accumulator `v`. -/
def bitsVal : Nat → List Bool → Nat
  | v, [] => v
  | v, b :: rest => bitsVal (2 * v + b.toNat) rest

theorem bitsVal_testBits (n : Nat) : ∀ (k v : Nat),
    bitsVal v ((List.range k).reverse.map (fun i => n.testBit i)) = v * 2 ^ k + n % 2 ^ k
  | 0, v => by simp [bitsVal, Nat.mod_one]
  | k + 1, v => by
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append, List.map_cons]
    show bitsVal (2 * v + (n.testBit k).toNat) _ = _
    rw [bitsVal_testBits n k, Nat.mod_pow_succ, Nat.toNat_testBit, Nat.pow_succ]
    generalize n % 2 ^ k = R
    generalize n / 2 ^ k % 2 = t
    generalize 2 ^ k = P
    rw [Nat.add_mul]
    ac_rfl

/-- `X25519.powBits` on the concrete field from the accumulator `x^v` is `x^(v ‖ bits)`. -/
theorem powBits_power (x : F) : ∀ (bits : List Bool) (v : Nat),
    X25519.powBits X25519.concrete x (TlsMpc.FieldDag.power x v) bits = TlsMpc.FieldDag.power x (bitsVal v bits)
  | [], _ => rfl
  | b :: rest, v => by
    have e : (if b = true then TlsMpc.FieldDag.power x v * TlsMpc.FieldDag.power x v * x
        else TlsMpc.FieldDag.power x v * TlsMpc.FieldDag.power x v) =
        TlsMpc.FieldDag.power x (2 * v + b.toNat) := by
      rw [← TlsMpc.FieldDag.V3.power_add, ← Nat.two_mul]
      cases b
      · rfl
      · show TlsMpc.FieldDag.power x (2 * v) * x = x * TlsMpc.FieldDag.power x (2 * v)
        exact Fin.mul_comm _ _
    show X25519.powBits X25519.concrete x (if b = true then TlsMpc.FieldDag.power x v * TlsMpc.FieldDag.power x v * x
        else TlsMpc.FieldDag.power x v * TlsMpc.FieldDag.power x v) rest = _
    rw [e]
    exact powBits_power x rest (2 * v + b.toNat)

theorem modulus_sub_two_lt : modulus - 2 < 2 ^ 255 :=
  Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt (Nat.two_pow_pos 255) (by decide))

/-- **`X25519.inverse` (square-and-multiply on the bits of p − 2) is `FieldDag.inverse`.** -/
theorem x25519_inverse_eq (x : F) : X25519.inverse X25519.concrete x = inverse x := by
  have hb : bitsVal 0 X25519.inverseBits = modulus - 2 := by
    rw [X25519.inverseBits, bitsVal_testBits (modulus - 2) 255 0, Nat.zero_mul, Nat.zero_add,
      Nat.mod_eq_of_lt modulus_sub_two_lt]
  show X25519.powBits X25519.concrete x (TlsMpc.FieldDag.power x 0) X25519.inverseBits = TlsMpc.FieldDag.power x (modulus - 2)
  rw [powBits_power, hb]

/-! ## X25519 agreements (`Curve.agree`) -/

/-- The 257 values of one `x25519-fast` instance (`ladderIns`): 0, 0, the 252 swap bits of steps
2 … 253 for `bits`, 0, 0, the point `u`. -/
def ladderVals (bits : Nat → Bool) (u : F) : List F :=
  [ofNat 0, ofNat 0] ++ (List.range 252).map (fun k => X25519.bitValue (X25519Fast.swapBitSpec bits (k + 2))) ++
    [ofNat 0, ofNat 0, u]

/-- The program's projective output `(x₂, z₂)` on those values. -/
def ladderOut (bits : Nat → Bool) (u : F) : X25519.Coordinates F :=
  X25519Fast.compute X25519.concrete (fun i => (ladderVals bits u).getD i 0) ((ladderVals bits u).getD 256 0)

theorem ladderVals_length (bits : Nat → Bool) (u : F) : (ladderVals bits u).length = 257 := by
  simp [ladderVals]

theorem ladderVals_swap (bits : Nat → Bool) (u : F) (t : Nat) (h2 : 2 ≤ t) (h3 : t ≤ 253) :
    (ladderVals bits u).getD t 0 = X25519.bitValue (X25519Fast.swapBitSpec bits t) := by
  unfold ladderVals
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
    List.getElem?_append_right (by simp; omega)]
  have ht : t - [ofNat 0, ofNat 0].length < 252 := by simp; omega
  rw [List.getElem?_map, List.getElem?_range ht]
  simp only [Option.map_some, Option.getD_some, List.length_cons, List.length_nil]
  rw [show t - (0 + 1 + 1) + 2 = t by omega]

theorem ladderVals_u (bits : Nat → Bool) (u : F) : (ladderVals bits u).getD 256 0 = u := by
  unfold ladderVals
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

/-- `x25519-fast`'s expressions evaluate to the concrete ladder's `(x₂, z₂)`. -/
theorem exprs_eval (i : Nat → F) :
    X25519Fast.exprs.map (TlsMpc.FieldDag.Expr.eval i) =
      [(X25519Fast.compute X25519.concrete i (i 256)).x2, (X25519Fast.compute X25519.concrete i (i 256)).z2] := by
  have hm := X25519Fast.compute_map (X25519.evaluationHom i) TlsMpc.FieldDag.Expr.input (.input 256)
  have e1 : (TlsMpc.FieldDag.Expr.eval i ∘ TlsMpc.FieldDag.Expr.input) = i := funext fun _ => rfl
  have e2 : TlsMpc.FieldDag.Expr.eval i (.input 256) = i 256 := rfl
  rw [e1, e2] at hm
  rw [← hm]
  rfl

theorem exprs_ladder (bits : Nat → Bool) (u : F) :
    X25519Fast.exprs.map (TlsMpc.FieldDag.Expr.eval fun i => (ladderVals bits u).getD i 0) =
      [(ladderOut bits u).x2, (ladderOut bits u).z2] := by
  unfold ladderOut
  rw [exprs_eval]

/-- **The RFC result is the quotient of the program's outputs** (`X25519Fast.spec_eq_quotient`, with
`x25519_inverse_eq`). -/
theorem ladderOut_spec (bits : Nat → Bool) (u : F) :
    (ladderOut bits u).x2 * inverse (ladderOut bits u).z2 = X25519.spec bits u := by
  have h := X25519Fast.spec_eq_quotient bits u (fun i => (ladderVals bits u).getD i 0)
    (fun t h2 h3 => ladderVals_swap bits u t h2 h3)
  unfold ladderOut
  rw [ladderVals_u, ← x25519_inverse_eq, h]

theorem mem_getD {α : Type} {l : List α} {a : α} (d : α) (h : a ∈ l) : ∃ j, j < l.length ∧ l.getD j d = a := by
  obtain ⟨j, hj, e⟩ := List.getElem_of_mem h
  exact ⟨j, hj, by simp [List.getD_eq_getElem?_getD, hj, e]⟩

theorem getD_mem {α : Type} {l : List α} (d : α) {j : Nat} (h : j < l.length) : l.getD j d ∈ l := by
  simp [List.getD_eq_getElem?_getD, h]

section Agree

variable (E : Env)

/-- **F22, `agree` through `jointRun`: n X25519 agreements.** Job `j`'s 252 swap-bit handles hold
the swap bits `swapBitSpec bits_j t` of steps `t = 2 … 253` (what `Convert.sharedBits` produces from
the XOR-shared scalar, with `X25519SwapBits`), its point handle holds `u_j`; every job handle lies
below `f0`; `x25519-fast` is loaded and computes its exported expressions (`Conv.Computes`, as for
`splitAgree_honest`); `field-quotient` is loaded; the parties' slot `slot` holds their mask
contributions with nonzero sums. Then both parties return the quotient handles (with some zero
flags), their stores are unchanged, handle `f0 + 1 + 2n + 3n + 2j` holds `X25519.spec bits_j u_j`
(RFC 7748), and nothing below `f0` changes. Hypotheses: `FieldInverse`, the two programs loaded,
the mask sums nonzero. -/
theorem agree_honest (hinv : FieldInverse) (px : TlsMpc.FieldDag.V3.Program)
    (hP : E.programs x25519Name = some px)
    (hPC : Conv.Computes px 257 [.never, .never] (fun i => X25519Fast.exprs.map (TlsMpc.FieldDag.Expr.eval i)))
    (hq : E.programs Inversion.quotientName = some quotient)
    (σA σB : Store) (I : Ideal) (f0 slot : Nat) (jobs : List (List FieldH × FieldH))
    (bits : Nat → Nat → Bool) (u mA mB : Nat → F)
    (hsw : ∀ j, j < jobs.length → (jobs.getD j ([], ⟨0⟩)).1.length = 252 ∧
      ∀ k, k < 252 → I.fields ((jobs.getD j ([], ⟨0⟩)).1.getD k ⟨0⟩).id =
        some (X25519.bitValue (X25519Fast.swapBitSpec (bits j) (k + 2))))
    (hu : ∀ j, j < jobs.length → I.fields (jobs.getD j ([], ⟨0⟩)).2.id = some (u j))
    (hlo : ∀ j, j < jobs.length → (∀ h ∈ (jobs.getD j ([], ⟨0⟩)).1, h.id < f0) ∧ (jobs.getD j ([], ⟨0⟩)).2.id < f0)
    (hA : σA.elems slot = (List.range jobs.length).map mA) (hB : σB.elems slot = (List.range jobs.length).map mB)
    (hm : ∀ j, j < jobs.length → mA j + mB j ≠ 0) :
    ∃ (J : Ideal) (zf : Nat → Bool), JRet (jointRun E (agree f0 slot jobs) (agree f0 slot jobs) σA σB I)
        ((List.range jobs.length).map fun j => (quotResult (f0 + 1 + 2 * jobs.length) jobs.length j, zf j))
        ((List.range jobs.length).map fun j => (quotResult (f0 + 1 + 2 * jobs.length) jobs.length j, zf j)) J σA σB ∧
      (∀ j, j < jobs.length →
        J.fields (f0 + 1 + 2 * jobs.length + 3 * jobs.length + 2 * j) = some (X25519.spec (bits j) (u j))) ∧
      (∀ k, k < f0 → J.fields k = I.fields k) := by
  by_cases h0 : jobs.length = 0
  · have hp : jobs = [] := List.length_eq_zero_iff.mp h0
    subst hp
    refine ⟨I, fun _ => false, ?_, fun j hj => by simp at hj, fun _ _ => rfl⟩
    unfold agree
    simp only [List.length_nil, ↓reduceIte, List.range_zero, List.map_nil]
    exact jret_done E _ _ σA σB I
  have hall : jobs.all (fun j => j.1.length == 252) = true := by
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_getD ([], ⟨0⟩) hx
    rw [(hsw j hj).1]
    rfl
  have hflat : jobs.flatMap (fun j => ladderIns ⟨f0⟩ j.1 j.2) =
      (List.range jobs.length).flatMap (fun j => ladderIns ⟨f0⟩ (jobs.getD j ([], ⟨0⟩)).1 (jobs.getD j ([], ⟨0⟩)).2) :=
    flatMap_getD jobs ([], ⟨0⟩) _
  unfold agree
  simp only [if_neg h0, hall, if_true]
  rw [hflat]
  generalize jobs.length = n at hsw hu hlo hA hB hm h0 ⊢
  -- the constant 0
  let I1 := I.setField ⟨f0⟩ (ofNat 0)
  have i1o : ∀ k, k ≠ f0 → I1.fields k = I.fields k := fun k hk => by simp [I1, Ideal.setField, hk]
  have i10 : I1.fields f0 = some (ofNat 0) := by simp [I1, Ideal.setField]
  -- the ladder inputs
  let chunks := (List.range n).map fun j => ladderVals (bits j) (u j)
  have hins : ((List.range n).flatMap (fun j => ladderIns ⟨f0⟩ (jobs.getD j ([], ⟨0⟩)).1 (jobs.getD j ([], ⟨0⟩)).2)).mapM
      (fun h => I1.fields h.id) = some chunks.flatten := by
    rw [TlsMpc.Node.Flows.Masks.flatten_map']
    apply mapM_flatMap_vals
    intro j hj
    have hj' := List.mem_range.mp hj
    obtain ⟨hl252, hv⟩ := hsw j hj'
    obtain ⟨lo1, lo2⟩ := hlo j hj'
    have hz : ([⟨f0⟩, ⟨f0⟩] : List FieldH).mapM (fun h => I1.fields h.id) = some [ofNat 0, ofNat 0] := by
      simp [List.mapM_cons, i10]
    have hsws : (jobs.getD j ([], ⟨0⟩)).1.mapM (fun h => I1.fields h.id) =
        some ((List.range 252).map fun k => X25519.bitValue (X25519Fast.swapBitSpec (bits j) (k + 2))) := by
      conv => lhs; rw [← map_getD_all (jobs.getD j ([], ⟨0⟩)).1 ⟨0⟩, hl252]
      apply mapM_map_vals
      intro k hk
      have hk' := List.mem_range.mp hk
      have hlt := lo1 _ (getD_mem ⟨0⟩ (by rw [hl252]; exact hk'))
      rw [i1o _ (by omega), hv k hk']
    have hu' : ([⟨f0⟩, ⟨f0⟩, (jobs.getD j ([], ⟨0⟩)).2] : List FieldH).mapM (fun h => I1.fields h.id) =
        some [ofNat 0, ofNat 0, u j] := by
      simp only [List.mapM_cons, List.mapM_nil, i10, i1o _ (Nat.ne_of_lt lo2), hu j hj']
      rfl
    exact mapM_append_vals _ _ _ _ _ (mapM_append_vals _ _ _ _ _ hz hsws) hu'
  -- the program
  let vo := ((List.range n).map fun j => [(ladderOut (bits j) (u j)).x2, (ladderOut (bits j) (u j)).z2]).flatten
  have hcl : ∀ c ∈ chunks, c.length = 257 := by
    intro c hc
    simp only [chunks, List.mem_map] at hc
    obtain ⟨j, -, rfl⟩ := hc
    exact ladderVals_length _ _
  have hrun0 := runProgram_chunks px 257 [.never, .never] _ hPC chunks hcl
  have hrun : runProgram px n chunks.flatten [] = some (vo, []) := by
    have e1 : chunks.length = n := by simp [chunks]
    have e2 : (chunks.map fun c => X25519Fast.exprs.map (TlsMpc.FieldDag.Expr.eval fun i => c.getD i 0)).flatten = vo := by
      simp only [chunks, vo, List.map_map, Function.comp_def, exprs_ladder]
    rw [e1, e2] at hrun0
    exact hrun0
  have hvl : ∀ c ∈ (List.range n).map (fun j => [(ladderOut (bits j) (u j)).x2, (ladderOut (bits j) (u j)).z2]),
      c.length = 2 := by
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨j, -, rfl⟩ := hc
    rfl
  have hvol : vo.length = 2 * n := by
    rw [length_flatten_eq 2 _ hvl]
    simp [Nat.mul_comm]
  let I2 := I1.setFields (hs (f0 + 1) (2 * n)) vo
  obtain ⟨c2, c3⟩ := setFields_hs I1 (f0 + 1) (2 * n) vo hvol
  let I3 := I2.dropField ⟨f0⟩
  have i3x : ∀ j, j < n → I3.fields (f0 + 1 + 2 * j) = some (ladderOut (bits j) (u j)).x2 := by
    intro j hj
    simp only [I3, Ideal.dropField, if_neg (show f0 + 1 + 2 * j ≠ f0 by omega)]
    show (I1.setFields (hs (f0 + 1) (2 * n)) vo).fields _ = _
    rw [c3 (2 * j) (by omega)]
    have := flatten_getD 2 _ j 0 (0 : F) hvl (by simpa using hj) (by decide)
    rw [show j * 2 + 0 = 2 * j by omega, getD_map_range _ _ _ _ hj] at this
    rw [this, List.getD_cons_zero]
  have i3z : ∀ j, j < n → I3.fields (f0 + 2 + 2 * j) = some (ladderOut (bits j) (u j)).z2 := by
    intro j hj
    simp only [I3, Ideal.dropField, if_neg (show f0 + 2 + 2 * j ≠ f0 by omega)]
    show (I1.setFields (hs (f0 + 1) (2 * n)) vo).fields _ = _
    rw [show f0 + 2 + 2 * j = f0 + 1 + (2 * j + 1) by omega, c3 (2 * j + 1) (by omega)]
    have := flatten_getD 2 _ j 1 (0 : F) hvl (by simpa using hj) (by decide)
    rw [show j * 2 + 1 = 2 * j + 1 by omega, getD_map_range _ _ _ _ hj] at this
    rw [this]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
  have i3o : ∀ k, k < f0 → I3.fields k = I.fields k := by
    intro k hk
    simp only [I3, Ideal.dropField, if_neg (show k ≠ f0 by omega)]
    show (I1.setFields (hs (f0 + 1) (2 * n)) vo).fields _ = _
    rw [c2 _ (Or.inl (by omega)), i1o _ (by omega)]
  -- the quotients
  let pairs : List (FieldH × FieldH) := (List.range n).map fun j => (⟨f0 + 1 + 2 * j⟩, ⟨f0 + 2 + 2 * j⟩)
  have hpl : pairs.length = n := by simp [pairs]
  have hpg : ∀ j, j < n → pairs.getD j (⟨0⟩, ⟨0⟩) = (⟨f0 + 1 + 2 * j⟩, ⟨f0 + 2 + 2 * j⟩) :=
    fun j hj => getD_map_range _ _ _ _ hj
  obtain ⟨J, hJ, hJq, hJo⟩ := quotientMany_honest E hinv hq σA σB I3 (f0 + 1 + 2 * n) slot pairs
    (fun j => (ladderOut (bits j) (u j)).x2) (fun j => (ladderOut (bits j) (u j)).z2) mA mB
    (fun j hj => by rw [hpl] at hj; rw [hpg j hj]; exact i3x j hj)
    (fun j hj => by rw [hpl] at hj; rw [hpg j hj]; exact i3z j hj)
    (fun p hp => by
      simp only [pairs, List.mem_map, List.mem_range] at hp
      obtain ⟨j, hj, rfl⟩ := hp
      exact ⟨by dsimp only; omega, by dsimp only; omega⟩)
    (by rw [hpl, hA]) (by rw [hpl, hB]) (fun j hj => by rw [hpl] at hj; exact hm j hj)
  rw [hpl] at hJ hJq hJo
  refine ⟨J, fun j => decide ((ladderOut (bits j) (u j)).z2 = 0), ?_, fun j hj => ?_, fun k hk => ?_⟩
  · show JRet (jointRun E (seqs [_] (seq _ (seqs [_] _))) (seqs [_] (seq _ (seqs [_] _))) σA σB I) _ _ _ _ _
    refine jret_locals E _ _ σA σB _ _ J σA σB [_] (fun i hi => by
      simp only [List.mem_singleton] at hi
      subst hi
      rfl) I I1 rfl ?_
    refine jret_program E _ _ _ _ _ _ _ _ σA σB I1 px _ [] vo [] _ _ J σA σB hP hins rfl hrun
      (by rw [hvol]; simp [hs]) ?_
    refine jret_locals E _ _ σA σB _ _ J σA σB [_] (fun i hi => by
      simp only [List.mem_singleton] at hi
      subst hi
      rfl) I2 I3 rfl ?_
    exact hJ
  · rw [hJq j hj, ladderOut_spec]
  · rw [hJo k (Or.inl (by omega)), i3o k hk]

end Agree

end TlsMpc.Node.Flows.Curve
