import TlsMpc.Node.Flows.CurveRunH

/-!
# Value-level disclosure of the masked quotient round (PROOF_GAPS F24, part)

Stage S11. `quotientMany_disclosure`: against ANY adversary, the adversary's view of
`quotientMany` (n masked quotients in one round: the agreements' last step in `agree`,
`offsetStepFast`, `agreeHinted`, `agreeAffine`) is a prefix of
[the masked denominators `z_j · m_j`, the zero flags], for the masks `m_j` the engines hold
(`m_j = m_H,j + m_D,j`, the honest party's uniform contribution plus whatever the adversary
input), and each flag is 1 exactly when its masked denominator is 0. This composes S10's
`Inversion.quotient_disclosure` over n copies; with `Inversion.inv_hides` / `mask_uniform`
each released `z_j · m_j` is uniform for `z_j ≠ 0`.
-/

namespace TlsMpc.Node.Flows.Curve

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs seqs_cons seqs_nil seqs_append Silent silent_prefix)
open TlsMpc.Node.Flows.Run
open TlsMpc.Node.Flows.Masks (setFields_block mapM_block mapM_append_vals mapM_flatMap_vals mapM_map_vals
  mapM_vals flatten_getD length_flatten_eq instanceAt_flatten getD_map_range map_getD_all flatten_map_singleton'
  runLocal_adds)
open TlsMpc.FieldDag (F modulus ofNat inverse)
open TlsMpc.FieldDag.V3 (FieldInverse quotient Program)

/-- `field-quotient` on n instances, any masks (`FieldDagV3.quotient_eval`). -/
theorem runProgram_quotient_any (n : Nat) (x z m : Nat → F) :
    runProgram quotient n ((List.range n).map fun j => [x j, z j]).flatten ((List.range n).map m) =
      some (((List.range n).map fun j => [if z j * m j = 0 then ofNat 0 else x j * m j * inverse (z j * m j),
          if z j * m j = 0 then ofNat 1 else ofNat 0]).flatten,
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
      some ([if z j * m j = 0 then ofNat 0 else x j * m j * inverse (z j * m j),
          if z j * m j = 0 then ofNat 1 else ofNat 0], [z j * m j]) := by
    intro j hj
    have hj' := List.mem_range.mp hj
    rw [instanceAt_flatten quotient.inputs _ hl j (by simpa using hj'), hvm,
      instanceAt_flatten quotient.masks _ hl1 j (by simpa using hj')]
    simp only [getD_map_range _ n j [] hj']
    rw [TlsMpc.FieldDag.V3.quotient_eval]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
  unfold runProgram
  rw [if_pos ⟨by rw [length_flatten_eq quotient.inputs _ hl]; simp, by simp [quotient]⟩, mapM_vals _ _ _ hev]
  simp only [Option.map_some, List.map_map, Function.comp_def]
  rw [flatten_map_singleton' (fun j => z j * m j)]

section Disclosure

variable (E : Env) (me : Party) (adv : Adversary)

/-- **T3 with values for n masked quotients** (F24, part). Against any adversary, from a state
where the pairs (handles below `f`) hold `x_j`, `z_j`: the adversary's view of `quotientMany` is a
prefix of [`z_j · m_j` for all j, then the flags `[z_j · m_j = 0]`], both labelled
`maskedDenominator`, for the masks `m_j` the engines hold. -/
theorem quotientMany_disclosure (hq : E.programs Inversion.quotientName = some quotient) (σ : Store) (I : Ideal)
    (vD : List Release) (f slot : Nat) (pairs : List (FieldH × FieldH)) (x z : Nat → F)
    (hx : ∀ j, j < pairs.length → I.fields (pairs.getD j (⟨0⟩, ⟨0⟩)).1.id = some (x j))
    (hz : ∀ j, j < pairs.length → I.fields (pairs.getD j (⟨0⟩, ⟨0⟩)).2.id = some (z j))
    (hlo : ∀ p ∈ pairs, p.1.id < f ∧ p.2.id < f) :
    ∃ mv : Nat → F, (withAdv E me adv (quotientMany f slot pairs) σ I vD).viewD <+:
      [⟨Label.maskedDenominator, .elems ((List.range pairs.length).map fun j => z j * mv j)⟩,
       ⟨Label.maskedDenominator, .elems ((List.range pairs.length).map fun j =>
          if z j * mv j = 0 then ofNat 1 else ofNat 0)⟩] := by
  by_cases h0 : pairs.length = 0
  · have hp : pairs = [] := List.length_eq_zero_iff.mp h0
    subst hp
    refine ⟨fun _ => 0, ?_⟩
    unfold quotientMany
    simp only [List.length_nil, ↓reduceIte]
    simp [withAdv]
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
  generalize pairs.length = n at hx hz h0 hlo' ⊢
  suffices key : ∃ va vb : List F, (withAdv E me adv (seqs (sharedBlock f n slot ++
      [.program Inversion.quotientName n
        ((List.range n).flatMap fun j => [(pairs.getD j (⟨0⟩, ⟨0⟩)).1, (pairs.getD j (⟨0⟩, ⟨0⟩)).2])
        (sharedOut f n) (quotOuts f n) Label.maskedDenominator])
      (openFieldThen (quotFlags f n) Label.maskedDenominator fun fl =>
        if fl.length = n then
          seqs (freeFs (sharedIns f n) ++ freeFs (quotFlags f n))
            (.done ((List.range n).map fun j => (quotResult f n j, fl.getD j 0 == ofNat 1)))
        else .abort "reply shape")) σ I vD).viewD <+:
      [⟨Label.maskedDenominator, .elems ((List.range n).map fun j => z j * (va.getD j 0 + vb.getD j 0))⟩,
       ⟨Label.maskedDenominator, .elems ((List.range n).map fun j =>
          if z j * (va.getD j 0 + vb.getD j 0) = 0 then ofNat 1 else ofNat 0)⟩] by
    obtain ⟨va, vb, h⟩ := key
    exact ⟨fun j => va.getD j 0 + vb.getD j 0, h⟩
  rw [sharedBlock, List.cons_append, seqs_cons, ← seqs_append, seqs_cons, seqs_nil]
  refine Inversion.viewD_fieldInput E me adv slot (hs f n) (hs (f + n) n) .elements false _ σ I vD _ (fun va vb ha hb => ?_)
  simp only [hs, List.length_map, List.length_range] at ha hb
  let I1 := (I.setFields (hs f n) va).setFields (hs (f + n) n) vb
  obtain ⟨a2, a3⟩ := setFields_hs I f n va ha
  obtain ⟨b2, b3⟩ := setFields_hs (I.setFields (hs f n) va) (f + n) n vb hb
  have i1a : ∀ i, i < n → I1.fields (f + i) = some (va.getD i 0) := fun i hi => by
    show ((I.setFields (hs f n) va).setFields (hs (f + n) n) vb).fields _ = _
    rw [b2 _ (Or.inl (by omega)), a3 i hi]
  have i1b : ∀ i, i < n → I1.fields (f + n + i) = some (vb.getD i 0) := fun i hi => b3 i hi
  have i1o : ∀ k, k < f → I1.fields k = I.fields k := fun k hk => by
    show ((I.setFields (hs f n) va).setFields (hs (f + n) n) vb).fields _ = _
    rw [b2 _ (Or.inl (by omega)), a2 _ (Or.inl hk)]
  let ts : List (FieldH × FieldH × FieldH) := (List.range n).map fun i => (⟨f + 2 * n + i⟩, ⟨f + i⟩, ⟨f + n + i⟩)
  have memts : ∀ t ∈ ts, ∃ i, i < n ∧ t = (⟨f + 2 * n + i⟩, ⟨f + i⟩, ⟨f + n + i⟩) := by
    intro t ht
    simp only [ts, List.mem_map, List.mem_range] at ht
    obtain ⟨i, hi, rfl⟩ := ht
    exact ⟨i, hi, rfl⟩
  refine viewD_locals E me adv _ σ _ _ (fun i hi => by
    simp only [List.mem_map] at hi
    obtain ⟨_, _, rfl⟩ := hi
    rfl) I1 vD (fun I2 h2 => ?_)
  obtain ⟨I2', g1, -, g3, g4⟩ := runLocal_adds E ts I1
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
  have hts : (List.range n).map (fun i => (.fieldAdd ⟨f + 2 * n + i⟩ ⟨f + i⟩ ⟨f + n + i⟩ : Instr)) =
      ts.map fun t => (.fieldAdd t.1 t.2.1 t.2.2 : Instr) := by
    simp only [ts, List.map_map]
    rfl
  have e2 : I2 = I2' := by
    rw [hts] at h2
    rw [g1] at h2
    exact (Option.some.inj h2).symm
  subst e2
  have i2s : ∀ i, i < n → I2.fields (f + 2 * n + i) = some (va.getD i 0 + vb.getD i 0) := by
    intro i hi
    rw [g3 (⟨f + 2 * n + i⟩, ⟨f + i⟩, ⟨f + n + i⟩) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩), i1a i hi,
      i1b i hi]
    rfl
  have i2o : ∀ k, k < f → I2.fields k = I.fields k := by
    intro k hk
    rw [g4 _ (fun t ht => by obtain ⟨i, hi, rfl⟩ := memts t ht; dsimp only; omega), i1o k hk]
  have hins : ((List.range n).flatMap (fun j => [(pairs.getD j (⟨0⟩, ⟨0⟩)).1, (pairs.getD j (⟨0⟩, ⟨0⟩)).2])).mapM
      (fun h => I2.fields h.id) = some ((List.range n).map fun j => [x j, z j]).flatten := by
    rw [TlsMpc.Node.Flows.Masks.flatten_map']
    apply mapM_flatMap_vals
    intro j hj
    have hj' := List.mem_range.mp hj
    obtain ⟨l1, l2⟩ := hlo' j hj'
    simp only [List.mapM_cons, List.mapM_nil, i2o _ l1, i2o _ l2, hx j hj', hz j hj']
    rfl
  have hmask : (sharedOut f n).mapM (fun h => I2.fields h.id) =
      some ((List.range n).map fun j => va.getD j 0 + vb.getD j 0) :=
    mapM_hs I2 (f + 2 * n) n _ (by simp) (fun i hi => by rw [i2s i hi, getD_map_range _ _ _ _ hi])
  have hrun := runProgram_quotient_any n x z (fun j => va.getD j 0 + vb.getD j 0)
  let vo := ((List.range n).map fun j => [if z j * (va.getD j 0 + vb.getD j 0) = 0 then ofNat 0
      else x j * (va.getD j 0 + vb.getD j 0) * inverse (z j * (va.getD j 0 + vb.getD j 0)),
    if z j * (va.getD j 0 + vb.getD j 0) = 0 then ofNat 1 else ofNat 0]).flatten
  have hvl : ∀ c ∈ (List.range n).map (fun j => [if z j * (va.getD j 0 + vb.getD j 0) = 0 then ofNat 0
      else x j * (va.getD j 0 + vb.getD j 0) * inverse (z j * (va.getD j 0 + vb.getD j 0)),
    if z j * (va.getD j 0 + vb.getD j 0) = 0 then ofNat 1 else ofNat 0]), c.length = 2 := by
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨j, -, rfl⟩ := hc
    rfl
  have hvol : vo.length = 2 * n := by
    rw [length_flatten_eq 2 _ hvl]
    simp [Nat.mul_comm]
  refine viewD_program E me adv _ _ _ _ _ _ _ σ I2 vD _ quotient _ _ vo _ hq hins hmask hrun
    (by rw [hvol]; simp [quotOuts, hs]) ?_
  obtain ⟨-, c3⟩ := setFields_hs I2 (f + 3 * n) (2 * n) vo hvol
  have hfl : (quotFlags f n).mapM (fun h => (I2.setFields (quotOuts f n) vo).fields h.id) =
      some ((List.range n).map fun j => if z j * (va.getD j 0 + vb.getD j 0) = 0 then ofNat 1 else ofNat 0) := by
    apply mapM_map_vals
    intro j hj
    have hj' := List.mem_range.mp hj
    show (I2.setFields (hs (f + 3 * n) (2 * n)) vo).fields (f + 3 * n + 2 * j + 1) = _
    rw [show f + 3 * n + 2 * j + 1 = f + 3 * n + (2 * j + 1) by omega, c3 (2 * j + 1) (by omega)]
    have := flatten_getD 2 _ j 1 (0 : F) hvl (by simpa using hj') (by decide)
    rw [show j * 2 + 1 = 2 * j + 1 by omega, getD_map_range _ _ _ _ hj'] at this
    rw [this]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
  refine viewD_openFieldThen E me adv _ _ _ σ _ _ _ [] hfl ?_
  split
  · exact silent_prefix E me adv _ (TlsMpc.Node.Flows.Run.silent_locals (Silent.done _) _ (fun i hi => by
      simp only [freeFs, List.mem_append, List.mem_map] at hi
      rcases hi with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl)) _ _ _ _
  · exact silent_prefix E me adv _ (Silent.abort _) _ _ _ _

end Disclosure

end TlsMpc.Node.Flows.Curve
