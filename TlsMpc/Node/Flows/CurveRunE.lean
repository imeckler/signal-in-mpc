import TlsMpc.Node.Flows.CurveRunD

/-!
# Honest curve runs (continued): torsion checks, agreements from affine powers

Stage S11, PROOF_GAPS F22 (program hypotheses `ComputesD`, `Live`: `CurveRunB.lean`).

  * `torsion_honest`: `edwards-torsion-hinted` on `n` lifted points, with both parties' torsion
    hints (the local step's output) and the shared `r`: handle `f0 + 19n + (2j + t)` holds output
    `t` of point `j`'s instance (`EdwardsHinted.torsionHinted_eval` gives its meaning).
  * `agreeAffine_honest`: `edwards-affine-bit-sum` (mask free) on `m` jobs, then one masked
    quotient round: the quotient handle of job `j` holds `X_j · Z_j⁻¹` of its projective output.
-/

namespace TlsMpc.Node.Flows.Curve

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs seqs_cons seqs_nil seqs_append)
open TlsMpc.Node.Flows.Run
open TlsMpc.Node.Flows.Masks (setFields_block mapM_block mapM_append_vals mapM_flatMap_vals mapM_map_vals
  mapM_vals flatten_getD length_flatten_eq instanceAt_flatten getD_map_range map_getD_all flatten_map_singleton'
  runLocal_adds runProgram_chunks flatMap_range_mul)
open TlsMpc.FieldDag (F modulus ofNat inverse)
open TlsMpc.FieldDag.V3 (FieldInverse quotient Program)

/-- The default lifted point (for `getD`). -/
def liftedD : Lifted := ⟨⟨0⟩, ⟨0⟩, ⟨0⟩, TlsMpc.Node.Local.Edwards.neutral, true⟩

theorem mask_index (j i n w : Nat) (hj : j < n) (hi : i < w) : j * w + i < n * w := by
  have : j * w + i < (j + 1) * w := by rw [Nat.succ_mul]; omega
  exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right w hj)

/-- `n` instances' masks, `w` each, as one block of sums. -/
theorem masks_flatten (s : Nat → F) (n w : Nat) :
    ((List.range n).map fun j => (List.range w).map fun i => s (j * w + i)).flatten = (List.range (n * w)).map s := by
  rw [TlsMpc.Node.Flows.Masks.flatten_map', flatMap_range_mul s w n]

section Torsion

variable (E : Env)

/-- The 7 values of point `j`'s torsion instance: its affine `x, y`, A's hint, B's hint, the
shared `r`. -/
def torsionVals (I : Ideal) (p : Lifted) (ha hb r : Nat → F) (j : Nat) : List F :=
  [(I.fields p.x.id).getD 0, (I.fields p.y.id).getD 0, ha (2 * j), ha (2 * j + 1), hb (2 * j), hb (2 * j + 1), r j]

/-- **F22, `torsion` through `jointRun`.** `n` lifted points (their `x`, `y` handles below `f0`,
defined); slot `hintSlot` holds each party's `2n` torsion-hint values (`torsionLocal`), slot `rSlot`
its `n` contributions to `r`, slot `maskSlot` its `4n` mask contributions with nonzero sums;
`edwards-torsion-hinted` loaded (`ComputesD … f`, 7 inputs, 4 masks, 2 outputs), live on each
point's values. Both return the output handles, stores unchanged; handle `f0 + 19n + (2j + t)`
holds output `t` of point `j`'s instance; nothing below `f0` changes. -/
theorem torsion_honest (pt : Program) (f : (Nat → F) → List F) (hP : E.programs torsionName = some pt)
    (hC : ComputesD pt 7 4 2 f) (σA σB : Store) (I : Ideal) (f0 hintSlot rSlot maskSlot : Nat) (pts : List Lifted)
    (hpts : ∀ j, j < pts.length → (pts.getD j liftedD).x.id < f0 ∧ (pts.getD j liftedD).y.id < f0 ∧
      (I.fields (pts.getD j liftedD).x.id).isSome ∧ (I.fields (pts.getD j liftedD).y.id).isSome)
    (ha hb rA rB mA mB : Nat → F)
    (hhA : σA.elems hintSlot = (List.range (2 * pts.length)).map ha)
    (hhB : σB.elems hintSlot = (List.range (2 * pts.length)).map hb)
    (hrA : σA.elems rSlot = (List.range pts.length).map rA) (hrB : σB.elems rSlot = (List.range pts.length).map rB)
    (hmA : σA.elems maskSlot = (List.range (4 * pts.length)).map mA)
    (hmB : σB.elems maskSlot = (List.range (4 * pts.length)).map mB)
    (hm : ∀ i, i < 4 * pts.length → mA i + mB i ≠ 0)
    (hL : ∀ j, j < pts.length → Live pt (fun i => (torsionVals I (pts.getD j liftedD) ha hb (fun j => rA j + rB j) j).getD i 0)) :
    ∃ J, JRet (jointRun E (torsion f0 hintSlot rSlot maskSlot pts) (torsion f0 hintSlot rSlot maskSlot pts) σA σB I)
        ((List.range pts.length).map fun j =>
          (⟨f0 + 4 * pts.length + 3 * pts.length + 12 * pts.length + 2 * j⟩,
           ⟨f0 + 4 * pts.length + 3 * pts.length + 12 * pts.length + 2 * j + 1⟩))
        ((List.range pts.length).map fun j =>
          (⟨f0 + 4 * pts.length + 3 * pts.length + 12 * pts.length + 2 * j⟩,
           ⟨f0 + 4 * pts.length + 3 * pts.length + 12 * pts.length + 2 * j + 1⟩)) J σA σB ∧
      (∀ j t, j < pts.length → t < 2 → J.fields (f0 + 4 * pts.length + 3 * pts.length + 12 * pts.length + (j * 2 + t)) =
        some ((f (fun i => (torsionVals I (pts.getD j liftedD) ha hb (fun j => rA j + rB j) j).getD i 0)).getD t 0)) ∧
      (∀ k, k < f0 → J.fields k = I.fields k) := by
  by_cases h0 : pts.length = 0
  · have hp : pts = [] := List.length_eq_zero_iff.mp h0
    subst hp
    refine ⟨I, ?_, fun j t hj => by simp at hj, fun _ _ => rfl⟩
    unfold torsion
    simp only [List.length_nil, ↓reduceIte, List.range_zero, List.map_nil]
    exact jret_done E _ _ σA σB I
  have hflat : ∀ g : Lifted × Nat → List FieldH, pts.zipIdx.flatMap g =
      (List.range pts.length).flatMap (fun j => g (pts.getD j liftedD, j)) := by
    intro g
    rw [zipIdx_eq_range pts liftedD, List.flatMap_map]
  unfold torsion
  simp only [if_neg h0]
  rw [hflat]
  generalize pts.length = n at hpts hhA hhB hrA hrB hmA hmB hm hL h0 ⊢
  -- the hints, r, the masks
  obtain ⟨I1, i1a, i1b, i1o, hk1⟩ := inputs_run E f0 (2 * n) hintSlot .elements σA σB I ha hb hhA hhB rfl rfl
  obtain ⟨I2, -, -, i2s, i2o, hk2⟩ := sharedBlock_run E (f0 + 4 * n) n rSlot σA σB I1 rA rB hrA hrB
  obtain ⟨I3, -, -, i3s, i3o, hk3⟩ := sharedBlock_run E (f0 + 4 * n + 3 * n) (4 * n) maskSlot σA σB I2 mA mB hmA hmB
  have back : ∀ k, k < f0 + 4 * n → I3.fields k = I1.fields k := by
    intro k hk
    rw [i3o _ (Or.inl (by omega)), i2o _ (Or.inl hk)]
  -- the inputs
  have hins : ((List.range n).flatMap (fun j => [(pts.getD j liftedD).x, (pts.getD j liftedD).y, ⟨f0 + 2 * j⟩,
      ⟨f0 + 2 * j + 1⟩, ⟨f0 + 2 * n + 2 * j⟩, ⟨f0 + 2 * n + 2 * j + 1⟩, ⟨f0 + 4 * n + 2 * n + j⟩])).mapM
      (fun h => I3.fields h.id) =
      some ((List.range n).map fun j => torsionVals I (pts.getD j liftedD) ha hb (fun j => rA j + rB j) j).flatten := by
    rw [TlsMpc.Node.Flows.Masks.flatten_map']
    apply mapM_flatMap_vals
    intro j hj
    have hj' := List.mem_range.mp hj
    obtain ⟨lx, ly, sx, sy⟩ := hpts j hj'
    obtain ⟨vx, hvx⟩ := Option.isSome_iff_exists.mp sx
    obtain ⟨vy, hvy⟩ := Option.isSome_iff_exists.mp sy
    have e1 : I3.fields (pts.getD j liftedD).x.id = some vx := by rw [back _ (by omega), i1o _ (Or.inl lx), hvx]
    have e2 : I3.fields (pts.getD j liftedD).y.id = some vy := by rw [back _ (by omega), i1o _ (Or.inl ly), hvy]
    have e3 : I3.fields (f0 + 2 * j) = some (ha (2 * j)) := by rw [back _ (by omega), i1a _ (by omega)]
    have e4 : I3.fields (f0 + 2 * j + 1) = some (ha (2 * j + 1)) := by
      rw [back _ (by omega), show f0 + 2 * j + 1 = f0 + (2 * j + 1) by omega, i1a _ (by omega)]
    have e5 : I3.fields (f0 + 2 * n + 2 * j) = some (hb (2 * j)) := by rw [back _ (by omega), i1b _ (by omega)]
    have e6 : I3.fields (f0 + 2 * n + 2 * j + 1) = some (hb (2 * j + 1)) := by
      rw [back _ (by omega), show f0 + 2 * n + 2 * j + 1 = f0 + 2 * n + (2 * j + 1) by omega, i1b _ (by omega)]
    have e7 : I3.fields (f0 + 4 * n + 2 * n + j) = some (rA j + rB j) := by
      rw [i3o _ (Or.inl (by omega)), i2s j hj']
    simp only [List.mapM_cons, List.mapM_nil, e1, e2, e3, e4, e5, e6, e7, torsionVals, hvx, hvy]
    rfl
  have hmask : (sharedOut (f0 + 4 * n + 3 * n) (4 * n)).mapM (fun h => I3.fields h.id) =
      some ((List.range n).map fun j => (List.range 4).map fun i => mA (j * 4 + i) + mB (j * 4 + i)).flatten := by
    rw [masks_flatten (fun i => mA i + mB i) n 4, Nat.mul_comm n 4]
    exact mapM_hs I3 _ (4 * n) _ (by simp) (fun i hi => by rw [i3s i hi, getD_map_range _ _ _ _ hi])
  have hol : ∀ j, j < n → (f (fun i => (torsionVals I (pts.getD j liftedD) ha hb (fun j => rA j + rB j) j).getD i 0)).length = 2 := by
    intro j hj
    obtain ⟨-, -, c3, c4⟩ := hC
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (hL j hj (fun _ => 1) (fun _ _ => by decide))
    obtain ⟨outs, opn⟩ := r
    have := c4 _ _ _ _ hr
    subst this
    rw [(TlsMpc.FieldDag.V3.eval_lengths pt _ _ _ _ hr).2, c3]
  obtain ⟨op, hrun⟩ := runProgram_live pt 7 4 2 f hC n
    (fun j => torsionVals I (pts.getD j liftedD) ha hb (fun j => rA j + rB j) j)
    (fun j => (List.range 4).map fun i => mA (j * 4 + i) + mB (j * 4 + i)) (fun j _ => rfl) (fun j _ => by simp)
    (fun j hj i hi => by
      rw [getD_map_range _ _ _ _ hi]
      exact hm _ (by have := mask_index j i n 4 hj hi; omega)) hL
  let fo := f0 + 4 * n + 3 * n + 12 * n
  let vo := ((List.range n).map fun j => f (fun i => (torsionVals I (pts.getD j liftedD) ha hb (fun j => rA j + rB j) j).getD i 0)).flatten
  have hvol : vo.length = n * 2 := by
    rw [length_flatten_eq 2 _ (by
      intro c hc
      simp only [List.mem_map, List.mem_range] at hc
      obtain ⟨j, hj, rfl⟩ := hc
      exact hol j hj)]
    simp
  let I4 := I3.setFields (hs fo (n * 2)) vo
  obtain ⟨c2, -⟩ := setFields_hs I3 fo (n * 2) vo hvol
  let L := hs f0 (4 * n) ++ sharedIns (f0 + 4 * n) n ++ sharedOut (f0 + 4 * n) n ++ sharedIns (f0 + 4 * n + 3 * n) (4 * n)
  obtain ⟨I5, r1, r2⟩ := TlsMpc.Node.Flows.Convert.runLocal_freeFields E L I4
  have nf : ∀ k, (k < f0 ∨ fo ≤ k) → ∀ h ∈ L, h.id ≠ k := by
    intro k hk h hh
    simp only [L, List.mem_append] at hh
    rcases hh with ((hh | hh) | hh) | hh <;>
    · obtain ⟨i, hi, e⟩ := mem_hs hh
      rw [e]
      omega
  refine ⟨I5, ?_, fun j t hj ht => ?_, fun k hk => ?_⟩
  · simp only [← seqs_append, seqs_cons, seqs_nil]
    refine hk1 _ _ _ _ I5 σA σB ?_
    refine hk2 _ _ _ _ I5 σA σB ?_
    refine hk3 _ _ _ _ I5 σA σB ?_
    refine jret_locals E _ _ σA σB _ _ I5 σA σB [.fieldCheck] (fun i hi => by
      simp only [List.mem_singleton] at hi
      subst hi
      rfl) I3 I3 rfl ?_
    refine jret_program E _ _ _ _ _ _ _ _ σA σB I3 pt _ _ vo op _ _ I5 σA σB hP hins hmask hrun
      (by rw [hvol]; simp [hs, Nat.mul_comm]) ?_
    refine jret_locals E _ _ σA σB _ _ I5 σA σB _ (freeFs_local _) _ I5 (by
      show runLocal E (L.map fun h => (.freeField h : Instr)) _ = _
      rw [show hs fo (2 * n) = hs fo (n * 2) by rw [Nat.mul_comm 2 n]]
      exact r1) ?_
    exact jret_done E _ _ σA σB I5
  · rw [r2 _ (nf _ (Or.inr (by omega)))]
    exact outs_value I3 fo n 2 _ hol j t hj ht
  · rw [r2 _ (nf _ (Or.inl hk)), c2 _ (Or.inl (by omega)), back _ (by omega), i1o _ (Or.inl hk)]

end Torsion

/-! ## Agreements from affine powers -/

/-- The 757 values of job `j`'s `edwards-affine-bit-sum` instance: 1, the shared `ρ_j`, its 252
affine powers (504 handles), its 251 bits. -/
def affineVals (I : Ideal) (job : List FieldH × List FieldH) (ρ : F) : List F :=
  [ofNat 1, ρ] ++ valsOf I job.2 ++ valsOf I job.1

section Affine

variable (E : Env)

/-- **F22, `agreeAffine` through `jointRun`.** `m` jobs (251 bit handles, 504 power handles, all
below `f0` and defined); slot `rho` holds each party's `m` contributions to `ρ`; slot `qslot` the
quotient masks with nonzero sums; `edwards-affine-bit-sum` loaded and computing `f` (mask free,
`Conv.Computes`); `field-quotient` loaded. Both return the quotient handles (with zero flags),
stores unchanged; job `j`'s quotient handle `fo + 2m + 3m + 2j` (`fo = f0 + 1 + 3m`) holds
`X_j · Z_j⁻¹` for `[X_j, Z_j] = f` of the job's values; nothing below `f0` changes. -/
theorem agreeAffine_honest (hinv : FieldInverse) (pa : Program) (f : (Nat → F) → List F)
    (hP : E.programs affineBitSumName = some pa) (hC : Conv.Computes pa 757 [.never, .never] f)
    (hq : E.programs Inversion.quotientName = some quotient)
    (σA σB : Store) (I : Ideal) (f0 rho qslot : Nat) (jobs : List (List FieldH × List FieldH))
    (hjobs : ∀ j, j < jobs.length → (jobs.getD j ([], [])).1.length = 251 ∧ (jobs.getD j ([], [])).2.length = 504)
    (hdef : ∀ j, j < jobs.length → ∀ h ∈ (jobs.getD j ([], [])).2 ++ (jobs.getD j ([], [])).1,
      h.id < f0 ∧ (I.fields h.id).isSome)
    (ρA ρB qA qB : Nat → F) (hrA : σA.elems rho = (List.range jobs.length).map ρA)
    (hrB : σB.elems rho = (List.range jobs.length).map ρB)
    (hqA : σA.elems qslot = (List.range jobs.length).map qA) (hqB : σB.elems qslot = (List.range jobs.length).map qB)
    (hqm : ∀ j, j < jobs.length → qA j + qB j ≠ 0) :
    ∃ (J : Ideal) (zf : Nat → Bool),
      JRet (jointRun E (agreeAffine f0 rho qslot jobs) (agreeAffine f0 rho qslot jobs) σA σB I)
        ((List.range jobs.length).map fun j =>
          (quotResult (f0 + 1 + 3 * jobs.length + 2 * jobs.length) jobs.length j, zf j))
        ((List.range jobs.length).map fun j =>
          (quotResult (f0 + 1 + 3 * jobs.length + 2 * jobs.length) jobs.length j, zf j)) J σA σB ∧
      (∀ j, j < jobs.length →
        J.fields (f0 + 1 + 3 * jobs.length + 2 * jobs.length + 3 * jobs.length + 2 * j) =
          some ((f (fun i => (affineVals I (jobs.getD j ([], [])) (ρA j + ρB j)).getD i 0)).getD 0 0 *
            inverse ((f (fun i => (affineVals I (jobs.getD j ([], [])) (ρA j + ρB j)).getD i 0)).getD 1 0))) ∧
      (∀ k, k < f0 → J.fields k = I.fields k) := by
  by_cases h0 : jobs.length = 0
  · have hp : jobs = [] := List.length_eq_zero_iff.mp h0
    subst hp
    refine ⟨I, fun _ => false, ?_, fun j hj => by simp at hj, fun _ _ => rfl⟩
    unfold agreeAffine
    simp only [List.length_nil, ↓reduceIte, List.range_zero, List.map_nil]
    exact jret_done E _ _ σA σB I
  have hall : jobs.all (fun j => j.1.length == 251 && j.2.length == 504) = true := by
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_getD ([], []) hx
    rw [(hjobs j hj).1, (hjobs j hj).2]
    rfl
  have hflat : ∀ g : (List FieldH × List FieldH) × Nat → List FieldH, jobs.zipIdx.flatMap g =
      (List.range jobs.length).flatMap (fun j => g (jobs.getD j ([], []), j)) := by
    intro g
    rw [zipIdx_eq_range jobs ([], []), List.flatMap_map]
  unfold agreeAffine
  simp only [if_neg h0, hall, if_true]
  rw [hflat]
  generalize jobs.length = m at hjobs hdef hrA hrB hqA hqB hqm h0 ⊢
  let I1 := I.setField ⟨f0⟩ (ofNat 1)
  have i1o : ∀ k, k ≠ f0 → I1.fields k = I.fields k := fun k hk => by simp [I1, Ideal.setField, hk]
  have i10 : I1.fields f0 = some (ofNat 1) := by simp [I1, Ideal.setField]
  obtain ⟨I2, -, -, i2s, i2o, hk2⟩ := sharedBlock_run E (f0 + 1) m rho σA σB I1 ρA ρB hrA hrB
  have back : ∀ k, k < f0 → I2.fields k = I.fields k := by
    intro k hk
    rw [i2o _ (Or.inl (by omega)), i1o _ (by omega)]
  -- the inputs
  have hins : ((List.range m).flatMap (fun j => [⟨f0⟩, ⟨f0 + 1 + 2 * m + j⟩] ++ (jobs.getD j ([], [])).2 ++
      (jobs.getD j ([], [])).1)).mapM (fun h => I2.fields h.id) =
      some ((List.range m).map fun j => affineVals I (jobs.getD j ([], [])) (ρA j + ρB j)).flatten := by
    rw [TlsMpc.Node.Flows.Masks.flatten_map']
    apply mapM_flatMap_vals
    intro j hj
    have hj' := List.mem_range.mp hj
    have e1 : I2.fields f0 = some (ofNat 1) := by rw [i2o _ (Or.inl (by omega)), i10]
    have e2 : I2.fields (f0 + 1 + 2 * m + j) = some (ρA j + ρB j) := i2s j hj'
    have hd : ∀ h ∈ (jobs.getD j ([], [])).2 ++ (jobs.getD j ([], [])).1, I2.fields h.id = I.fields h.id :=
      fun h hh => back _ (hdef j hj' h hh).1
    refine mapM_append_vals _ _ _ _ _ (mapM_append_vals _ _ _ _ _ ?_ ?_) ?_
    · simp only [List.mapM_cons, List.mapM_nil, e1, e2]
      rfl
    · rw [TlsMpc.Node.Flows.Masks.mapM_congr' _ (fun h => I.fields h.id) _ (fun h hh => hd h (List.mem_append_left _ hh))]
      exact mapM_defined I _ (fun h hh => (hdef j hj' h (List.mem_append_left _ hh)).2)
    · rw [TlsMpc.Node.Flows.Masks.mapM_congr' _ (fun h => I.fields h.id) _ (fun h hh => hd h (List.mem_append_right _ hh))]
      exact mapM_defined I _ (fun h hh => (hdef j hj' h (List.mem_append_right _ hh)).2)
  have hlen : ∀ j, j < m → (affineVals I (jobs.getD j ([], [])) (ρA j + ρB j)).length = 757 := by
    intro j hj
    obtain ⟨l1, l2⟩ := hjobs j hj
    simp only [affineVals, valsOf, List.length_append, List.length_map, List.length_cons, List.length_nil, l1, l2]
  obtain ⟨op, hrun⟩ := runProgram_live pa 757 0 2 f (computesD_of_computes pa 757 _ f hC) m
    (fun j => affineVals I (jobs.getD j ([], [])) (ρA j + ρB j)) (fun _ => []) hlen (fun _ _ => rfl)
    (fun _ _ i hi => absurd hi (Nat.not_lt_zero i)) (fun j _ => live_of_computes pa 757 _ f hC _)
  rw [TlsMpc.Node.Flows.Masks.flatten_map_nil] at hrun
  have hol : ∀ j, j < m → (f (fun i => (affineVals I (jobs.getD j ([], [])) (ρA j + ρB j)).getD i 0)).length = 2 := by
    intro j _
    exact (run_one_computes pa 757 _ f hC _ (hlen j (by assumption))).2
  let fo := f0 + 1 + 3 * m
  let g := fun j => f (fun i => (affineVals I (jobs.getD j ([], [])) (ρA j + ρB j)).getD i 0)
  let vo := ((List.range m).map g).flatten
  have hvol : vo.length = m * 2 := by
    rw [length_flatten_eq 2 _ (by
      intro c hc
      simp only [List.mem_map, List.mem_range] at hc
      obtain ⟨j, hj, rfl⟩ := hc
      exact hol j hj)]
    simp
  let I3 := I2.setFields (hs fo (m * 2)) vo
  obtain ⟨c2, -⟩ := setFields_hs I2 fo (m * 2) vo hvol
  let L := (⟨f0⟩ : FieldH) :: sharedIns (f0 + 1) m ++ sharedOut (f0 + 1) m
  obtain ⟨I4, r1, r2⟩ := TlsMpc.Node.Flows.Convert.runLocal_freeFields E L I3
  have nf : ∀ k, (k < f0 ∨ fo ≤ k) → ∀ h ∈ L, h.id ≠ k := by
    intro k hk h hh
    simp only [L, List.cons_append, List.mem_cons, List.mem_append] at hh
    rcases hh with rfl | hh | hh
    · dsimp only
      omega
    · obtain ⟨i, hi, e⟩ := mem_hs hh
      rw [e]
      omega
    · obtain ⟨i, hi, e⟩ := mem_hs hh
      rw [e]
      omega
  have i4v : ∀ j t, j < m → t < 2 → I4.fields (fo + (j * 2 + t)) = some ((g j).getD t 0) := by
    intro j t hj ht
    rw [r2 _ (nf _ (Or.inr (by omega)))]
    exact outs_value I2 fo m 2 _ hol j t hj ht
  let pairs : List (FieldH × FieldH) := (List.range m).map fun j => (⟨fo + 2 * j⟩, ⟨fo + 2 * j + 1⟩)
  have hpl : pairs.length = m := by simp [pairs]
  have hpg : ∀ j, j < m → pairs.getD j (⟨0⟩, ⟨0⟩) = (⟨fo + 2 * j⟩, ⟨fo + 2 * j + 1⟩) :=
    fun j hj => getD_map_range _ _ _ _ hj
  obtain ⟨J, hJ, hJq, hJo⟩ := quotientMany_honest E hinv hq σA σB I4 (fo + 2 * m) qslot pairs
    (fun j => (g j).getD 0 0) (fun j => (g j).getD 1 0) qA qB
    (fun j hj => by
      rw [hpl] at hj
      rw [hpg j hj]
      have := i4v j 0 hj (by decide)
      rw [show fo + (j * 2 + 0) = fo + 2 * j by omega] at this
      exact this)
    (fun j hj => by
      rw [hpl] at hj
      rw [hpg j hj]
      have := i4v j 1 hj (by decide)
      rw [show fo + (j * 2 + 1) = fo + 2 * j + 1 by omega] at this
      exact this)
    (fun p hp => by
      simp only [pairs, List.mem_map, List.mem_range] at hp
      obtain ⟨j, hj, rfl⟩ := hp
      exact ⟨by dsimp only; omega, by dsimp only; omega⟩)
    (by rw [hpl, hqA]) (by rw [hpl, hqB]) (fun j hj => by rw [hpl] at hj; exact hqm j hj)
  rw [hpl] at hJ hJq hJo
  refine ⟨J, fun j => decide ((g j).getD 1 0 = 0), ?_, fun j hj => hJq j hj, fun k hk => ?_⟩
  · simp only [← seqs_append, seqs_cons, seqs_nil]
    refine jret_locals E _ _ σA σB _ _ J σA σB [.fieldPublic ⟨f0⟩ (ofNat 1)] (fun i hi => by
      simp only [List.mem_singleton] at hi
      subst hi
      rfl) I I1 rfl ?_
    refine hk2 _ _ _ _ J σA σB ?_
    refine jret_program E _ _ _ _ _ _ _ _ σA σB I2 pa _ [] vo op _ _ J σA σB hP hins rfl hrun
      (by rw [hvol]; simp [hs, Nat.mul_comm]) ?_
    refine jret_locals E _ _ σA σB _ _ J σA σB _ (freeFs_local _) _ I4 (by
      show runLocal E (L.map fun h => (.freeField h : Instr)) _ = _
      rw [show hs fo (2 * m) = hs fo (m * 2) by rw [Nat.mul_comm 2 m]]
      exact r1) ?_
    exact hJ
  · rw [hJo k (Or.inl (by omega)), r2 _ (nf _ (Or.inl hk)), c2 _ (Or.inl (by omega)), back k hk]

end Affine

end TlsMpc.Node.Flows.Curve
