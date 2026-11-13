import TlsMpc.Node.Flows.CurveRunE

/-!
# Honest curve runs (continued): bit tables

Stage S11, PROOF_GAPS F22 (program hypotheses `ComputesD`, `Live`: `CurveRunB.lean`).

  * `tables_honest`: `edwards-bit-table` on `m` lifted points with both parties' hints (the local
    step's output) and the shared link masks; the 126 link checks per point open to zero (the
    honest hints are right: `EdwardsHinted.bitTable_sound` / `entries_sound`); the table handles
    `fo + 1150j + 126 + t` hold outputs `126 + t` of point `j`'s instance.
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

theorem hs_drop_take (a k d w : Nat) (h : d + w ≤ k) : ((hs a k).drop d).take w = hs (a + d) w := by
  apply List.ext_getElem
  · simp [hs]
    omega
  · intro i h1 h2
    simp [hs, Nat.add_assoc]

/-- The 380 values of point `j`'s `edwards-bit-table` instance: `x, y`, per window A's hint then
B's hint, the 126 link masks. -/
def tableVals (I : Ideal) (p : Lifted) (ha hb lk : Nat → F) (j : Nat) : List F :=
  [(I.fields p.x.id).getD 0, (I.fields p.y.id).getD 0] ++
    (List.range 63).flatMap (fun w => [ha (126 * j + 2 * w), ha (126 * j + 2 * w + 1), hb (126 * j + 2 * w),
      hb (126 * j + 2 * w + 1)]) ++
    (List.range 126).map (fun i => lk (126 * j + i))

section Tables

variable (E : Env)

/-- **F22, `tables` through `jointRun`.** `m` lifted points (`x`, `y` below `f0`, defined); slot
`hints` holds each party's `126m` hint values, `links` its `126m` link-mask contributions,
`masks` its `252m` mask contributions with nonzero sums; `edwards-bit-table` loaded (`ComputesD …
f`: 380 inputs, 252 masks, 1150 outputs), live on each point's values, and its 126 link checks
vanish there (`hck`: the honest hints are right). Both return, per point, its 1024 table handles
`fo + 1150j + 126 …` (`fo = f0 + 252m + 378m + 756m`), stores unchanged; handle
`fo + 1150j + 126 + t` holds output `126 + t` of point `j`'s instance; nothing below `f0` changes. -/
theorem tables_honest (pb : Program) (f : (Nat → F) → List F) (hP : E.programs bitTableName = some pb)
    (hC : ComputesD pb 380 252 1150 f) (σA σB : Store) (I : Ideal) (f0 : Nat) (s : TableSlots) (pts : List Lifted)
    (hpts : ∀ j, j < pts.length → (pts.getD j liftedD).x.id < f0 ∧ (pts.getD j liftedD).y.id < f0 ∧
      (I.fields (pts.getD j liftedD).x.id).isSome ∧ (I.fields (pts.getD j liftedD).y.id).isSome)
    (ha hb lA lB mA mB : Nat → F)
    (hhA : σA.elems s.hints = (List.range (126 * pts.length)).map ha)
    (hhB : σB.elems s.hints = (List.range (126 * pts.length)).map hb)
    (hlA : σA.elems s.links = (List.range (126 * pts.length)).map lA)
    (hlB : σB.elems s.links = (List.range (126 * pts.length)).map lB)
    (hmA : σA.elems s.masks = (List.range (252 * pts.length)).map mA)
    (hmB : σB.elems s.masks = (List.range (252 * pts.length)).map mB)
    (hm : ∀ i, i < 252 * pts.length → mA i + mB i ≠ 0)
    (hL : ∀ j, j < pts.length → Live pb (fun i => (tableVals I (pts.getD j liftedD) ha hb (fun i => lA i + lB i) j).getD i 0))
    (hck : ∀ j, j < pts.length → ∀ i, i < 126 →
      (f (fun i => (tableVals I (pts.getD j liftedD) ha hb (fun i => lA i + lB i) j).getD i 0)).getD i 0 = 0) :
    ∃ J, JRet (jointRun E (tables f0 s pts) (tables f0 s pts) σA σB I)
        ((List.range pts.length).map fun j =>
          hs (f0 + 252 * pts.length + 378 * pts.length + 756 * pts.length + 1150 * j + 126) 1024)
        ((List.range pts.length).map fun j =>
          hs (f0 + 252 * pts.length + 378 * pts.length + 756 * pts.length + 1150 * j + 126) 1024) J σA σB ∧
      (∀ j t, j < pts.length → t < 1024 →
        J.fields (f0 + 252 * pts.length + 378 * pts.length + 756 * pts.length + 1150 * j + 126 + t) =
          some ((f (fun i => (tableVals I (pts.getD j liftedD) ha hb (fun i => lA i + lB i) j).getD i 0)).getD
            (126 + t) 0)) ∧
      (∀ k, k < f0 → J.fields k = I.fields k) := by
  by_cases h0 : pts.length = 0
  · have hp : pts = [] := List.length_eq_zero_iff.mp h0
    subst hp
    refine ⟨I, ?_, fun j t hj => by simp at hj, fun _ _ => rfl⟩
    unfold tables
    simp only [List.length_nil, ↓reduceIte, List.range_zero, List.map_nil]
    exact jret_done E _ _ σA σB I
  have hflat : ∀ g : Lifted × Nat → List FieldH, pts.zipIdx.flatMap g =
      (List.range pts.length).flatMap (fun j => g (pts.getD j liftedD, j)) := by
    intro g
    rw [zipIdx_eq_range pts liftedD, List.flatMap_map]
  unfold tables
  simp only [if_neg h0]
  rw [hflat]
  generalize pts.length = m at hpts hhA hhB hlA hlB hmA hmB hm hL hck h0 ⊢
  -- the hints, the links, the masks
  obtain ⟨I1, i1a, i1b, i1o, hk1⟩ := inputs_run E f0 (126 * m) s.hints .elements σA σB I ha hb hhA hhB rfl rfl
  obtain ⟨I2, -, -, i2s, i2o, hk2⟩ := sharedBlock_run E (f0 + 252 * m) (126 * m) s.links σA σB I1 lA lB hlA hlB
  obtain ⟨I3, -, -, i3s, i3o, hk3⟩ := sharedBlock_run E (f0 + 252 * m + 378 * m) (252 * m) s.masks σA σB I2 mA mB
    hmA hmB
  have back : ∀ k, k < f0 + 252 * m → I3.fields k = I1.fields k := by
    intro k hk
    rw [i3o _ (Or.inl (by omega)), i2o _ (Or.inl hk)]
  -- the inputs
  have hins : ((List.range m).flatMap (fun j => [(pts.getD j liftedD).x, (pts.getD j liftedD).y] ++ hintRow f0 m j ++
      ((sharedOut (f0 + 252 * m) (126 * m)).drop (126 * j)).take 126)).mapM (fun h => I3.fields h.id) =
      some ((List.range m).map fun j => tableVals I (pts.getD j liftedD) ha hb (fun i => lA i + lB i) j).flatten := by
    rw [TlsMpc.Node.Flows.Masks.flatten_map']
    apply mapM_flatMap_vals
    intro j hj
    have hj' := List.mem_range.mp hj
    obtain ⟨lx, ly, sx, sy⟩ := hpts j hj'
    obtain ⟨vx, hvx⟩ := Option.isSome_iff_exists.mp sx
    obtain ⟨vy, hvy⟩ := Option.isSome_iff_exists.mp sy
    have e1 : I3.fields (pts.getD j liftedD).x.id = some vx := by rw [back _ (by omega), i1o _ (Or.inl lx), hvx]
    have e2 : I3.fields (pts.getD j liftedD).y.id = some vy := by rw [back _ (by omega), i1o _ (Or.inl ly), hvy]
    have hj126 : 126 * j + 126 ≤ 126 * m := by omega
    refine mapM_append_vals _ _ _ _ _ (mapM_append_vals _ _ _ _ _ ?_ ?_) ?_
    · simp only [List.mapM_cons, List.mapM_nil, e1, e2, hvx, hvy]
      rfl
    · unfold hintRow
      apply mapM_flatMap_vals
      intro w hw
      have hw' := List.mem_range.mp hw
      have q1 : I3.fields (f0 + 126 * j + 2 * w) = some (ha (126 * j + 2 * w)) := by
        rw [back _ (by omega), show f0 + 126 * j + 2 * w = f0 + (126 * j + 2 * w) by omega, i1a _ (by omega)]
      have q2 : I3.fields (f0 + 126 * j + 2 * w + 1) = some (ha (126 * j + 2 * w + 1)) := by
        rw [back _ (by omega), show f0 + 126 * j + 2 * w + 1 = f0 + (126 * j + 2 * w + 1) by omega, i1a _ (by omega)]
      have q3 : I3.fields (f0 + 126 * m + 126 * j + 2 * w) = some (hb (126 * j + 2 * w)) := by
        rw [back _ (by omega), show f0 + 126 * m + 126 * j + 2 * w = f0 + 126 * m + (126 * j + 2 * w) by omega,
          i1b _ (by omega)]
      have q4 : I3.fields (f0 + 126 * m + 126 * j + 2 * w + 1) = some (hb (126 * j + 2 * w + 1)) := by
        rw [back _ (by omega),
          show f0 + 126 * m + 126 * j + 2 * w + 1 = f0 + 126 * m + (126 * j + 2 * w + 1) by omega, i1b _ (by omega)]
      simp only [List.mapM_cons, List.mapM_nil, q1, q2, q3, q4]
      rfl
    · rw [show sharedOut (f0 + 252 * m) (126 * m) = hs (f0 + 252 * m + 2 * (126 * m)) (126 * m) from rfl,
        hs_drop_take _ _ _ _ hj126]
      exact mapM_hs I3 _ 126 _ (by simp) (fun i hi => by
        rw [i3o _ (Or.inl (by omega)), show f0 + 252 * m + 2 * (126 * m) + 126 * j + i =
          f0 + 252 * m + 2 * (126 * m) + (126 * j + i) by omega, i2s _ (by omega), getD_map_range _ _ _ _ hi])
  have hmask : (sharedOut (f0 + 252 * m + 378 * m) (252 * m)).mapM (fun h => I3.fields h.id) =
      some ((List.range m).map fun j => (List.range 252).map fun i => mA (j * 252 + i) + mB (j * 252 + i)).flatten := by
    rw [masks_flatten (fun i => mA i + mB i) m 252, Nat.mul_comm m 252]
    exact mapM_hs I3 _ (252 * m) _ (by simp) (fun i hi => by rw [i3s i hi, getD_map_range _ _ _ _ hi])
  have hlen : ∀ j, j < m → (tableVals I (pts.getD j liftedD) ha hb (fun i => lA i + lB i) j).length = 380 := by
    intro j _
    simp only [tableVals, List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_range,
      List.length_flatMap]
    rfl
  let g := fun j => f (fun i => (tableVals I (pts.getD j liftedD) ha hb (fun i => lA i + lB i) j).getD i 0)
  have hol : ∀ j, j < m → (g j).length = 1150 := by
    intro j hj
    obtain ⟨-, -, c3, c4⟩ := hC
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (hL j hj (fun _ => 1) (fun _ _ => by decide))
    obtain ⟨outs, opn⟩ := r
    have := c4 _ _ _ _ hr
    simp only [g]
    rw [← this, (TlsMpc.FieldDag.V3.eval_lengths pb _ _ _ _ hr).2, c3]
  obtain ⟨op, hrun⟩ := runProgram_live pb 380 252 1150 f hC m
    (fun j => tableVals I (pts.getD j liftedD) ha hb (fun i => lA i + lB i) j)
    (fun j => (List.range 252).map fun i => mA (j * 252 + i) + mB (j * 252 + i)) hlen (fun j _ => by simp)
    (fun j hj i hi => by
      rw [getD_map_range _ _ _ _ hi]
      exact hm _ (by have := mask_index j i m 252 hj hi; omega)) hL
  let fo := f0 + 252 * m + 378 * m + 756 * m
  let vo := ((List.range m).map g).flatten
  have hvol : vo.length = m * 1150 := by
    rw [length_flatten_eq 1150 _ (by
      intro c hc
      simp only [List.mem_map, List.mem_range] at hc
      obtain ⟨j, hj, rfl⟩ := hc
      exact hol j hj)]
    simp
  let I4 := I3.setFields (hs fo (m * 1150)) vo
  obtain ⟨c2, -⟩ := setFields_hs I3 fo (m * 1150) vo hvol
  have i4v : ∀ j t, j < m → t < 1150 → I4.fields (fo + (j * 1150 + t)) = some ((g j).getD t 0) :=
    fun j t hj ht => outs_value I3 fo m 1150 g hol j t hj ht
  -- the link checks
  let zs : List F := ((List.range m).map fun _ => (List.range 126).map fun _ => (0 : F)).flatten
  have hz : ((List.range m).flatMap fun j => hs (fo + 1150 * j) 126).mapM (fun h => I4.fields h.id) = some zs := by
    simp only [zs]
    rw [TlsMpc.Node.Flows.Masks.flatten_map']
    apply mapM_flatMap_vals
    intro j hj
    have hj' := List.mem_range.mp hj
    exact mapM_hs I4 _ 126 _ (by simp) (fun i hi => by
      rw [show fo + 1150 * j + i = fo + (j * 1150 + i) by omega, i4v j i hj' (by omega), getD_map_range _ _ _ _ hi]
      exact congrArg some (hck j hj' i hi))
  have hzok : zs.length = 126 * m ∧ allZero zs = true := by
    refine ⟨?_, ?_⟩
    · rw [length_flatten_eq 126 _ (by
        intro c hc
        simp only [List.mem_map, List.mem_range] at hc
        obtain ⟨j, -, rfl⟩ := hc
        simp)]
      simp [Nat.mul_comm]
    · simp only [allZero, List.all_eq_true, zs, List.mem_flatten, List.mem_map, List.mem_range]
      rintro x ⟨l, ⟨j, -, rfl⟩, hx⟩
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      rfl
  -- the frees
  let L := hs f0 (252 * m) ++ sharedIns (f0 + 252 * m) (126 * m) ++ sharedOut (f0 + 252 * m) (126 * m) ++
    sharedIns (f0 + 252 * m + 378 * m) (252 * m) ++ (List.range m).flatMap fun j => hs (fo + 1150 * j) 126
  obtain ⟨I5, r1, r2⟩ := TlsMpc.Node.Flows.Convert.runLocal_freeFields E L I4
  have nf : ∀ k, (k < f0 ∨ ∃ j t, j < m ∧ t < 1024 ∧ k = fo + 1150 * j + 126 + t) → ∀ h ∈ L, h.id ≠ k := by
    intro k hk h hh
    simp only [L, List.mem_append, List.mem_flatMap, List.mem_range] at hh
    rcases hh with (((hh | hh) | hh) | hh) | ⟨j', hj', hh⟩
    all_goals
      obtain ⟨i, hi, e⟩ := mem_hs hh
      rw [e]
      rcases hk with hk | ⟨j, t, hj, ht, rfl⟩ <;> omega
  refine ⟨I5, ?_, fun j t hj ht => ?_, fun k hk => ?_⟩
  · simp only [← seqs_append, seqs_cons, seqs_nil]
    refine hk1 _ _ _ _ I5 σA σB ?_
    refine hk2 _ _ _ _ I5 σA σB ?_
    refine hk3 _ _ _ _ I5 σA σB ?_
    refine jret_locals E _ _ σA σB _ _ I5 σA σB [.fieldCheck] (fun i hi => by
      simp only [List.mem_singleton] at hi
      subst hi
      rfl) I3 I3 rfl ?_
    refine jret_program E _ _ _ _ _ _ _ _ σA σB I3 pb _ _ vo op _ _ I5 σA σB hP hins hmask hrun
      (by rw [hvol]; simp [hs, Nat.mul_comm]) ?_
    rw [show hs fo (1150 * m) = hs fo (m * 1150) by rw [Nat.mul_comm 1150 m]]
    refine jret_openFieldThen E _ _ _ _ σA σB I4 zs _ _ I5 σA σB hz ?_
    rw [if_pos hzok]
    refine jret_locals E _ _ σA σB _ _ I5 σA σB _ (freeFs_local _) I4 I5 r1 ?_
    exact jret_done E _ _ σA σB I5
  · rw [r2 _ (nf _ (Or.inr ⟨j, t, hj, ht, rfl⟩)), show fo + 1150 * j + 126 + t = fo + (j * 1150 + (126 + t)) by omega,
      i4v j (126 + t) hj (by omega)]
  · rw [r2 _ (nf _ (Or.inl hk)), c2 _ (Or.inl (by omega)), back _ (by omega), i1o _ (Or.inl hk)]

end Tables

end TlsMpc.Node.Flows.Curve
