import TlsMpc.Node.Flows.CurveRunG

/-!
# Honest curve runs (continued): agreements from bit tables

Stage S11, PROOF_GAPS F22 (program hypotheses: `CurveRunB.lean`).

  * `agreeHinted_honest`: `edwards-bit-sum` (mask free) on the jobs that have a table (`liveJobs`),
    one quotient round, and the result assembled in job order (a job without a table, its
    coordinate was 0, gets the constant handle `f0`, which holds 0, and `zero = true`): the quotient
    handle of live job `i` holds `X_i · Z_i⁻¹` of its projective output.
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

/-- The jobs that have a table, with it (`agreeHinted`'s `live`). -/
def liveJobs (jobs : List HintedJob) : List (HintedJob × List FieldH) :=
  jobs.filterMap fun j => j.table.map fun t => (j, t)

/-- `agreeHinted`'s result in job order (its `assemble`). -/
def assembleH (f0 : Nat) (jobs : List HintedJob) (us : List (FieldH × Bool)) : List (FieldH × Bool) :=
  (jobs.foldl (fun (st : List (FieldH × Bool) × Nat) j =>
    match j.table with
    | some _ => (st.1 ++ [us.getD st.2 (⟨f0⟩, true)], st.2 + 1)
    | none => (st.1 ++ [(⟨f0⟩, true)], st.2)) ([], 0)).1

def liveD : HintedJob × List FieldH := (⟨[], none, ⟨0⟩⟩, [])

/-- The 1261 values of live job `i`'s `edwards-bit-sum` instance: its validity, the shared `ρ`, the
1008 table entries from 12 on, its 251 bits. -/
def hintedVals (I : Ideal) (e : HintedJob × List FieldH) (ρ : F) : List F :=
  [(I.fields e.1.valid.id).getD 0, ρ] ++ valsOf I ((e.2.drop 12).take 1008) ++ valsOf I e.1.bits

section Hinted

variable (E : Env)

/-- **F22, `agreeHinted` through `jointRun`.** For the live jobs (`liveJobs`: those with a table;
251 bit handles, 1024 table handles, the validity handle, all below `f0` and defined), slot `rho`
holding each party's contributions to `ρ`, slot `qslot` the quotient masks with nonzero sums,
`edwards-bit-sum` loaded and computing `f` (mask free), `field-quotient` loaded: both return
`assembleH f0 jobs us` (the quotient handles of the live jobs, in job order, with zero flags; the
constant handle `f0` for the others), stores unchanged; handle `f0` holds 0; live job `i`'s quotient
handle `fo + 2m + 3m + 2i` (`fo = f0 + 1 + 3m`) holds `X_i · Z_i⁻¹` of `f` on its values; nothing
below `f0` changes. -/
theorem agreeHinted_honest (hinv : FieldInverse) (pb : Program) (f : (Nat → F) → List F)
    (hP : E.programs bitSumName = some pb) (hC : Conv.Computes pb 1261 [.never, .never] f)
    (hq : E.programs Inversion.quotientName = some quotient)
    (σA σB : Store) (I : Ideal) (f0 rho qslot : Nat) (jobs : List HintedJob)
    (hjobs : ∀ i, i < (liveJobs jobs).length → ((liveJobs jobs).getD i liveD).1.bits.length = 251 ∧
      ((liveJobs jobs).getD i liveD).2.length = 1024)
    (hdef : ∀ i, i < (liveJobs jobs).length → ∀ h ∈ ((liveJobs jobs).getD i liveD).1.valid ::
      ((((liveJobs jobs).getD i liveD).2.drop 12).take 1008 ++ ((liveJobs jobs).getD i liveD).1.bits),
      h.id < f0 ∧ (I.fields h.id).isSome)
    (ρA ρB qA qB : Nat → F) (hrA : σA.elems rho = (List.range (liveJobs jobs).length).map ρA)
    (hrB : σB.elems rho = (List.range (liveJobs jobs).length).map ρB)
    (hqA : σA.elems qslot = (List.range (liveJobs jobs).length).map qA)
    (hqB : σB.elems qslot = (List.range (liveJobs jobs).length).map qB)
    (hqm : ∀ i, i < (liveJobs jobs).length → qA i + qB i ≠ 0) :
    ∃ (J : Ideal) (zf : Nat → Bool),
      JRet (jointRun E (agreeHinted f0 rho qslot jobs) (agreeHinted f0 rho qslot jobs) σA σB I)
        (assembleH f0 jobs ((List.range (liveJobs jobs).length).map fun i =>
          (quotResult (f0 + 1 + 3 * (liveJobs jobs).length + 2 * (liveJobs jobs).length) (liveJobs jobs).length i, zf i)))
        (assembleH f0 jobs ((List.range (liveJobs jobs).length).map fun i =>
          (quotResult (f0 + 1 + 3 * (liveJobs jobs).length + 2 * (liveJobs jobs).length) (liveJobs jobs).length i, zf i)))
        J σA σB ∧
      J.fields f0 = some (ofNat 0) ∧
      (∀ i, i < (liveJobs jobs).length →
        J.fields (f0 + 1 + 3 * (liveJobs jobs).length + 2 * (liveJobs jobs).length + 3 * (liveJobs jobs).length + 2 * i) =
          some ((f (fun k => (hintedVals I ((liveJobs jobs).getD i liveD) (ρA i + ρB i)).getD k 0)).getD 0 0 *
            inverse ((f (fun k => (hintedVals I ((liveJobs jobs).getD i liveD) (ρA i + ρB i)).getD k 0)).getD 1 0))) ∧
      (∀ k, k < f0 → J.fields k = I.fields k) := by
  have hall : (liveJobs jobs).all (fun e => e.1.bits.length == 251 && e.2.length == 1024) = true := by
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_getD liveD hx
    rw [(hjobs i hi).1, (hjobs i hi).2]
    rfl
  have hflat : ∀ g : (HintedJob × List FieldH) × Nat → List FieldH, (liveJobs jobs).zipIdx.flatMap g =
      (List.range (liveJobs jobs).length).flatMap (fun i => g ((liveJobs jobs).getD i liveD, i)) := by
    intro g
    rw [zipIdx_eq_range (liveJobs jobs) liveD, List.flatMap_map]
  let I1 := I.setField ⟨f0⟩ (ofNat 0)
  have i1o : ∀ k, k ≠ f0 → I1.fields k = I.fields k := fun k hk => by simp [I1, Ideal.setField, hk]
  have i10 : I1.fields f0 = some (ofNat 0) := by simp [I1, Ideal.setField]
  unfold agreeHinted
  simp only [show (jobs.filterMap fun j => j.table.map fun t => (j, t)) = liveJobs jobs from rfl, hall, if_true]
  rw [hflat]
  by_cases h0 : (liveJobs jobs).length = 0
  · refine ⟨I1, fun _ => false, ?_, i10, fun i hi => absurd hi (by omega), fun k hk => i1o k (by omega)⟩
    refine jret_locals E _ _ σA σB _ _ I1 σA σB [.fieldPublic ⟨f0⟩ (ofNat 0)] (fun i hi => by
      simp only [List.mem_singleton] at hi
      subst hi
      rfl) I I1 rfl ?_
    rw [if_pos h0]
    have e : (List.range (liveJobs jobs).length).map (fun i =>
        (quotResult (f0 + 1 + 3 * (liveJobs jobs).length + 2 * (liveJobs jobs).length) (liveJobs jobs).length i,
          (fun _ => false : Nat → Bool) i)) = [] := by rw [h0]; rfl
    rw [e]
    exact jret_done E _ _ σA σB I1
  rw [if_neg h0]
  generalize liveJobs jobs = live at hjobs hdef hrA hrB hqA hqB hqm h0 ⊢
  generalize live.length = m at hjobs hdef hrA hrB hqA hqB hqm h0 ⊢
  obtain ⟨I2, -, -, i2s, i2o, hk2⟩ := sharedBlock_run E (f0 + 1) m rho σA σB I1 ρA ρB hrA hrB
  have back : ∀ k, k < f0 → I2.fields k = I.fields k := by
    intro k hk
    rw [i2o _ (Or.inl (by omega)), i1o _ (by omega)]
  -- the inputs
  have hins : ((List.range m).flatMap (fun i => [(live.getD i liveD).1.valid, ⟨f0 + 1 + 2 * m + i⟩] ++
      ((live.getD i liveD).2.drop 12).take 1008 ++ (live.getD i liveD).1.bits)).mapM (fun h => I2.fields h.id) =
      some ((List.range m).map fun i => hintedVals I (live.getD i liveD) (ρA i + ρB i)).flatten := by
    rw [TlsMpc.Node.Flows.Masks.flatten_map']
    apply mapM_flatMap_vals
    intro i hi
    have hi' := List.mem_range.mp hi
    have hd : ∀ h ∈ (live.getD i liveD).1.valid :: ((((live.getD i liveD).2.drop 12).take 1008) ++
        (live.getD i liveD).1.bits), I2.fields h.id = I.fields h.id :=
      fun h hh => back _ (hdef i hi' h hh).1
    obtain ⟨vv, hvv⟩ := Option.isSome_iff_exists.mp (hdef i hi' _ (List.mem_cons_self ..)).2
    have e1 : I2.fields (live.getD i liveD).1.valid.id = some vv := by
      rw [hd _ (List.mem_cons_self ..), hvv]
    have e2 : I2.fields (f0 + 1 + 2 * m + i) = some (ρA i + ρB i) := i2s i hi'
    refine mapM_append_vals _ _ _ _ _ (mapM_append_vals _ _ _ _ _ ?_ ?_) ?_
    · simp only [List.mapM_cons, List.mapM_nil, e1, e2, hvv]
      rfl
    · rw [TlsMpc.Node.Flows.Masks.mapM_congr' _ (fun h => I.fields h.id) _
        (fun h hh => hd h (List.mem_cons_of_mem _ (List.mem_append_left _ hh)))]
      exact mapM_defined I _ (fun h hh => (hdef i hi' h (List.mem_cons_of_mem _ (List.mem_append_left _ hh))).2)
    · rw [TlsMpc.Node.Flows.Masks.mapM_congr' _ (fun h => I.fields h.id) _
        (fun h hh => hd h (List.mem_cons_of_mem _ (List.mem_append_right _ hh)))]
      exact mapM_defined I _ (fun h hh => (hdef i hi' h (List.mem_cons_of_mem _ (List.mem_append_right _ hh))).2)
  have hlen : ∀ i, i < m → (hintedVals I (live.getD i liveD) (ρA i + ρB i)).length = 1261 := by
    intro i hi
    obtain ⟨l1, l2⟩ := hjobs i hi
    simp only [hintedVals, valsOf, List.length_append, List.length_map, List.length_cons, List.length_nil,
      List.length_take, List.length_drop, l1, l2]
    omega
  obtain ⟨op, hrun⟩ := runProgram_live pb 1261 0 2 f (computesD_of_computes pb 1261 _ f hC) m
    (fun i => hintedVals I (live.getD i liveD) (ρA i + ρB i)) (fun _ => []) hlen (fun _ _ => rfl)
    (fun _ _ k hk => absurd hk (Nat.not_lt_zero k)) (fun i _ => live_of_computes pb 1261 _ f hC _)
  rw [TlsMpc.Node.Flows.Masks.flatten_map_nil] at hrun
  have hol : ∀ i, i < m → (f (fun k => (hintedVals I (live.getD i liveD) (ρA i + ρB i)).getD k 0)).length = 2 := by
    intro i hi
    exact (run_one_computes pb 1261 _ f hC _ (hlen i hi)).2
  let fo := f0 + 1 + 3 * m
  let g := fun i => f (fun k => (hintedVals I (live.getD i liveD) (ρA i + ρB i)).getD k 0)
  let vo := ((List.range m).map g).flatten
  have hvol : vo.length = m * 2 := by
    rw [length_flatten_eq 2 _ (by
      intro c hc
      simp only [List.mem_map, List.mem_range] at hc
      obtain ⟨i, hi, rfl⟩ := hc
      exact hol i hi)]
    simp
  let I3 := I2.setFields (hs fo (m * 2)) vo
  obtain ⟨c2, -⟩ := setFields_hs I2 fo (m * 2) vo hvol
  let L := sharedIns (f0 + 1) m ++ sharedOut (f0 + 1) m
  obtain ⟨I4, r1, r2⟩ := TlsMpc.Node.Flows.Convert.runLocal_freeFields E L I3
  have nf : ∀ k, (k ≤ f0 ∨ fo ≤ k) → ∀ h ∈ L, h.id ≠ k := by
    intro k hk h hh
    simp only [L, List.mem_append] at hh
    rcases hh with hh | hh
    · obtain ⟨i, hi, e⟩ := mem_hs hh
      rw [e]
      omega
    · obtain ⟨i, hi, e⟩ := mem_hs hh
      rw [e]
      omega
  have i4v : ∀ i t, i < m → t < 2 → I4.fields (fo + (i * 2 + t)) = some ((g i).getD t 0) := by
    intro i t hi ht
    rw [r2 _ (nf _ (Or.inr (by omega)))]
    exact outs_value I2 fo m 2 _ hol i t hi ht
  let pairs : List (FieldH × FieldH) := (List.range m).map fun i => (⟨fo + 2 * i⟩, ⟨fo + 2 * i + 1⟩)
  have hpl : pairs.length = m := by simp [pairs]
  have hpg : ∀ i, i < m → pairs.getD i (⟨0⟩, ⟨0⟩) = (⟨fo + 2 * i⟩, ⟨fo + 2 * i + 1⟩) :=
    fun i hi => getD_map_range _ _ _ _ hi
  obtain ⟨J, hJ, hJq, hJo⟩ := quotientMany_honest E hinv hq σA σB I4 (fo + 2 * m) qslot pairs
    (fun i => (g i).getD 0 0) (fun i => (g i).getD 1 0) qA qB
    (fun i hi => by
      rw [hpl] at hi
      rw [hpg i hi]
      have := i4v i 0 hi (by decide)
      rw [show fo + (i * 2 + 0) = fo + 2 * i by omega] at this
      exact this)
    (fun i hi => by
      rw [hpl] at hi
      rw [hpg i hi]
      have := i4v i 1 hi (by decide)
      rw [show fo + (i * 2 + 1) = fo + 2 * i + 1 by omega] at this
      exact this)
    (fun p hp => by
      simp only [pairs, List.mem_map, List.mem_range] at hp
      obtain ⟨i, hi, rfl⟩ := hp
      exact ⟨by dsimp only; omega, by dsimp only; omega⟩)
    (by rw [hpl, hqA]) (by rw [hpl, hqB]) (fun i hi => by rw [hpl] at hi; exact hqm i hi)
  rw [hpl] at hJ hJq hJo
  refine ⟨J, fun i => decide ((g i).getD 1 0 = 0), ?_, ?_, fun i hi => hJq i hi, fun k hk => ?_⟩
  · refine jret_locals E _ _ σA σB _ _ J σA σB [.fieldPublic ⟨f0⟩ (ofNat 0)] (fun i hi => by
      simp only [List.mem_singleton] at hi
      subst hi
      rfl) I I1 rfl ?_
    simp only [← seqs_append, seqs_cons, seqs_nil]
    refine hk2 _ _ _ _ J σA σB ?_
    refine jret_program E _ _ _ _ _ _ _ _ σA σB I2 pb _ [] vo op _ _ J σA σB hP hins rfl hrun
      (by rw [hvol]; simp [hs, Nat.mul_comm]) ?_
    refine jret_locals E _ _ σA σB _ _ J σA σB _ (freeFs_local _) _ I4 (by
      show runLocal E (L.map fun h => (.freeField h : Instr)) _ = _
      rw [show hs fo (2 * m) = hs fo (m * 2) by rw [Nat.mul_comm 2 m]]
      exact r1) ?_
    refine jret_bind E _ _ _ _ σA σB I4 _ _ J σA σB _ _ J σA σB hJ ?_
    exact jret_done E _ _ σA σB J
  · rw [hJo f0 (Or.inl (by omega)), r2 _ (nf _ (Or.inl (Nat.le_refl _))), c2 _ (Or.inl (by omega)),
      i2o _ (Or.inl (by omega)), i10]
  · rw [hJo k (Or.inl (by omega)), r2 _ (nf _ (Or.inl (by omega))), c2 _ (Or.inl (by omega)), back k hk]

end Hinted

end TlsMpc.Node.Flows.Curve
