import TlsMpc.Node.Flows.CurveRunC

/-!
# Honest curve runs (continued): n-instance programs; signatures, torsion, affine agreements

Stage S11, PROOF_GAPS F22 (program hypotheses `ComputesD`, `Live`: `CurveRunB.lean`).

  * `runProgram_live`: `n` instances of a program computing `f`, each live on its input, with
    nonzero masks: the outputs are the instances' `f` values, concatenated.
  * `signatures_honest`: `edwards-signature-sum` on `n` jobs (two masks each): handle
    `f0 + 6n + 2j + t` holds output `t` of job `j`'s instance.
  * `torsion_honest`: `edwards-torsion-hinted` on `n` lifted points with both parties' torsion
    hints and the shared `r`: handle `f0 + 19n + 2j + t` holds output `t` of point `j`'s instance.
  * `agreeAffine_honest`: `edwards-affine-bit-sum` (mask free) on `m` jobs and one quotient round:
    handle `f0 + 1 + 3m + 2m + 3m + 2j` holds `X_j · Z_j⁻¹` of job `j`'s projective output.
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

/-! ## n instances -/

theorem live_of_computes (p : Program) (k : Nat) (marks : List TlsMpc.FieldDag.V3.OMark) (f : (Nat → F) → List F)
    (hC : Conv.Computes p k marks f) (input : Nat → F) : Live p input := by
  intro mask _
  rw [hC.2.2.2 input mask]
  rfl

/-- **`n` live instances**: the outputs are each instance's `f` value, in order. -/
theorem runProgram_live (p : Program) (k m o : Nat) (f : (Nat → F) → List F) (hC : ComputesD p k m o f) (n : Nat)
    (ci cm : Nat → List F) (hci : ∀ j, j < n → (ci j).length = k) (hcm : ∀ j, j < n → (cm j).length = m)
    (hnz : ∀ j, j < n → ∀ i, i < m → (cm j).getD i 0 ≠ 0)
    (hL : ∀ j, j < n → Live p (fun i => (ci j).getD i 0)) :
    ∃ opened, runProgram p n ((List.range n).map ci).flatten ((List.range n).map cm).flatten =
      some (((List.range n).map fun j => f (fun i => (ci j).getD i 0)).flatten, opened) := by
  obtain ⟨c1, c2, c3, c4⟩ := hC
  have hl : ∀ c ∈ (List.range n).map ci, c.length = p.inputs := by
    intro c hc
    simp only [List.mem_map, List.mem_range] at hc
    obtain ⟨j, hj, rfl⟩ := hc
    rw [hci j hj, c1]
  have hlm : ∀ c ∈ (List.range n).map cm, c.length = p.masks := by
    intro c hc
    simp only [List.mem_map, List.mem_range] at hc
    obtain ⟨j, hj, rfl⟩ := hc
    rw [hcm j hj, c2]
  let opOf := fun j => ((TlsMpc.FieldDag.V3.eval p (fun i => (ci j).getD i 0) (fun i => (cm j).getD i 0)).map
    Prod.snd).getD []
  have hev : ∀ j ∈ List.range n,
      TlsMpc.FieldDag.V3.eval p (instanceAt ((List.range n).map ci).flatten p.inputs j)
        (instanceAt ((List.range n).map cm).flatten p.masks j) = some (f (fun i => (ci j).getD i 0), opOf j) := by
    intro j hj
    have hj' := List.mem_range.mp hj
    rw [instanceAt_flatten p.inputs _ hl j (by simpa using hj'), instanceAt_flatten p.masks _ hlm j (by simpa using hj')]
    simp only [getD_map_range _ n j [] hj']
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp
      (hL j hj' (fun i => (cm j).getD i 0) (fun i hi => hnz j hj' i (by rw [← c2]; exact hi)))
    obtain ⟨outs, op⟩ := r
    have ho := c4 _ _ _ _ hr
    subst ho
    simp only [opOf, hr, Option.map_some, Option.getD_some]
  refine ⟨((List.range n).map opOf).flatten, ?_⟩
  unfold runProgram
  rw [if_pos ⟨by rw [length_flatten_eq p.inputs _ hl]; simp, by rw [length_flatten_eq p.masks _ hlm]; simp⟩,
    mapM_vals _ (fun j => (f (fun i => (ci j).getD i 0), opOf j)) _ hev]
  simp only [Option.map_some, List.map_map, Function.comp_def]

theorem flatMap_flatten {α β : Type} (n : Nat) (g : Nat → List α) (val : α → β) :
    ((List.range n).flatMap g).map val = ((List.range n).map fun j => (g j).map val).flatten := by
  rw [List.map_flatMap, TlsMpc.Node.Flows.Masks.flatten_map']

/-- The value of handle `fo + o·j + t` after `n` instances with `o` outputs each. -/
theorem outs_value (I : Ideal) (fo n o : Nat) (g : Nat → List F) (hg : ∀ j, j < n → (g j).length = o)
    (j t : Nat) (hj : j < n) (ht : t < o) :
    (I.setFields (hs fo (n * o)) ((List.range n).map g).flatten).fields (fo + (j * o + t)) = some ((g j).getD t 0) := by
  have hl : ∀ c ∈ (List.range n).map g, c.length = o := by
    intro c hc
    simp only [List.mem_map, List.mem_range] at hc
    obtain ⟨j, hj, rfl⟩ := hc
    exact hg j hj
  have hlen : ((List.range n).map g).flatten.length = n * o := by rw [length_flatten_eq o _ hl]; simp
  obtain ⟨-, c3⟩ := setFields_hs I fo (n * o) _ hlen
  rw [c3 _ (by
    have : j * o + t < (j + 1) * o := by rw [Nat.succ_mul]; omega
    exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ hj)),
    flatten_getD o _ j t 0 hl (by simpa using hj) ht, getD_map_range _ _ _ _ hj]

theorem zipIdx_eq_range {α : Type} (l : List α) (d : α) : l.zipIdx = (List.range l.length).map fun j => (l.getD j d, j) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]

/-- Values of a list of handles that are all defined. -/
def valsOf (J : Ideal) (l : List FieldH) : List F := l.map fun g => (J.fields g.id).getD 0

/-! ## Signatures -/

/-- The 2546 program inputs of one signature job (`signatures`): flip, the key's table, h, the
base table, s. -/
def sigIns (baseT : List FieldH) (job : List FieldH × List FieldH) : List FieldH :=
  job.2.take 1 ++ job.1 ++ (job.2.drop 1).take 256 ++ baseT.take 1012 ++ job.2.drop 257

section Sig

variable (E : Env)

/-- **F22, `signatures` through `jointRun`.** `n` jobs (each a key table of 1024 handles and 510
scalar handles), the base table (1024 handles), every handle below `f0` and defined;
`edwards-signature-sum` loaded (`ComputesD … f`, 2 masks, 2 outputs), live on every job's inputs;
the 2n mask contributions with nonzero sums. Both return the output handles, stores unchanged,
handle `f0 + 6n + (2j + t)` holds output `t` of job `j`'s instance (`f` on the job's input values),
nothing below `f0` changes. -/
theorem signatures_honest (ps : Program) (f : (Nat → F) → List F) (hP : E.programs signatureSumName = some ps)
    (hC : ComputesD ps 2546 2 2 f) (σA σB : Store) (I : Ideal) (f0 maskSlot : Nat) (baseT : List FieldH)
    (jobs : List (List FieldH × List FieldH))
    (hjobs : ∀ j, j < jobs.length → (jobs.getD j ([], [])).1.length = 1024 ∧ (jobs.getD j ([], [])).2.length = 510)
    (hbase : baseT.length = 1024)
    (hdef : ∀ j, j < jobs.length → ∀ h ∈ sigIns baseT (jobs.getD j ([], [])), h.id < f0 ∧ (I.fields h.id).isSome)
    (mA mB : Nat → F) (hA : σA.elems maskSlot = (List.range (2 * jobs.length)).map mA)
    (hB : σB.elems maskSlot = (List.range (2 * jobs.length)).map mB)
    (hm : ∀ i, i < 2 * jobs.length → mA i + mB i ≠ 0)
    (hL : ∀ j, j < jobs.length → Live ps (fun i => (valsOf I (sigIns baseT (jobs.getD j ([], [])))).getD i 0)) :
    ∃ J, JRet (jointRun E (signatures f0 maskSlot baseT jobs) (signatures f0 maskSlot baseT jobs) σA σB I)
        ((List.range jobs.length).map fun j => (⟨f0 + 6 * jobs.length + 2 * j⟩, ⟨f0 + 6 * jobs.length + 2 * j + 1⟩))
        ((List.range jobs.length).map fun j => (⟨f0 + 6 * jobs.length + 2 * j⟩, ⟨f0 + 6 * jobs.length + 2 * j + 1⟩))
        J σA σB ∧
      (∀ j t, j < jobs.length → t < 2 → J.fields (f0 + 6 * jobs.length + (j * 2 + t)) =
        some ((f (fun i => (valsOf I (sigIns baseT (jobs.getD j ([], [])))).getD i 0)).getD t 0)) ∧
      (∀ k, k < f0 → J.fields k = I.fields k) := by
  by_cases h0 : jobs.length = 0
  · have hp : jobs = [] := List.length_eq_zero_iff.mp h0
    subst hp
    refine ⟨I, ?_, fun j t hj => by simp at hj, fun _ _ => rfl⟩
    unfold signatures
    simp only [List.length_nil, ↓reduceIte, List.range_zero, List.map_nil]
    exact jret_done E _ _ σA σB I
  have hall : (jobs.all (fun j => j.1.length == 1024 && j.2.length == 510) && baseT.length == 1024) = true := by
    simp only [Bool.and_eq_true, List.all_eq_true]
    refine ⟨fun x hx => ?_, by rw [hbase]; rfl⟩
    obtain ⟨j, hj, rfl⟩ := mem_getD ([], []) hx
    rw [(hjobs j hj).1, (hjobs j hj).2]
    exact ⟨rfl, rfl⟩
  have hflat : jobs.flatMap (fun j => j.2.take 1 ++ j.1 ++ (j.2.drop 1).take 256 ++ baseT.take 1012 ++ j.2.drop 257) =
      (List.range jobs.length).flatMap (fun j => sigIns baseT (jobs.getD j ([], []))) :=
    flatMap_getD jobs ([], []) _
  unfold signatures
  simp only [if_neg h0, hall, if_true]
  rw [hflat]
  generalize jobs.length = n at hjobs hdef hA hB hm hL h0 ⊢
  obtain ⟨I1, -, -, i1s, i1o, hk1⟩ := sharedBlock_run E f0 (2 * n) maskSlot σA σB I mA mB hA hB
  -- inputs
  have hval : ∀ j, j < n → ∀ h ∈ sigIns baseT (jobs.getD j ([], [])), I1.fields h.id = I.fields h.id :=
    fun j hj h hh => i1o _ (Or.inl (hdef j hj h hh).1)
  have hins : ((List.range n).flatMap (fun j => sigIns baseT (jobs.getD j ([], []))) ).mapM (fun h => I1.fields h.id) =
      some ((List.range n).map fun j => valsOf I (sigIns baseT (jobs.getD j ([], [])))).flatten := by
    rw [TlsMpc.Node.Flows.Masks.flatten_map']
    apply mapM_flatMap_vals
    intro j hj
    have hj' := List.mem_range.mp hj
    rw [TlsMpc.Node.Flows.Masks.mapM_congr' _ (fun h => I.fields h.id) _ (hval j hj')]
    exact mapM_defined I _ (fun h hh => (hdef j hj' h hh).2)
  have hlen : ∀ j, j < n → (valsOf I (sigIns baseT (jobs.getD j ([], [])))).length = 2546 := by
    intro j hj
    obtain ⟨l1, l2⟩ := hjobs j hj
    simp only [valsOf, sigIns, List.length_map, List.length_append, List.length_take, List.length_drop, l1, l2, hbase]
    omega
  -- masks: two per job
  have hmv : ((List.range n).map fun j => (List.range 2).map fun i => mA (j * 2 + i) + mB (j * 2 + i)).flatten =
      (List.range (2 * n)).map fun i => mA i + mB i := by
    rw [TlsMpc.Node.Flows.Masks.flatten_map', flatMap_range_mul (fun i => mA i + mB i) 2 n, Nat.mul_comm]
  have hmask : (sharedOut f0 (2 * n)).mapM (fun h => I1.fields h.id) =
      some ((List.range n).map fun j => (List.range 2).map fun i => mA (j * 2 + i) + mB (j * 2 + i)).flatten := by
    rw [hmv]
    exact mapM_hs I1 (f0 + 2 * (2 * n)) (2 * n) _ (by simp) (fun i hi => by rw [i1s i hi, getD_map_range _ _ _ _ hi])
  obtain ⟨op, hrun⟩ := runProgram_live ps 2546 2 2 f hC n (fun j => valsOf I (sigIns baseT (jobs.getD j ([], []))))
    (fun j => (List.range 2).map fun i => mA (j * 2 + i) + mB (j * 2 + i)) hlen (fun j _ => by simp)
    (fun j hj i hi => by
      rw [getD_map_range _ _ _ _ hi]
      exact hm _ (by
        have : j * 2 + i < (j + 1) * 2 := by rw [Nat.succ_mul]; omega
        have := Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right 2 hj)
        omega)) hL
  let vo := ((List.range n).map fun j => f (fun i => (valsOf I (sigIns baseT (jobs.getD j ([], []))) ).getD i 0)).flatten
  have hol : ∀ j, j < n → (f (fun i => (valsOf I (sigIns baseT (jobs.getD j ([], [])))).getD i 0)).length = 2 := by
    intro j hj
    obtain ⟨-, -, c3, c4⟩ := hC
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (hL j hj (fun _ => 1) (fun _ _ => by decide))
    obtain ⟨outs, opn⟩ := r
    have := c4 _ _ _ _ hr
    subst this
    rw [(TlsMpc.FieldDag.V3.eval_lengths ps _ _ _ _ hr).2, c3]
  have hvol : vo.length = n * 2 := by
    rw [length_flatten_eq 2 _ (by
      intro c hc
      simp only [List.mem_map, List.mem_range] at hc
      obtain ⟨j, hj, rfl⟩ := hc
      exact hol j hj)]
    simp
  let I2 := I1.setFields (hs (f0 + 6 * n) (n * 2)) vo
  obtain ⟨c2, -⟩ := setFields_hs I1 (f0 + 6 * n) (n * 2) vo hvol
  obtain ⟨I3, r1, r2⟩ := TlsMpc.Node.Flows.Convert.runLocal_freeFields E (sharedIns f0 (2 * n)) I2
  have nf : ∀ k, (k < f0 ∨ f0 + 4 * n ≤ k) → ∀ h ∈ sharedIns f0 (2 * n), h.id ≠ k := by
    intro k hk h hh
    obtain ⟨i, hi, e⟩ := mem_hs hh
    rw [e]
    omega
  refine ⟨I3, ?_, fun j t hj ht => ?_, fun k hk => ?_⟩
  · simp only [← seqs_append]
    refine hk1 _ _ _ _ I3 σA σB ?_
    rw [seqs_cons, seqs_nil]
    have hprog : (2 * n * 1 : Nat) = 2 * n := Nat.mul_one _
    refine jret_program E _ _ _ _ _ _ _ _ σA σB I1 ps _ _ vo op _ _ I3 σA σB hP hins hmask hrun
      (by rw [hvol]; simp [hs, Nat.mul_comm]) ?_
    refine jret_locals E _ _ σA σB _ _ I3 σA σB _ (freeFs_local _) _ I3 (by
      show runLocal E ((sharedIns f0 (2 * n)).map fun h => (.freeField h : Instr)) _ = _
      rw [show hs (f0 + 6 * n) (2 * n) = hs (f0 + 6 * n) (n * 2) by rw [Nat.mul_comm 2 n]]
      exact r1) ?_
    exact jret_done E _ _ σA σB I3
  · rw [r2 _ (nf _ (Or.inr (by omega)))]
    exact outs_value I1 (f0 + 6 * n) n 2 _ hol j t hj ht
  · rw [r2 _ (nf _ (Or.inl hk)), c2 _ (Or.inl (by omega)), i1o _ (Or.inl hk)]

end Sig

end TlsMpc.Node.Flows.Curve
