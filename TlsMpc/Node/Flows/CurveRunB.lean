import TlsMpc.Node.Flows.CurveRun
import TlsMpc.EdwardsAffine

/-!
# Honest curve runs (continued): blocks with masks, the offset agreement's step

Stage S11, PROOF_GAPS F22. Generic run lemmas for the blocks the curve scripts are made of, then
the per-message steps of the offset agreement through `jointRun`.

THE PROGRAM HYPOTHESES (named; no program is evaluated in a proof):
  * `ComputesD p k m o f`: `p` has `k` data inputs, `m` masks, `o` outputs, and every evaluation
    that returns gives the outputs `f input` (whatever the masks). For a program that is the V3
    translation of `compileAll es` (`FieldDagV3.ofArtifact`) this is `FieldDagV3.eval_compileAll`
    with `f input = es.map (Expr.eval input)`; for a mask-free program it follows from
    `Conv.Computes` (`computesD_of_computes`).
  * `Live p input`: on this input, every evaluation with nonzero masks returns (no `D` row opens
    zero). For a translated artifact: `FieldDagV3.eval_ofArtifact_some` from `DivisorsNonzero`
    (the honest denominators are nonzero: for the Edwards programs, completeness of the addition
    law, `proofs/` `edwards_complete`).

PROVED (standard axioms only):
  * blocks: `inputs_run` (both parties' field inputs), `sharedBlock_run` (inputs and their sums),
    `runProgram_one` (one instance), `mapM_defined`;
  * `offsetStep_honest`: two honest parties' `offsetStep` returns `(u, f0 + 387)` to both, with
    `u = montU (K₀ + τ·B)` (`ephemeralKey_spec`), and handle `f0 + 387` holds the program's output
    on the step's inputs (`stepIns`: the initial point, per window the entry its recoded digit
    names and the sign); `offsetStep_value`: for `edwards-offset-sum` (`EdwardsAffine.offsetSum`),
    that output is the Montgomery `u = (1 + y)/(1 − y)` of the sum of the initial point and the
    signed entries (`offsetSum_eval`), i.e. with `step_tableSum`, `u((k₀ + τ)·R)` when the table holds
    the multiples of R.
-/

namespace TlsMpc.Node.Flows.Curve

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs seqs_cons seqs_nil seqs_append)
open TlsMpc.Node.Flows.Run
open TlsMpc.Node.Flows.Masks (setFields_block mapM_block mapM_append_vals mapM_flatMap_vals mapM_map_vals
  mapM_vals flatten_getD length_flatten_eq instanceAt_flatten getD_map_range map_getD_all flatten_map_singleton'
  runLocal_adds runProgram_chunks)
open TlsMpc.FieldDag (F modulus ofNat inverse)
open TlsMpc.FieldDag.V3 (FieldInverse quotient Program)

/-! ## Program hypotheses -/

/-- `p` computes `f` on every evaluation that returns: `k` data inputs, `m` masks, `o` outputs. -/
def ComputesD (p : Program) (k m o : Nat) (f : (Nat → F) → List F) : Prop :=
  p.inputs = k ∧ p.masks = m ∧ p.outputs.length = o ∧
    ∀ input mask outs opened, TlsMpc.FieldDag.V3.eval p input mask = some (outs, opened) → outs = f input

/-- On `input`, every evaluation of `p` with nonzero masks returns (no `D` row opens zero). -/
def Live (p : Program) (input : Nat → F) : Prop :=
  ∀ mask : Nat → F, (∀ i, i < p.masks → mask i ≠ 0) → (TlsMpc.FieldDag.V3.eval p input mask).isSome

theorem computesD_of_computes (p : Program) (k : Nat) (marks : List TlsMpc.FieldDag.V3.OMark)
    (f : (Nat → F) → List F) (h : Conv.Computes p k marks f) :
    ComputesD p k 0 marks.length f := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, by rw [← h3, List.length_map], fun input mask outs opened he => ?_⟩
  rw [h4] at he
  exact (Prod.mk.inj (Option.some.inj he)).1.symm

/-! ## Lookups and single instances -/

theorem mapM_defined (J : Ideal) (l : List FieldH) (h : ∀ g ∈ l, (J.fields g.id).isSome) :
    l.mapM (fun g => J.fields g.id) = some (l.map fun g => (J.fields g.id).getD 0) := by
  apply mapM_vals
  intro g hg
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (h g hg)
  rw [hv]
  rfl

theorem instanceAt_zero (v : List F) (w : Nat) (hl : v.length = w) : instanceAt v w 0 = fun i => v.getD i 0 := by
  funext i
  unfold instanceAt
  split
  · simp
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

/-- One instance of a program on `vi`, masks `vm`. -/
theorem runProgram_one (p : Program) (vi vm o op : List F) (hi : vi.length = p.inputs) (hm : vm.length = p.masks)
    (he : TlsMpc.FieldDag.V3.eval p (fun i => vi.getD i 0) (fun i => vm.getD i 0) = some (o, op)) :
    runProgram p 1 vi vm = some (o, op) := by
  unfold runProgram
  rw [if_pos ⟨by rw [hi, Nat.one_mul], by rw [hm, Nat.one_mul]⟩]
  simp only [List.range_one, List.mapM_cons, List.mapM_nil]
  rw [instanceAt_zero vi _ hi, instanceAt_zero vm _ hm, he]
  simp

/-- The honest single instance: it returns, and its outputs are `f input`. -/
theorem run_one_live (p : Program) (k m o : Nat) (f : (Nat → F) → List F) (hC : ComputesD p k m o f)
    (vi vm : List F) (hi : vi.length = k) (hm : vm.length = m) (hvm : ∀ i, i < m → vm.getD i 0 ≠ 0)
    (hL : Live p (fun i => vi.getD i 0)) :
    ∃ op, runProgram p 1 vi vm = some (f (fun i => vi.getD i 0), op) ∧ (f (fun i => vi.getD i 0)).length = o := by
  obtain ⟨c1, c2, c3, c4⟩ := hC
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (hL (fun i => vm.getD i 0) (fun i hi => hvm i (by rw [← c2]; exact hi)))
  obtain ⟨outs, op⟩ := r
  have ho := c4 _ _ _ _ hr
  subst ho
  refine ⟨op, runProgram_one p vi vm _ op (by rw [hi, c1]) (by rw [hm, c2]) hr, ?_⟩
  rw [(TlsMpc.FieldDag.V3.eval_lengths p _ _ _ _ hr).2, c3]

/-! ## Blocks of both parties' inputs -/

section Blocks

variable (E : Env)

/-- **Both parties' field inputs** into `hs fa k` (A) and `hs (fa + k) k` (B), from their slot
holding `a 0 … a (k − 1)` and `b 0 … b (k − 1)` (coins when coins are asked): the handles hold
them, nothing else changes, and a joint run continues from that state. -/
theorem inputs_run (fa k slot : Nat) (kd : FieldIn) (σA σB : Store) (I : Ideal) (a b : Nat → F)
    (hA : σA.elems slot = (List.range k).map a) (hB : σB.elems slot = (List.range k).map b)
    (hcA : coinsOk kd ((List.range k).map a) = true) (hcB : coinsOk kd ((List.range k).map b) = true) :
    ∃ I', (∀ i, i < k → I'.fields (fa + i) = some (a i)) ∧ (∀ i, i < k → I'.fields (fa + k + i) = some (b i)) ∧
      (∀ j, (j < fa ∨ fa + 2 * k ≤ j) → I'.fields j = I.fields j) ∧
      ∀ {α β : Type} (tA : Script α) (tB : Script β) (x : α) (y : β) (J : Ideal) (sA sB : Store),
        JRet (jointRun E tA tB σA σB I') x y J sA sB →
        JRet (jointRun E (seq (.fieldInput (hs fa k) (hs (fa + k) k) kd false slot) tA)
          (seq (.fieldInput (hs fa k) (hs (fa + k) k) kd false slot) tB) σA σB I) x y J sA sB := by
  obtain ⟨a2, a3⟩ := setFields_hs I fa k ((List.range k).map a) (by simp)
  obtain ⟨b2, b3⟩ := setFields_hs (I.setFields (hs fa k) ((List.range k).map a)) (fa + k) k ((List.range k).map b)
    (by simp)
  refine ⟨(I.setFields (hs fa k) ((List.range k).map a)).setFields (hs (fa + k) k) ((List.range k).map b),
    fun i hi => ?_, fun i hi => ?_, fun j hj => ?_, ?_⟩
  · rw [b2 _ (Or.inl (by omega)), a3 i hi, getD_map_range _ _ _ _ hi]
  · rw [b3 i hi, getD_map_range _ _ _ _ hi]
  · rw [b2 _ (by omega), a2 _ (by omega)]
  · intro α β tA tB x y J sA sB h
    refine jret_fieldInput E _ _ _ _ _ _ _ _ σA σB I _ _ J sA sB (by simp [hs])
      (by rw [hA]; simp [hs]) (by rw [hA]; exact hcA) (by rw [hB]; simp [hs]) (by rw [hB]; exact hcB) ?_
    have e : bothFields .a I (hs fa k) (hs (fa + k) k) (σA.elems slot) (σB.elems slot) =
        (I.setFields (hs fa k) ((List.range k).map a)).setFields (hs (fa + k) k) ((List.range k).map b) := by
      simp [bothFields, hA, hB]
    rw [e]
    exact h

/-- **A shared block** (`sharedBlock f k slot`): both parties' `k` contributions and their sums
`f + 2k + i` (`a i + b i`); nothing outside `f … f + 3k − 1` changes. -/
theorem sharedBlock_run (f k slot : Nat) (σA σB : Store) (I : Ideal) (a b : Nat → F)
    (hA : σA.elems slot = (List.range k).map a) (hB : σB.elems slot = (List.range k).map b) :
    ∃ I', (∀ i, i < k → I'.fields (f + i) = some (a i)) ∧ (∀ i, i < k → I'.fields (f + k + i) = some (b i)) ∧
      (∀ i, i < k → I'.fields (f + 2 * k + i) = some (a i + b i)) ∧
      (∀ j, (j < f ∨ f + 3 * k ≤ j) → I'.fields j = I.fields j) ∧
      ∀ {α β : Type} (tA : Script α) (tB : Script β) (x : α) (y : β) (J : Ideal) (sA sB : Store),
        JRet (jointRun E tA tB σA σB I') x y J sA sB →
        JRet (jointRun E (seqs (sharedBlock f k slot) tA) (seqs (sharedBlock f k slot) tB) σA σB I) x y J sA sB := by
  obtain ⟨I1, i1a, i1b, i1o, hk1⟩ := inputs_run E f k slot .elements σA σB I a b hA hB rfl rfl
  let ts : List (FieldH × FieldH × FieldH) := (List.range k).map fun i => (⟨f + 2 * k + i⟩, ⟨f + i⟩, ⟨f + k + i⟩)
  have hts : (List.range k).map (fun i => (.fieldAdd ⟨f + 2 * k + i⟩ ⟨f + i⟩ ⟨f + k + i⟩ : Instr)) =
      ts.map fun t => (.fieldAdd t.1 t.2.1 t.2.2 : Instr) := by
    simp only [ts, List.map_map]
    rfl
  have memts : ∀ t ∈ ts, ∃ i, i < k ∧ t = (⟨f + 2 * k + i⟩, ⟨f + i⟩, ⟨f + k + i⟩) := by
    intro t ht
    simp only [ts, List.mem_map, List.mem_range] at ht
    obtain ⟨i, hi, rfl⟩ := ht
    exact ⟨i, hi, rfl⟩
  obtain ⟨I2, g1, -, g3, g4⟩ := runLocal_adds E ts I1
    (by
      have e : ts.map (·.1.id) = List.range' (f + 2 * k) k := by
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
  have i2o : ∀ j, (j < f + 2 * k ∨ f + 3 * k ≤ j) → I2.fields j = I1.fields j := by
    intro j hj
    apply g4
    intro t ht
    obtain ⟨i, hi, rfl⟩ := memts t ht
    dsimp only
    omega
  refine ⟨I2, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun j hj => ?_, ?_⟩
  · rw [i2o _ (Or.inl (by omega)), i1a i hi]
  · rw [i2o _ (Or.inl (by omega)), i1b i hi]
  · rw [g3 (⟨f + 2 * k + i⟩, ⟨f + i⟩, ⟨f + k + i⟩) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩),
      i1a i hi, i1b i hi]
    rfl
  · rw [i2o _ (by omega), i1o _ (by omega)]
  · intro α β tA tB x y J sA sB h
    unfold sharedBlock
    rw [seqs_cons]
    refine hk1 _ _ x y J sA sB ?_
    refine jret_locals E _ _ σA σB x y J sA sB _ (fun i hi => by
      simp only [List.mem_map] at hi
      obtain ⟨_, _, rfl⟩ := hi
      rfl) I1 I2 (by rw [hts]; exact g1) h

end Blocks

/-! ## The offset agreement's step (`offsetStep`) -/

/-- The value the engines give a handle of the step's inputs: the constants 0, 1, −1 at
`f0 … f0 + 2` (`stepConsts`), the engine value otherwise. -/
def stepVal (I : Ideal) (f0 : Nat) (h : FieldH) : F :=
  if h.id = f0 then ofNat 0 else if h.id = f0 + 1 then ofNat 1 else if h.id = f0 + 2 then ofNat 0 - ofNat 1
  else (I.fields h.id).getD 0

/-- The step's 194 input values (`stepIns`), from the engine state before the step. -/
def stepVals (I : Ideal) (f0 : Nat) (st : OffsetState) (τ : Nat) : List F := (stepIns f0 st τ).map (stepVal I f0)

theorem mem_windowInputs {table : List FieldH} {zero one minus : FieldH} {digits : List Int} {h : FieldH}
    (hm : h ∈ windowInputs table zero one minus digits) : h ∈ table ∨ h = zero ∨ h = one ∨ h = minus := by
  simp only [windowInputs, List.mem_flatMap] at hm
  obtain ⟨e, -, he⟩ := hm
  have hg : ∀ k, table.getD k zero ∈ table ∨ table.getD k zero = zero := by
    intro k
    by_cases hk : k < table.length
    · exact Or.inl (getD_mem zero hk)
    · right
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
  split at he
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · rcases hg (entryAt e.2 e.1) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases hg (entryAt e.2 e.1 + 1) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · split <;> simp

theorem mem_stepIns {f0 : Nat} {st : OffsetState} {τ : Nat} {h : FieldH} (hm : h ∈ stepIns f0 st τ) :
    h = st.initial.1 ∨ h = st.initial.2 ∨ h ∈ st.table ∨ h.id = f0 ∨ h.id = f0 + 1 ∨ h.id = f0 + 2 := by
  simp only [stepIns, List.cons_append, List.mem_cons, List.nil_append] at hm
  rcases hm with rfl | rfl | hm
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · rcases mem_windowInputs hm with h1 | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

/-- The prepared state's handles lie below `f0` and hold values. -/
def StateBelow (I : Ideal) (f0 : Nat) (st : OffsetState) : Prop :=
  ∀ h, (h = st.initial.1 ∨ h = st.initial.2 ∨ h ∈ st.table) → h.id < f0 ∧ (I.fields h.id).isSome

section Step

variable (E : Env)

theorem localStep_public (out : FieldH) (v : F) (I : Ideal) :
    localStep E (.fieldPublic out v) I = some (I.setField out v) := rfl

theorem stepConsts_run (f0 : Nat) (I : Ideal) :
    runLocal E (stepConsts f0) I =
      some (((I.setField ⟨f0 + 0⟩ (ofNat 0)).setField ⟨f0 + 1⟩ (ofNat 1)).setField ⟨f0 + 2⟩ (ofNat 0 - ofNat 1)) := by
  simp only [stepConsts, publics, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, runLocal,
    localStep_public]

/-- **F22, `offsetStep` through `jointRun`.** Two honest parties with the same prepared state `st`
(its handles below `f0`, holding values), an offset τ < 2^252 whose ephemeral key is valid
(`ephemeralKey st.key τ = some u`), their 128 mask contributions in slot `maskSlot` with nonzero
sums, `edwards-offset-sum` loaded (`ComputesD … f`) and live on the step's inputs: both return
`(u, f0 + 387)`, with `u = montU (K₀ + τ·B)` (`ephemeralKey_spec`), their stores unchanged, handle
`f0 + 387` holding the program's output `f` on the step's input values (`stepVals`), and nothing
below `f0` changed. -/
theorem offsetStep_honest (po : Program) (f : (Nat → F) → List F) (hP : E.programs offsetSumName = some po)
    (hC : ComputesD po 194 128 1 f) (σA σB : Store) (I : Ideal) (f0 maskSlot : Nat) (st : OffsetState) (τ : Nat)
    (u : F) (hkey : ephemeralKey st.key τ = some u) (hτ : τ < 2 ^ 252) (hst : StateBelow I f0 st)
    (mA mB : Nat → F) (hA : σA.elems maskSlot = (List.range 128).map mA)
    (hB : σB.elems maskSlot = (List.range 128).map mB) (hm : ∀ i, i < 128 → mA i + mB i ≠ 0)
    (hL : Live po (fun i => (stepVals I f0 st τ).getD i 0)) :
    ∃ J, JRet (jointRun E (offsetStep f0 maskSlot st τ) (offsetStep f0 maskSlot st τ) σA σB I)
        (u, ⟨f0 + 387⟩) (u, ⟨f0 + 387⟩) J σA σB ∧
      J.fields (f0 + 387) = some ((f (fun i => (stepVals I f0 st τ).getD i 0)).getD 0 0) ∧
      u = TlsMpc.Node.Local.Edwards.montU
        (TlsMpc.Node.Local.Edwards.add st.key (TlsMpc.Node.Local.Edwards.mul τ TlsMpc.Node.Local.Edwards.base)) ∧
      (∀ k, k < f0 → J.fields k = I.fields k) := by
  rw [offsetStep_key f0 maskSlot st τ u hkey, if_pos (recode64_value τ hτ).2.1]
  -- the constants
  let I1 := ((I.setField ⟨f0 + 0⟩ (ofNat 0)).setField ⟨f0 + 1⟩ (ofNat 1)).setField ⟨f0 + 2⟩ (ofNat 0 - ofNat 1)
  have i1o : ∀ k, k ≠ f0 → k ≠ f0 + 1 → k ≠ f0 + 2 → I1.fields k = I.fields k := by
    intro k h0 h1 h2
    simp [I1, Ideal.setField, h0, h1, h2]
  -- the mask block
  obtain ⟨I2, -, -, i2s, i2o, hk2⟩ := sharedBlock_run E (f0 + 3) 128 maskSlot σA σB I1 mA mB hA hB
  -- the inputs' values
  have hval : ∀ h ∈ stepIns f0 st τ, I2.fields h.id = some (stepVal I f0 h) := by
    intro h hh
    rw [i2o _ (Or.inl ?_)]
    · rcases mem_stepIns hh with e | e | e | e | e | e
      · obtain ⟨l, s⟩ := hst h (Or.inl e)
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp s
        simp [stepVal, I1, Ideal.setField, hv, show h.id ≠ f0 by omega, show h.id ≠ f0 + 1 by omega,
          show h.id ≠ f0 + 2 by omega]
      · obtain ⟨l, s⟩ := hst h (Or.inr (Or.inl e))
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp s
        simp [stepVal, I1, Ideal.setField, hv, show h.id ≠ f0 by omega, show h.id ≠ f0 + 1 by omega,
          show h.id ≠ f0 + 2 by omega]
      · obtain ⟨l, s⟩ := hst h (Or.inr (Or.inr e))
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp s
        simp [stepVal, I1, Ideal.setField, hv, show h.id ≠ f0 by omega, show h.id ≠ f0 + 1 by omega,
          show h.id ≠ f0 + 2 by omega]
      · simp [stepVal, I1, Ideal.setField, e]
      · simp [stepVal, I1, Ideal.setField, e]
      · simp [stepVal, I1, Ideal.setField, e]
    · rcases mem_stepIns hh with e | e | e | e | e | e
      · exact Nat.lt_of_lt_of_le (hst h (Or.inl e)).1 (by omega)
      · exact Nat.lt_of_lt_of_le (hst h (Or.inr (Or.inl e))).1 (by omega)
      · exact Nat.lt_of_lt_of_le (hst h (Or.inr (Or.inr e))).1 (by omega)
      · omega
      · omega
      · omega
  have hins : (stepIns f0 st τ).mapM (fun h => I2.fields h.id) = some (stepVals I f0 st τ) :=
    mapM_vals _ _ _ hval
  have hmask : (sharedOut (f0 + 3) 128).mapM (fun h => I2.fields h.id) =
      some ((List.range 128).map fun i => mA i + mB i) :=
    mapM_hs I2 (f0 + 3 + 2 * 128) 128 _ (by simp) (fun i hi => by rw [i2s i hi, getD_map_range _ _ _ _ hi])
  obtain ⟨op, hrun, hol⟩ := run_one_live po 194 128 1 f hC (stepVals I f0 st τ) ((List.range 128).map fun i => mA i + mB i)
    (by simp [stepVals, stepIns_length]) (by simp) (fun i hi => by rw [getD_map_range _ _ _ _ hi]; exact hm i hi) hL
  let o := f (fun i => (stepVals I f0 st τ).getD i 0)
  let I3 := I2.setFields [⟨f0 + 3 + 384⟩] o
  obtain ⟨c2, c3⟩ := setFields_hs I2 (f0 + 387) 1 o hol
  have i3v : I3.fields (f0 + 387) = some (o.getD 0 0) := c3 0 (by decide)
  have i3o : ∀ k, k ≠ f0 + 387 → I3.fields k = I2.fields k := fun k hk => c2 k (by omega)
  -- the frees
  obtain ⟨I4, r1, r2⟩ := TlsMpc.Node.Flows.Convert.runLocal_freeFields E (hs f0 3 ++ sharedIns (f0 + 3) 128) I3
  have notFreed : ∀ k, (k < f0 ∨ f0 + 259 ≤ k) → ∀ h ∈ hs f0 3 ++ sharedIns (f0 + 3) 128, h.id ≠ k := by
    intro k hk h hh
    rcases List.mem_append.mp hh with hh | hh
    · obtain ⟨i, hi, e⟩ := mem_hs hh
      rw [e]
      omega
    · obtain ⟨i, hi, e⟩ := mem_hs hh
      rw [e]
      omega
  refine ⟨I4, ?_, ?_, (ephemeralKey_spec st.key τ u hkey).1, fun k hk => ?_⟩
  · rw [← seqs_append, ← seqs_append, ← seqs_append]
    refine jret_locals E _ _ σA σB _ _ I4 σA σB _ (fun i hi => by
      simp only [stepConsts, publics, List.mem_map] at hi
      obtain ⟨_, _, rfl⟩ := hi
      rfl) I I1 (stepConsts_run E f0 I) ?_
    refine hk2 _ _ _ _ I4 σA σB ?_
    rw [seqs_cons, seqs_nil]
    refine jret_program E _ _ _ _ _ _ _ _ σA σB I2 po _ _ o op _ _ I4 σA σB hP hins hmask hrun (by rw [hol]; rfl) ?_
    refine jret_locals E _ _ σA σB _ _ I4 σA σB _ (freeFs_local _) I3 I4 r1 ?_
    exact jret_done E _ _ σA σB I4
  · rw [r2 _ (notFreed _ (Or.inr (by omega))), i3v]
  · rw [r2 _ (notFreed _ (Or.inl hk)), i3o _ (by omega), i2o _ (Or.inl (by omega)),
      i1o _ (by omega) (by omega) (by omega)]

/-- **The agreement value** for `edwards-offset-sum` itself (`EdwardsAffine.offsetSum`): the handle
holds the Montgomery `u = (1 + y)/(1 − y)` of the sum of the initial point and the per-window
signed entries (`offsetSum_eval`; the inputs per window are `stepIns_window`). With `step_tableSum`
(H-GROUP: the table holds `(j·16^w)·R`) this is `u((k₀ + τ)·R)`. -/
theorem offsetStep_value (po : Program) (hP : E.programs offsetSumName = some po)
    (hC : ComputesD po 194 128 1 (fun i => TlsMpc.EdwardsAffine.offsetSum.map (TlsMpc.FieldDag.Expr.eval i)))
    (σA σB : Store) (I : Ideal) (f0 maskSlot : Nat) (st : OffsetState) (τ : Nat)
    (u : F) (hkey : ephemeralKey st.key τ = some u) (hτ : τ < 2 ^ 252) (hst : StateBelow I f0 st)
    (mA mB : Nat → F) (hA : σA.elems maskSlot = (List.range 128).map mA)
    (hB : σB.elems maskSlot = (List.range 128).map mB) (hm : ∀ i, i < 128 → mA i + mB i ≠ 0)
    (hL : Live po (fun i => (stepVals I f0 st τ).getD i 0)) :
    ∃ J, JRet (jointRun E (offsetStep f0 maskSlot st τ) (offsetStep f0 maskSlot st τ) σA σB I)
        (u, ⟨f0 + 387⟩) (u, ⟨f0 + 387⟩) J σA σB ∧
      J.fields (f0 + 387) = some
        (let input := fun i => (stepVals I f0 st τ).getD i 0
         let sum := TlsMpc.EdwardsAffine.sumTreeValue ((input 0, input 1) :: (List.range TlsMpc.EdwardsAffine.windows).map
            (fun w => (input (2 + 3 * w + 2) * input (2 + 3 * w), input (2 + 3 * w + 1))))
         (ofNat 1 + sum.2) * inverse (ofNat 1 - sum.2)) ∧
      u = TlsMpc.Node.Local.Edwards.montU
        (TlsMpc.Node.Local.Edwards.add st.key (TlsMpc.Node.Local.Edwards.mul τ TlsMpc.Node.Local.Edwards.base)) ∧
      (∀ k, k < f0 → J.fields k = I.fields k) := by
  obtain ⟨J, h1, h2, h3, h4⟩ := offsetStep_honest E po _ hP hC σA σB I f0 maskSlot st τ u hkey hτ hst mA mB hA hB hm hL
  refine ⟨J, h1, ?_, h3, h4⟩
  rw [h2, TlsMpc.EdwardsAffine.offsetSum_eval]
  simp only [List.getD_cons_zero]

end Step

end TlsMpc.Node.Flows.Curve
