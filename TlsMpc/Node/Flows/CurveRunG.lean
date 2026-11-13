import TlsMpc.Node.Flows.CurveRunF

/-!
# Honest curve runs (continued): the hinted lift

Stage S11, PROOF_GAPS F22 (program hypotheses `ComputesD`, `Live`: `CurveRunB.lean`).

  * `publics_run`: a block of public constants (`publics f vs`): handle `f + i` holds `vs_i`.
  * `lift_honest`: two honest parties' `lift` of `n` private coordinates. `lift-open` (mask free)
    on each `u_j` with the shared `r_j`, both parties' bits and mask points; its four checks per
    point open to zero; the `w_j` are opened; their public roots `rs`; `lift-point` (five masks)
    with the roots; the masked points `Z_j` are opened and are curve points. Both return
    `liftResult f0 n zv rs` (the validity, `x`, `y` handles, the opened `Z_j`, whether `w_j = 0`);
    handle `lfl + 5j + t` holds `lift-point`'s output `t` (`EdwardsHinted.liftPoint_eval`: the
    validity bit `sel ⊕ b` and the affine point).
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

theorem publics_run_from (E : Env) (f : Nat) : ∀ (vs : List F) (k : Nat) (I : Ideal),
    ∃ I', runLocal E ((vs.zipIdx k).map fun e => (.fieldPublic ⟨f + e.2⟩ e.1 : Instr)) I = some I' ∧
      (∀ i, i < vs.length → I'.fields (f + k + i) = some (vs.getD i 0)) ∧
      (∀ j, (j < f + k ∨ f + k + vs.length ≤ j) → I'.fields j = I.fields j)
  | [], k, I => ⟨I, rfl, fun i hi => by simp at hi, fun _ _ => rfl⟩
  | v :: vs, k, I => by
    obtain ⟨I', h1, h2, h3⟩ := publics_run_from E f vs (k + 1) (I.setField ⟨f + k⟩ v)
    refine ⟨I', ?_, fun i hi => ?_, fun j hj => ?_⟩
    · simp only [List.zipIdx_cons, List.map_cons, runLocal, localStep_public]
      exact h1
    · cases i with
      | zero =>
        rw [h3 _ (Or.inl (by omega))]
        simp [Ideal.setField]
      | succ i =>
        rw [show f + k + (i + 1) = f + (k + 1) + i by omega, h2 i (by simpa using hi)]
        simp
    · rw [h3 _ (by simp only [List.length_cons] at hj; omega)]
      simp only [Ideal.setField]
      rw [if_neg (by simp only [List.length_cons] at hj; omega)]

theorem publics_local (f : Nat) (vs : List F) : ∀ i ∈ publics f vs, isLocal i = true := by
  intro i hi
  simp only [publics, List.mem_map] at hi
  obtain ⟨_, _, rfl⟩ := hi
  rfl

theorem mapM_length_eq {α β : Type} (g : α → Option β) : ∀ (l : List α) (r : List β), l.mapM g = some r → r.length = l.length
  | [], r, h => by simp at h; subst h; rfl
  | a :: l, r, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨b, -, r', hr', rfl⟩ := h
    simp [mapM_length_eq g l r' hr']

/-- The 8 values of point `j`'s `lift-open` instance: `u`, the shared `r`, both bits, both mask points. -/
def liftOpenVals (uv rA rB pA pB : Nat → F) (bA bB : Nat → Bool) (j : Nat) : List F :=
  [uv j, rA j + rB j, X25519.bitValue (bA j), X25519.bitValue (bB j), pA (2 * j), pA (2 * j + 1), pB (2 * j), pB (2 * j + 1)]

/-- The 9 values of point `j`'s `lift-point` instance: the public root `cs`, `sel`, `u`, `r`, `b`
(0 when `w = 0`, else `lift-open`'s output 5), both mask points. -/
def liftPointVals (uv rA rB pA pB : Nat → F) (ov : Nat → List F) (rs : List (F × F × Bool)) (j : Nat) : List F :=
  [(rs.getD j (0, 0, false)).1, (rs.getD j (0, 0, false)).2.1, uv j, rA j + rB j,
   if (rs.getD j (0, 0, false)).2.2 then ofNat 0 else (ov j).getD 5 0, pA (2 * j), pA (2 * j + 1), pB (2 * j), pB (2 * j + 1)]

section Lift

variable (E : Env)

/-- **F22, `lift` through `jointRun`** (P-HINT at run level). `n` private coordinates (handles below
`f0`, holding `u_j`); slot `coins` holds each party's `n` random bits, `points` its `2n` mask-point
coordinates, `r` its `n` contributions, `masks` its `5n` contributions with nonzero sums;
`lift-open` loaded and computing `fO` (mask free), its four checks per point vanishing on the
honest values (`hchk`: the bits are bits and the mask points on the curve); the public roots of the
opened `w_j` exist (`hroots`; never fails under H-QR/Euler: `s11_liveness`); `lift-point` loaded
(`ComputesD … fP`) and live; the opened `Z_j` are curve points (`hZ`). Both return
`liftResult f0 n zv rs`, stores unchanged; the validity, `x`, `y` handles `lfl + 5j + t` hold
`lift-point`'s outputs `t`; nothing below `f0` changes. -/
theorem lift_honest (po pp : Program) (fO fP : (Nat → F) → List F) (mk : List TlsMpc.FieldDag.V3.OMark)
    (hPo : E.programs liftOpenName = some po) (hCo : Conv.Computes po 8 mk fO) (hmk : mk.length = 6)
    (hPp : E.programs liftPointName = some pp) (hCp : ComputesD pp 9 5 5 fP)
    (σA σB : Store) (I : Ideal) (f0 : Nat) (s : LiftSlots) (us : List FieldH)
    (uv rA rB pA pB mA mB : Nat → F) (bA bB : Nat → Bool)
    (hu : ∀ j, j < us.length → (us.getD j ⟨0⟩).id < f0 ∧ I.fields (us.getD j ⟨0⟩).id = some (uv j))
    (hcA : σA.elems s.coins = (List.range us.length).map fun j => X25519.bitValue (bA j))
    (hcB : σB.elems s.coins = (List.range us.length).map fun j => X25519.bitValue (bB j))
    (hpA : σA.elems s.points = (List.range (2 * us.length)).map pA)
    (hpB : σB.elems s.points = (List.range (2 * us.length)).map pB)
    (hrA : σA.elems s.r = (List.range us.length).map rA) (hrB : σB.elems s.r = (List.range us.length).map rB)
    (hmA : σA.elems s.masks = (List.range (5 * us.length)).map mA)
    (hmB : σB.elems s.masks = (List.range (5 * us.length)).map mB)
    (hm : ∀ i, i < 5 * us.length → mA i + mB i ≠ 0)
    (ov : Nat → List F) (hov : ∀ j, ov j = fO (fun i => (liftOpenVals uv rA rB pA pB bA bB j).getD i 0))
    (hchk : ∀ j, j < us.length → ∀ i, i < 4 → (ov j).getD (1 + i) 0 = 0)
    (rs : List (F × F × Bool)) (hroots : roots ((List.range us.length).map fun j => (ov j).getD 0 0) = some rs)
    (pv : Nat → List F) (hpv : ∀ j, pv j = fP (fun i => (liftPointVals uv rA rB pA pB ov rs j).getD i 0))
    (hL : ∀ j, j < us.length → Live pp (fun i => (liftPointVals uv rA rB pA pB ov rs j).getD i 0))
    (hZ : ∀ j, j < us.length → TlsMpc.Node.Local.Edwards.onCurve ((pv j).getD 3 0, (pv j).getD 4 0) = true) :
    ∃ J, JRet (jointRun E (lift f0 s us) (lift f0 s us) σA σB I)
        (liftResult f0 us.length ((List.range us.length).map fun j => [(pv j).getD 3 0, (pv j).getD 4 0]).flatten rs)
        (liftResult f0 us.length ((List.range us.length).map fun j => [(pv j).getD 3 0, (pv j).getD 4 0]).flatten rs)
        J σA σB ∧
      (∀ j t, j < us.length → t < 3 → J.fields (lfl f0 us.length + 5 * j + t) = some ((pv j).getD t 0)) ∧
      (∀ k, k < f0 → J.fields k = I.fields k) := by
  by_cases h0 : us.length = 0
  · have hp : us = [] := List.length_eq_zero_iff.mp h0
    subst hp
    refine ⟨I, ?_, fun j t hj => by simp at hj, fun _ _ => rfl⟩
    unfold lift
    simp only [List.length_nil, ↓reduceIte, List.range_zero, List.map_nil, List.flatten_nil]
    simp only [liftResult, List.range_zero, List.map_nil]
    exact jret_done E _ _ σA σB I
  generalize hn : us.length = n at hu hcA hcB hpA hpB hrA hrB hmA hmB hm hchk hroots hL hZ h0 ⊢
  have q1 : lfc f0 = f0 := rfl
  have q2 : lfp f0 n = f0 + 2 * n := rfl
  have q3 : lfr f0 n = f0 + 6 * n := by simp only [lfr, lfp]; omega
  have q4 : lfo f0 n = f0 + 9 * n := by simp only [lfo, lfr, lfp]; omega
  have q5 : lfk f0 n = f0 + 15 * n := by simp only [lfk, lfo, lfr, lfp]; omega
  have q6 : lfm f0 n = f0 + 18 * n := by simp only [lfm, lfk, lfo, lfr, lfp]; omega
  have q7 : lfl f0 n = f0 + 33 * n := by simp only [lfl, lfm, lfk, lfo, lfr, lfp]; omega
  have hrsl : rs.length = n := by
    have := mapM_length_eq _ _ _ hroots
    simpa using this
  -- the coins, the mask points, r
  obtain ⟨I1, i1a, i1b, i1o, hk1⟩ := inputs_run E (lfc f0) n s.coins .coins σA σB I
    (fun j => X25519.bitValue (bA j)) (fun j => X25519.bitValue (bB j)) hcA hcB (coins_range _ _) (coins_range _ _)
  obtain ⟨I2, i2a, i2b, i2o, hk2⟩ := inputs_run E (lfp f0 n) (2 * n) s.points .elements σA σB I1 pA pB hpA hpB rfl rfl
  obtain ⟨I3, -, -, i3s, i3o, hk3⟩ := sharedBlock_run E (lfr f0 n) n s.r σA σB I2 rA rB hrA hrB
  have back3 : ∀ k, k < f0 → I3.fields k = I.fields k := by
    intro k hk
    rw [i3o _ (Or.inl (by omega)), i2o _ (Or.inl (by omega)), i1o _ (Or.inl (by omega))]
  have i3u : ∀ j, j < n → I3.fields (us.getD j ⟨0⟩).id = some (uv j) := fun j hj => by
    rw [back3 _ (hu j hj).1, (hu j hj).2]
  have i3r : ∀ j, j < n → I3.fields (lfr f0 n + 2 * n + j) = some (rA j + rB j) := fun j hj => i3s j hj
  have i3ba : ∀ j, j < n → I3.fields (lfc f0 + j) = some (X25519.bitValue (bA j)) := fun j hj => by
    rw [i3o _ (Or.inl (by omega)), i2o _ (Or.inl (by omega)), i1a j hj]
  have i3bb : ∀ j, j < n → I3.fields (lfc f0 + n + j) = some (X25519.bitValue (bB j)) := fun j hj => by
    rw [i3o _ (Or.inl (by omega)), i2o _ (Or.inl (by omega)), i1b j hj]
  have i3pa : ∀ i, i < 2 * n → I3.fields (lfp f0 n + i) = some (pA i) := fun i hi => by
    rw [i3o _ (Or.inl (by omega)), i2a i hi]
  have i3pb : ∀ i, i < 2 * n → I3.fields (lfp f0 n + 2 * n + i) = some (pB i) := fun i hi => by
    rw [i3o _ (Or.inl (by omega)), i2b i hi]
  -- lift-open
  have hinsO : ((List.range n).flatMap (openIns f0 n us)).mapM (fun h => I3.fields h.id) =
      some ((List.range n).map fun j => liftOpenVals uv rA rB pA pB bA bB j).flatten := by
    rw [TlsMpc.Node.Flows.Masks.flatten_map']
    apply mapM_flatMap_vals
    intro j hj
    have hj' := List.mem_range.mp hj
    have e5 := i3pa (2 * j) (by omega)
    have e6 : I3.fields (lfp f0 n + 2 * j + 1) = some (pA (2 * j + 1)) := by
      rw [show lfp f0 n + 2 * j + 1 = lfp f0 n + (2 * j + 1) by omega]; exact i3pa _ (by omega)
    have e7 := i3pb (2 * j) (by omega)
    have e8 : I3.fields (lfp f0 n + 2 * n + 2 * j + 1) = some (pB (2 * j + 1)) := by
      rw [show lfp f0 n + 2 * n + 2 * j + 1 = lfp f0 n + 2 * n + (2 * j + 1) by omega]; exact i3pb _ (by omega)
    simp only [openIns, List.mapM_cons, List.mapM_nil, i3u j hj', i3r j hj', i3ba j hj', i3bb j hj', e5, e6, e7, e8]
    rfl
  have hCoD := computesD_of_computes po 8 mk fO hCo
  rw [hmk] at hCoD
  obtain ⟨opO, hrunO⟩ := runProgram_live po 8 0 6 fO hCoD n (fun j => liftOpenVals uv rA rB pA pB bA bB j) (fun _ => [])
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ i hi => absurd hi (Nat.not_lt_zero i))
    (fun j _ => live_of_computes po 8 mk fO hCo _)
  rw [TlsMpc.Node.Flows.Masks.flatten_map_nil] at hrunO
  have holO : ∀ j, j < n → (ov j).length = 6 := by
    intro j _
    rw [hov j, ← hmk]
    exact (run_one_computes po 8 mk fO hCo _ rfl).2
  have hov' : (fun j => fO (fun i => (liftOpenVals uv rA rB pA pB bA bB j).getD i 0)) = ov := funext fun j => (hov j).symm
  rw [hov'] at hrunO
  let voO := ((List.range n).map ov).flatten
  have hvoO : voO.length = n * 6 := by
    rw [length_flatten_eq 6 _ (by
      intro c hc
      simp only [List.mem_map, List.mem_range] at hc
      obtain ⟨j, hj, rfl⟩ := hc
      exact holO j hj)]
    simp
  let I4 := I3.setFields (hs (lfo f0 n) (n * 6)) voO
  obtain ⟨c2, -⟩ := setFields_hs I3 (lfo f0 n) (n * 6) voO hvoO
  have i4v : ∀ j t, j < n → t < 6 → I4.fields (lfo f0 n + (j * 6 + t)) = some ((ov j).getD t 0) :=
    fun j t hj ht => outs_value I3 (lfo f0 n) n 6 ov holO j t hj ht
  have back4 : ∀ k, k < lfo f0 n → I4.fields k = I3.fields k := fun k hk => c2 k (Or.inl hk)
  -- the checks
  let zc : List F := ((List.range n).map fun _ => (List.range 4).map fun _ => (0 : F)).flatten
  have hzc : (liftChecks f0 n).mapM (fun h => I4.fields h.id) = some zc := by
    simp only [zc, liftChecks]
    rw [TlsMpc.Node.Flows.Masks.flatten_map']
    apply mapM_flatMap_vals
    intro j hj
    have hj' := List.mem_range.mp hj
    exact mapM_hs I4 _ 4 _ (by simp) (fun i hi => by
      rw [show lfo f0 n + 6 * j + 1 + i = lfo f0 n + (j * 6 + (1 + i)) by omega, i4v j (1 + i) hj' (by omega),
        getD_map_range _ _ _ _ hi]
      exact congrArg some (hchk j hj' i hi))
  have hzcok : zc.length = 4 * n ∧ allZero zc = true := by
    refine ⟨?_, ?_⟩
    · rw [length_flatten_eq 4 _ (by
        intro c hc
        simp only [List.mem_map, List.mem_range] at hc
        obtain ⟨j, -, rfl⟩ := hc
        simp)]
      simp [Nat.mul_comm]
    · simp only [allZero, List.all_eq_true, zc, List.mem_flatten, List.mem_map, List.mem_range]
      rintro x ⟨l, ⟨j, -, rfl⟩, hx⟩
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      rfl
  -- the w's
  let ws := (List.range n).map fun j => (ov j).getD 0 0
  have hws : (liftWs f0 n).mapM (fun h => I4.fields h.id) = some ws :=
    mapM_map_vals _ _ _ _ (fun j hj => by
      have hj' := List.mem_range.mp hj
      show I4.fields (lfo f0 n + 6 * j) = _
      rw [show lfo f0 n + 6 * j = lfo f0 n + (j * 6 + 0) by omega]
      exact i4v j 0 hj' (by decide))
  have hwsl : ws.length = us.length := by simp [ws, hn]
  -- the publics
  let pubs := rs.flatMap fun r => [r.1, r.2.1, ofNat 0]
  obtain ⟨I5, p1, p2, p3⟩ := publics_run_from E (lfk f0 n) pubs 0 I4
  have hpubl : pubs.length = 3 * n := by
    simp only [pubs]
    rw [← TlsMpc.Node.Flows.Masks.flatten_map', length_flatten_eq 3 _ (by
      intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨r, -, rfl⟩ := hc
      rfl), List.length_map, hrsl, Nat.mul_comm]
  have i5p : ∀ j t, j < n → t < 3 → I5.fields (lfk f0 n + (3 * j + t)) =
      some ([(rs.getD j (0, 0, false)).1, (rs.getD j (0, 0, false)).2.1, ofNat 0].getD t 0) := by
    intro j t hj ht
    rw [show lfk f0 n + (3 * j + t) = lfk f0 n + 0 + (j * 3 + t) by omega, p2 _ (by omega)]
    have := flatten_getD 3 (rs.map fun r => [r.1, r.2.1, ofNat 0]) j t (0 : F) (by
      intro c hc
      simp only [List.mem_map] at hc
      obtain ⟨r, -, rfl⟩ := hc
      rfl) (by simpa [hrsl] using hj) ht
    simp only [pubs]
    rw [← TlsMpc.Node.Flows.Masks.flatten_map', this,
      TlsMpc.Node.Flows.Masks.getD_map_lt _ _ _ (0, 0, false) _ (by rw [hrsl]; exact hj)]
  have back5 : ∀ k, (k < lfk f0 n ∨ lfk f0 n + 3 * n ≤ k) → I5.fields k = I4.fields k := by
    intro k hk
    exact p3 k (by rw [hpubl]; omega)
  -- the masks
  obtain ⟨I6, -, -, i6s, i6o, hk6⟩ := sharedBlock_run E (lfm f0 n) (5 * n) s.masks σA σB I5 mA mB hmA hmB
  have back6 : ∀ k, k < lfm f0 n → I6.fields k = I5.fields k := fun k hk => i6o k (Or.inl hk)
  -- lift-point
  have hinsP : ((List.range n).flatMap (pointIns f0 n us rs)).mapM (fun h => I6.fields h.id) =
      some ((List.range n).map fun j => liftPointVals uv rA rB pA pB ov rs j).flatten := by
    rw [TlsMpc.Node.Flows.Masks.flatten_map']
    apply mapM_flatMap_vals
    intro j hj
    have hj' := List.mem_range.mp hj
    have b6 : ∀ k, k < lfo f0 n → I6.fields k = I3.fields k := fun k hk => by
      rw [back6 _ (by omega), back5 _ (Or.inl (by omega)), back4 _ hk]
    have e1 : I6.fields (lfk f0 n + 3 * j) = some (rs.getD j (0, 0, false)).1 := by
      rw [back6 _ (by omega), show lfk f0 n + 3 * j = lfk f0 n + (3 * j + 0) by omega, i5p j 0 hj' (by decide)]
      rfl
    have e2 : I6.fields (lfk f0 n + 3 * j + 1) = some (rs.getD j (0, 0, false)).2.1 := by
      rw [back6 _ (by omega), show lfk f0 n + 3 * j + 1 = lfk f0 n + (3 * j + 1) by omega, i5p j 1 hj' (by decide)]
      rfl
    have e5 : I6.fields (if (rs.getD j (0, 0, false)).2.2 then (⟨lfk f0 n + 3 * j + 2⟩ : FieldH)
        else ⟨lfo f0 n + 6 * j + 5⟩).id =
        some (if (rs.getD j (0, 0, false)).2.2 then ofNat 0 else (ov j).getD 5 0) := by
      split
      · rw [back6 (lfk f0 n + 3 * j + 2) (by omega), show lfk f0 n + 3 * j + 2 = lfk f0 n + (3 * j + 2) by omega,
          i5p j 2 hj' (by decide)]
        rfl
      · rw [back6 (lfo f0 n + 6 * j + 5) (by omega), back5 (lfo f0 n + 6 * j + 5) (Or.inl (by omega)),
          show lfo f0 n + 6 * j + 5 = lfo f0 n + (j * 6 + 5) by omega, i4v j 5 hj' (by decide)]
    have e6 : I6.fields (lfp f0 n + 2 * j) = some (pA (2 * j)) := by
      rw [b6 (lfp f0 n + 2 * j) (by omega)]
      exact i3pa _ (by omega)
    have e7 : I6.fields (lfp f0 n + 2 * j + 1) = some (pA (2 * j + 1)) := by
      rw [b6 (lfp f0 n + 2 * j + 1) (by omega), show lfp f0 n + 2 * j + 1 = lfp f0 n + (2 * j + 1) by omega]
      exact i3pa _ (by omega)
    have e8 : I6.fields (lfp f0 n + 2 * n + 2 * j) = some (pB (2 * j)) := by
      rw [b6 (lfp f0 n + 2 * n + 2 * j) (by omega)]
      exact i3pb _ (by omega)
    have e9 : I6.fields (lfp f0 n + 2 * n + 2 * j + 1) = some (pB (2 * j + 1)) := by
      rw [b6 (lfp f0 n + 2 * n + 2 * j + 1) (by omega),
        show lfp f0 n + 2 * n + 2 * j + 1 = lfp f0 n + 2 * n + (2 * j + 1) by omega]
      exact i3pb _ (by omega)
    have e3 : I6.fields (us.getD j ⟨0⟩).id = some (uv j) := by
      rw [b6 (us.getD j ⟨0⟩).id (by have := (hu j hj').1; omega), i3u j hj']
    have e4 : I6.fields (lfr f0 n + 2 * n + j) = some (rA j + rB j) := by
      rw [b6 (lfr f0 n + 2 * n + j) (by omega), i3r j hj']
    simp only [pointIns, List.mapM_cons, List.mapM_nil, e1, e2, e3, e4, e5, e6, e7, e8, e9]
    rfl
  have hmaskP : (sharedOut (lfm f0 n) (5 * n)).mapM (fun h => I6.fields h.id) =
      some ((List.range n).map fun j => (List.range 5).map fun i => mA (j * 5 + i) + mB (j * 5 + i)).flatten := by
    rw [masks_flatten (fun i => mA i + mB i) n 5, Nat.mul_comm n 5]
    exact mapM_hs I6 _ (5 * n) _ (by simp) (fun i hi => by rw [i6s i hi, getD_map_range _ _ _ _ hi])
  have holP : ∀ j, j < n → (pv j).length = 5 := by
    intro j hj
    obtain ⟨-, -, c3, c4⟩ := hCp
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp (hL j hj (fun _ => 1) (fun _ _ => by decide))
    obtain ⟨outs, opn⟩ := r
    have := c4 _ _ _ _ hr
    rw [hpv j, ← this, (TlsMpc.FieldDag.V3.eval_lengths pp _ _ _ _ hr).2, c3]
  obtain ⟨opP, hrunP⟩ := runProgram_live pp 9 5 5 fP hCp n (fun j => liftPointVals uv rA rB pA pB ov rs j)
    (fun j => (List.range 5).map fun i => mA (j * 5 + i) + mB (j * 5 + i)) (fun _ _ => rfl) (fun j _ => by simp)
    (fun j hj i hi => by
      rw [getD_map_range _ _ _ _ hi]
      exact hm _ (by have := mask_index j i n 5 hj hi; omega)) hL
  have hpv' : (fun j => fP (fun i => (liftPointVals uv rA rB pA pB ov rs j).getD i 0)) = pv := funext fun j => (hpv j).symm
  rw [hpv'] at hrunP
  let voP := ((List.range n).map pv).flatten
  have hvoP : voP.length = n * 5 := by
    rw [length_flatten_eq 5 _ (by
      intro c hc
      simp only [List.mem_map, List.mem_range] at hc
      obtain ⟨j, hj, rfl⟩ := hc
      exact holP j hj)]
    simp
  let I7 := I6.setFields (hs (lfl f0 n) (n * 5)) voP
  obtain ⟨c7, -⟩ := setFields_hs I6 (lfl f0 n) (n * 5) voP hvoP
  have i7v : ∀ j t, j < n → t < 5 → I7.fields (lfl f0 n + (j * 5 + t)) = some ((pv j).getD t 0) :=
    fun j t hj ht => outs_value I6 (lfl f0 n) n 5 pv holP j t hj ht
  -- the Z's
  let zv := ((List.range n).map fun j => [(pv j).getD 3 0, (pv j).getD 4 0]).flatten
  have hzv : (liftZs f0 n).mapM (fun h => I7.fields h.id) = some zv := by
    simp only [zv, liftZs]
    rw [TlsMpc.Node.Flows.Masks.flatten_map']
    apply mapM_flatMap_vals
    intro j hj
    have hj' := List.mem_range.mp hj
    exact mapM_hs I7 _ 2 _ rfl (fun i hi => by
      rw [show lfl f0 n + 5 * j + 3 + i = lfl f0 n + (j * 5 + (3 + i)) by omega, i7v j (3 + i) hj' (by omega)]
      match i, hi with
      | 0, _ => rfl
      | 1, _ => rfl)
  have hzl : ∀ c ∈ (List.range n).map (fun j => [(pv j).getD 3 0, (pv j).getD 4 0]), c.length = 2 := by
    intro c hc
    simp only [List.mem_map] at hc
    obtain ⟨j, -, rfl⟩ := hc
    rfl
  have hzvok : zv.length = 2 * n ∧ (liftResult f0 n zv rs).all (fun l => TlsMpc.Node.Local.Edwards.onCurve l.z) = true := by
    refine ⟨by rw [length_flatten_eq 2 _ hzl]; simp [Nat.mul_comm], ?_⟩
    simp only [liftResult, List.all_eq_true, List.mem_map, List.mem_range]
    rintro l ⟨j, hj, rfl⟩
    have g0 := flatten_getD 2 _ j 0 (0 : F) hzl (by simpa using hj) (by decide)
    have g1 := flatten_getD 2 _ j 1 (0 : F) hzl (by simpa using hj) (by decide)
    rw [getD_map_range _ _ _ _ hj] at g0 g1
    show TlsMpc.Node.Local.Edwards.onCurve (zv.getD (2 * j) 0, zv.getD (2 * j + 1) 0) = true
    rw [show 2 * j = j * 2 + 0 by omega, g0, show j * 2 + 0 + 1 = j * 2 + 1 by omega, g1]
    exact hZ j hj
  -- the frees
  have hfrees : liftFrees f0 n = (hs (lfc f0) (2 * n) ++ hs (lfp f0 n) (4 * n) ++ sharedIns (lfr f0 n) n ++
      sharedOut (lfr f0 n) n ++ hs (lfo f0 n) (6 * n) ++ hs (lfk f0 n) (3 * n) ++ sharedIns (lfm f0 n) (5 * n) ++
      liftZs f0 n).map fun h => (.freeField h : Instr) := rfl
  obtain ⟨I8, r1, r2⟩ := TlsMpc.Node.Flows.Convert.runLocal_freeFields E (hs (lfc f0) (2 * n) ++ hs (lfp f0 n) (4 * n) ++
    sharedIns (lfr f0 n) n ++ sharedOut (lfr f0 n) n ++ hs (lfo f0 n) (6 * n) ++ hs (lfk f0 n) (3 * n) ++
    sharedIns (lfm f0 n) (5 * n) ++ liftZs f0 n) I7
  have nf : ∀ k, (k < f0 ∨ ∃ j t, j < n ∧ t < 3 ∧ k = lfl f0 n + 5 * j + t) →
      ∀ h ∈ hs (lfc f0) (2 * n) ++ hs (lfp f0 n) (4 * n) ++ sharedIns (lfr f0 n) n ++ sharedOut (lfr f0 n) n ++
        hs (lfo f0 n) (6 * n) ++ hs (lfk f0 n) (3 * n) ++ sharedIns (lfm f0 n) (5 * n) ++ liftZs f0 n, h.id ≠ k := by
    intro k hk h hh
    simp only [List.mem_append] at hh
    rcases hh with ((((((hh | hh) | hh) | hh) | hh) | hh) | hh) | hh
    any_goals
      obtain ⟨i, hi, e⟩ := mem_hs hh
      rw [e]
      rcases hk with hk | ⟨j, t, hj, ht, rfl⟩ <;> omega
    · simp only [liftZs, List.mem_flatMap, List.mem_range] at hh
      obtain ⟨j', hj', hh⟩ := hh
      obtain ⟨i, hi, e⟩ := mem_hs hh
      rw [e]
      rcases hk with hk | ⟨j, t, hj, ht, rfl⟩ <;> omega
  refine ⟨I8, ?_, fun j t hj ht => ?_, fun k hk => ?_⟩
  · unfold lift
    rw [hn, if_neg h0]
    simp only [liftBlock, hn, ← seqs_append, seqs_cons, seqs_nil, List.cons_append]
    refine hk1 _ _ _ _ I8 σA σB ?_
    refine hk2 _ _ _ _ I8 σA σB ?_
    refine hk3 _ _ _ _ I8 σA σB ?_
    refine jret_locals E _ _ σA σB _ _ I8 σA σB [.fieldCheck] (fun i hi => by
      simp only [List.mem_singleton] at hi
      subst hi
      rfl) I3 I3 rfl ?_
    refine jret_program E _ _ _ _ _ _ _ _ σA σB I3 po _ [] voO opO _ _ I8 σA σB hPo hinsO rfl hrunO
      (by rw [hvoO]; simp [hs, Nat.mul_comm]) ?_
    rw [show hs (lfo f0 n) (6 * n) = hs (lfo f0 n) (n * 6) by rw [Nat.mul_comm 6 n]]
    refine jret_openFieldThen E _ _ _ _ σA σB I4 zc _ _ I8 σA σB hzc ?_
    unfold liftAfterChecks
    rw [hn, if_pos hzcok]
    refine jret_openFieldThen E _ _ _ _ σA σB I4 ws _ _ I8 σA σB hws ?_
    unfold liftAfterW
    rw [if_pos hwsl, hroots]
    simp only [pointBlock, hn, ← seqs_append]
    refine jret_locals E _ _ σA σB _ _ I8 σA σB _ (publics_local _ _) I4 I5 p1 ?_
    refine hk6 _ _ _ _ I8 σA σB ?_
    rw [seqs_cons, seqs_nil]
    refine jret_program E _ _ _ _ _ _ _ _ σA σB I6 pp _ _ voP opP _ _ I8 σA σB hPp hinsP hmaskP hrunP
      (by rw [hvoP]; simp [hs, Nat.mul_comm]) ?_
    rw [show hs (lfl f0 n) (5 * n) = hs (lfl f0 n) (n * 5) by rw [Nat.mul_comm 5 n]]
    refine jret_openFieldThen E _ _ _ _ σA σB I7 zv _ _ I8 σA σB hzv ?_
    unfold liftAfterZ
    rw [if_pos hzvok, hfrees]
    refine jret_locals E _ _ σA σB _ _ I8 σA σB _ (fun i hi => by
      simp only [List.mem_map] at hi
      obtain ⟨_, _, rfl⟩ := hi
      rfl) I7 I8 r1 ?_
    exact jret_done E _ _ σA σB I8
  · rw [r2 _ (nf _ (Or.inr ⟨j, t, hj, ht, rfl⟩)), show lfl f0 n + 5 * j + t = lfl f0 n + (j * 5 + t) by omega,
      i7v j t hj (by omega)]
  · rw [r2 _ (nf _ (Or.inl hk)), c7 _ (Or.inl (by omega)), back6 _ (by omega), back5 _ (Or.inl (by omega)),
      back4 _ (by omega), back3 k hk]

end Lift

end TlsMpc.Node.Flows.Curve
