import TlsMpc.Node.Flows.CurveRunB

/-!
# Honest curve runs (continued): the fast step, agreements from affine powers

Stage S11, PROOF_GAPS F22 (see `CurveRunB.lean` for the program hypotheses `ComputesD`, `Live`).

  * `offsetStepFast_honest`: `edwards-offset-sum-fast` (mask free, `Conv.Computes`) and one masked
    quotient: both parties return `(u, f0 + 8)` with `u = montU (K₀ + τ·B)`; handle `f0 + 8` holds
    `X · Z⁻¹` of the program's projective output on the step's inputs, when `Z ≠ 0` (a zero `Z`,
    the neutral sum, aborts).
  * `agreeAffine_honest`: `m` agreements from affine powers (`edwards-affine-bit-sum`, mask free,
    with the shared `ρ` per job) and one quotient round: handle `fo + 2m + 3m + 2j` holds
    `X_j · Z_j⁻¹` of job `j`'s outputs.
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

section Fast

variable (E : Env)

/-- A mask-free program on one instance returns `f input` (`Conv.Computes`). -/
theorem run_one_computes (p : Program) (k : Nat) (marks : List TlsMpc.FieldDag.V3.OMark) (f : (Nat → F) → List F)
    (hC : Conv.Computes p k marks f) (vi : List F) (hi : vi.length = k) :
    runProgram p 1 vi [] = some (f (fun i => vi.getD i 0), []) ∧ (f (fun i => vi.getD i 0)).length = marks.length := by
  obtain ⟨c1, c2, c3, c4⟩ := hC
  have he := c4 (fun i => vi.getD i 0) (fun i => ([] : List F).getD i 0)
  refine ⟨runProgram_one p vi [] _ [] (by rw [hi, c1]) (by rw [c2]; rfl) he, ?_⟩
  rw [(TlsMpc.FieldDag.V3.eval_lengths p _ _ _ _ he).2, ← c3, List.length_map]

/-- **F22, `offsetStepFast` through `jointRun`.** As `offsetStep_honest`, with
`edwards-offset-sum-fast` (mask free, computing `f`: the projective `(X, Z)` of the sum) and one
masked quotient (slot `slot`, one contribution each, nonzero sum). If the sum's `Z` is not zero,
both return `(u, f0 + 8)`, `u = montU (K₀ + τ·B)`, handle `f0 + 8` holds `X · Z⁻¹`, the stores are
unchanged, nothing below `f0` changes. -/
theorem offsetStepFast_honest (hinv : FieldInverse) (po : Program) (f : (Nat → F) → List F)
    (hP : E.programs offsetSumFastName = some po) (hC : Conv.Computes po 194 [.never, .never] f)
    (hq : E.programs Inversion.quotientName = some quotient)
    (σA σB : Store) (I : Ideal) (f0 slot : Nat) (st : OffsetState) (τ : Nat) (u : F)
    (hkey : ephemeralKey st.key τ = some u) (hτ : τ < 2 ^ 252) (hst : StateBelow I f0 st)
    (mA mB : F) (hA : σA.elems slot = [mA]) (hB : σB.elems slot = [mB]) (hm : mA + mB ≠ 0)
    (hz : (f (fun i => (stepVals I f0 st τ).getD i 0)).getD 1 0 ≠ 0) :
    ∃ J, JRet (jointRun E (offsetStepFast f0 slot st τ) (offsetStepFast f0 slot st τ) σA σB I)
        (u, ⟨f0 + 8⟩) (u, ⟨f0 + 8⟩) J σA σB ∧
      J.fields (f0 + 8) = some ((f (fun i => (stepVals I f0 st τ).getD i 0)).getD 0 0 *
        inverse ((f (fun i => (stepVals I f0 st τ).getD i 0)).getD 1 0)) ∧
      u = TlsMpc.Node.Local.Edwards.montU
        (TlsMpc.Node.Local.Edwards.add st.key (TlsMpc.Node.Local.Edwards.mul τ TlsMpc.Node.Local.Edwards.base)) ∧
      (∀ k, k < f0 → J.fields k = I.fields k) := by
  simp only [offsetStepFast, hkey]
  rw [if_pos (recode64_value τ hτ).2.1]
  let I1 := ((I.setField ⟨f0 + 0⟩ (ofNat 0)).setField ⟨f0 + 1⟩ (ofNat 1)).setField ⟨f0 + 2⟩ (ofNat 0 - ofNat 1)
  have i1o : ∀ k, k ≠ f0 → k ≠ f0 + 1 → k ≠ f0 + 2 → I1.fields k = I.fields k := by
    intro k h0 h1 h2
    simp [I1, Ideal.setField, h0, h1, h2]
  -- the inputs' values
  have hval : ∀ h ∈ stepIns f0 st τ, I1.fields h.id = some (stepVal I f0 h) := by
    intro h hh
    rcases mem_stepIns hh with e | e | e | e | e | e
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
  have hins : (stepIns f0 st τ).mapM (fun h => I1.fields h.id) = some (stepVals I f0 st τ) :=
    mapM_vals _ _ _ hval
  obtain ⟨hrun, hol⟩ := run_one_computes po 194 _ f hC (stepVals I f0 st τ) (by simp [stepVals, stepIns_length])
  let o := f (fun i => (stepVals I f0 st τ).getD i 0)
  let I2 := I1.setFields (hs (f0 + 3) 2) o
  obtain ⟨c2, c3⟩ := setFields_hs I1 (f0 + 3) 2 o hol
  obtain ⟨I3, r1, r2⟩ := TlsMpc.Node.Flows.Convert.runLocal_freeFields E (hs f0 3) I2
  have nf : ∀ k, (k < f0 ∨ f0 + 3 ≤ k) → ∀ h ∈ hs f0 3, h.id ≠ k := by
    intro k hk h hh
    obtain ⟨i, hi, e⟩ := mem_hs hh
    rw [e]
    omega
  have i3x : I3.fields (f0 + 3) = some (o.getD 0 0) := by
    rw [r2 _ (nf _ (Or.inr (by omega)))]
    exact c3 0 (by decide)
  have i3z : I3.fields (f0 + 4) = some (o.getD 1 0) := by
    rw [r2 _ (nf _ (Or.inr (by omega)))]
    exact c3 1 (by decide)
  have i3o : ∀ k, k < f0 → I3.fields k = I.fields k := by
    intro k hk
    rw [r2 _ (nf _ (Or.inl hk)), c2 _ (Or.inl (by omega)), i1o _ (by omega) (by omega) (by omega)]
  obtain ⟨J, hJ, hJq, hJo⟩ := quotientMany_honest E hinv hq σA σB I3 (f0 + 5) slot [(⟨f0 + 3⟩, ⟨f0 + 4⟩)]
    (fun _ => o.getD 0 0) (fun _ => o.getD 1 0) (fun _ => mA) (fun _ => mB)
    (fun j hj => by
      have : j = 0 := by simpa using hj
      subst this
      exact i3x)
    (fun j hj => by
      have : j = 0 := by simpa using hj
      subst this
      exact i3z)
    (fun p hp => by
      simp only [List.mem_singleton] at hp
      subst hp
      exact ⟨by dsimp only; omega, by dsimp only; omega⟩)
    (by rw [hA]; rfl) (by rw [hB]; rfl) (fun _ _ => hm)
  have hres : (List.range [((⟨f0 + 3⟩ : FieldH), (⟨f0 + 4⟩ : FieldH))].length).map
      (fun j => (quotResult (f0 + 5) [((⟨f0 + 3⟩ : FieldH), (⟨f0 + 4⟩ : FieldH))].length j, decide (o.getD 1 0 = 0))) =
      [(⟨f0 + 8⟩, false)] := by
    have hz' : o.getD 1 0 ≠ 0 := hz
    simp only [List.length_singleton, List.range_one, List.map_cons, List.map_nil, decide_eq_false hz']
    rfl
  rw [hres] at hJ
  refine ⟨J, ?_, ?_, (ephemeralKey_spec st.key τ u hkey).1, fun k hk => ?_⟩
  · rw [← seqs_append, ← seqs_append]
    refine jret_locals E _ _ σA σB _ _ J σA σB _ (fun i hi => by
      simp only [stepConsts, publics, List.mem_map] at hi
      obtain ⟨_, _, rfl⟩ := hi
      rfl) I I1 (stepConsts_run E f0 I) ?_
    rw [seqs_cons, seqs_nil]
    refine jret_program E _ _ _ _ _ _ _ _ σA σB I1 po _ [] o [] _ _ J σA σB hP hins rfl hrun
      (by rw [hol]; rfl) ?_
    refine jret_locals E _ _ σA σB _ _ J σA σB _ (freeFs_local _) I2 I3 r1 ?_
    refine jret_bind E _ _ _ _ σA σB I3 _ _ J σA σB _ _ J σA σB hJ ?_
    exact jret_done E _ _ σA σB J
  · have := hJq 0 (by simp)
    simp only [List.length_singleton] at this
    rw [show f0 + 8 = f0 + 5 + 3 * 1 + 2 * 0 by omega]
    exact this
  · rw [hJo k (Or.inl (by omega)), i3o k hk]

end Fast

/-! ## The offset agreement's preparation (`offsetPrepare`) -/

theorem hs_add (a k l : Nat) : hs a (k + l) = hs a k ++ hs (a + k) l := by
  simp only [hs, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.add_assoc]

/-- The 506 input values of `edwards-prepare` in an honest run: the recipient's `u`, the shared
uniform `r = r_A + r_B`, A's 252 scalar bits, B's 252 scalar bits. -/
def prepVals (uv rA rB : F) (bA bB : Nat → Bool) : List F :=
  uv :: (rA + rB) :: ((List.range 252).map (fun i => X25519.bitValue (bA i)) ++
    (List.range 252).map (fun i => X25519.bitValue (bB i)))

theorem prepVals_length (uv rA rB : F) (bA bB : Nat → Bool) : (prepVals uv rA rB bA bB).length = 506 := by
  simp [prepVals]

/-- The state `offsetPrepare` returns in an honest run: the initial point and table handles after
the program's 505 checks, and `K₀ = P_A + P_B`. -/
def prepState (f0 : Nat) (K : TlsMpc.Node.Local.Edwards.Value) : OffsetState :=
  ⟨(⟨prepOuts f0 + 505⟩, ⟨prepOuts f0 + 506⟩), hs (prepOuts f0 + 507) 1024, K⟩

section Prepare

variable (E : Env)

theorem coins_range (b : Nat → Bool) (k : Nat) :
    coinsOk .coins ((List.range k).map fun i => X25519.bitValue (b i)) = true := by
  have e : ((List.range k).map fun i => X25519.bitValue (b i)) = ((List.range k).map b).map X25519.bitValue := by
    rw [List.map_map]
    rfl
  rw [e]
  exact TlsMpc.Node.Flows.Masks.coinsOk_bits _

/-- **F22, `offsetPrepare` through `jointRun`** (P-OFFSET (a), (c), (d) at run level). Two honest
parties: the recipient handle `u` (below `f0`) holds `uv`; slot `r` holds one contribution each;
slot `bits` holds each party's 252 scalar bits as 0/1 coins; slot `masks` 2031 contributions with
nonzero sums; the byte slots `nonce`, `share` as for `pointExchange_honest` (32-byte nonces, the
encoded K₀ halves decoding to valid `P_A`, `P_B` with a valid sum, distinct commitments);
`edwards-prepare` loaded (`ComputesD … f`), live on the honest inputs (`prepVals`), and its 505
checks vanish there (the recipient's masked curve check and the bit checks). Then both return
`prepState f0 (P_A + P_B)`: the initial point and the table are the handles after the checks, and
they hold the program's outputs 505 … 1530 on the honest inputs; the stores are unchanged; nothing
below `f0` changes. -/
theorem offsetPrepare_honest (hh : ∀ m, (E.hash m).length = 32) (pp : Program) (f : (Nat → F) → List F)
    (hP : E.programs prepareName = some pp) (hC : ComputesD pp 506 2031 1531 f)
    (σA σB : Store) (I : Ideal) (f0 : Nat) (s : OffsetSlots) (u : FieldH) (uv : F)
    (hu : I.fields u.id = some uv) (hul : u.id < f0)
    (rA rB : F) (hrA : σA.elems s.r = [rA]) (hrB : σB.elems s.r = [rB])
    (bA bB : Nat → Bool) (hbA : σA.elems s.bits = (List.range 252).map fun i => X25519.bitValue (bA i))
    (hbB : σB.elems s.bits = (List.range 252).map fun i => X25519.bitValue (bB i))
    (mA mB : Nat → F) (hmA : σA.elems s.masks = (List.range 2031).map mA)
    (hmB : σB.elems s.masks = (List.range 2031).map mB) (hm : ∀ i, i < 2031 → mA i + mB i ≠ 0)
    (hL : Live pp (fun i => (prepVals uv rA rB bA bB).getD i 0))
    (hck : ∀ i, i < 505 → (f (fun i => (prepVals uv rA rB bA bB).getD i 0)).getD i 0 = 0)
    (PA PB : TlsMpc.Node.Local.Edwards.Value)
    (hnA : (σA.bytes s.nonce).length = 32) (hsA : (σA.bytes s.share).length = 32)
    (hnB : (σB.bytes s.nonce).length = 32) (hsB : (σB.bytes s.share).length = 32)
    (hdA : TlsMpc.Node.Local.Edwards.decode (σA.bytes s.share) = some PA)
    (hdB : TlsMpc.Node.Local.Edwards.decode (σB.bytes s.share) = some PB)
    (hvA : TlsMpc.Node.Local.Edwards.isValid PA = true) (hvB : TlsMpc.Node.Local.Edwards.isValid PB = true)
    (hvS : TlsMpc.Node.Local.Edwards.isValid (TlsMpc.Node.Local.Edwards.add PA PB) = true)
    (hc : E.hash (commitFrame offsetTag .a (σA.bytes s.nonce) (σA.bytes s.share)) ≠
      E.hash (commitFrame offsetTag .b (σB.bytes s.nonce) (σB.bytes s.share))) :
    ∃ J, JRet (jointRun E (offsetPrepare E.hash .a f0 s u) (offsetPrepare E.hash .b f0 s u) σA σB I)
        (prepState f0 (TlsMpc.Node.Local.Edwards.add PA PB)) (prepState f0 (TlsMpc.Node.Local.Edwards.add PA PB))
        J σA σB ∧
      (∀ i, i < 1026 → J.fields (prepOuts f0 + 505 + i) =
        some ((f (fun i => (prepVals uv rA rB bA bB).getD i 0)).getD (505 + i) 0)) ∧
      (∀ k, k < f0 → J.fields k = I.fields k) := by
  have hfo : prepOuts f0 = f0 + 6600 := rfl
  have hpm : prepMasks = 2031 := rfl
  -- the shared r
  obtain ⟨I1, -, -, i1s, i1o, hk1⟩ := sharedBlock_run E f0 1 s.r σA σB I (fun _ => rA) (fun _ => rB)
    (by rw [hrA]; rfl) (by rw [hrB]; rfl)
  -- the scalar bits
  obtain ⟨I2, i2a, i2b, i2o, hk2⟩ := inputs_run E (f0 + 3) 252 s.bits .coins σA σB I1
    (fun i => X25519.bitValue (bA i)) (fun i => X25519.bitValue (bB i)) hbA hbB (coins_range _ _) (coins_range _ _)
  -- the masks
  obtain ⟨I3, -, -, i3s, i3o, hk3⟩ := sharedBlock_run E (f0 + 507) 2031 s.masks σA σB I2 mA mB hmA hmB
  -- the program's inputs
  have hins : (u :: sharedOut f0 1 ++ hs (f0 + 3) 504).mapM (fun h => I3.fields h.id) =
      some (prepVals uv rA rB bA bB) := by
    show ((u :: sharedOut f0 1) ++ hs (f0 + 3) 504).mapM _ = some ([uv, rA + rB] ++ _)
    refine mapM_append_vals _ _ _ _ _ ?_ ?_
    · show [u, (⟨f0 + 2 * 1 + 0⟩ : FieldH)].mapM _ = _
      have e1 : I3.fields u.id = some uv := by
        rw [i3o _ (Or.inl (by omega)), i2o _ (Or.inl (by omega)), i1o _ (Or.inl hul), hu]
      have e2 : I3.fields (f0 + 2 * 1 + 0) = some (rA + rB) := by
        rw [i3o _ (Or.inl (by omega)), i2o _ (Or.inl (by omega)), i1s 0 (by decide)]
      simp only [List.mapM_cons, List.mapM_nil, e1, e2]
      rfl
    · rw [show (504 : Nat) = 252 + 252 from rfl, hs_add]
      refine mapM_append_vals _ _ _ _ _
        (mapM_hs I3 (f0 + 3) 252 ((List.range 252).map fun i => X25519.bitValue (bA i)) (by simp) (fun i hi => ?_))
        (mapM_hs I3 (f0 + 3 + 252) 252 ((List.range 252).map fun i => X25519.bitValue (bB i)) (by simp)
          (fun i hi => ?_))
      · rw [i3o _ (Or.inl (by omega)), i2a i hi, getD_map_range _ _ _ _ hi]
      · rw [i3o _ (Or.inl (by omega)), i2b i hi, getD_map_range _ _ _ _ hi]
  have hmask : (sharedOut (f0 + 507) prepMasks).mapM (fun h => I3.fields h.id) =
      some ((List.range 2031).map fun i => mA i + mB i) :=
    mapM_hs I3 (f0 + 507 + 2 * 2031) 2031 _ (by simp) (fun i hi => by rw [i3s i hi, getD_map_range _ _ _ _ hi])
  obtain ⟨op, hrun, hol⟩ := run_one_live pp 506 2031 1531 f hC (prepVals uv rA rB bA bB)
    ((List.range 2031).map fun i => mA i + mB i) (prepVals_length _ _ _ _ _) (by simp)
    (fun i hi => by rw [getD_map_range _ _ _ _ hi]; exact hm i hi) hL
  let o := f (fun i => (prepVals uv rA rB bA bB).getD i 0)
  let I4 := I3.setFields (hs (prepOuts f0) 1531) o
  obtain ⟨c2, c3⟩ := setFields_hs I3 (prepOuts f0) 1531 o hol
  -- the checks
  let zs : List F := (List.range 505).map fun _ => 0
  have hz : (hs (prepOuts f0) 505).mapM (fun h => I4.fields h.id) = some zs :=
    mapM_hs I4 (prepOuts f0) 505 zs (by simp [zs]) (fun i hi => by
      rw [c3 i (by omega), getD_map_range _ _ _ _ hi]
      exact congrArg some (hck i hi))
  have hzok : zs.length = 505 ∧ allZero zs = true := by
    refine ⟨by simp [zs], ?_⟩
    simp [allZero, zs]
  -- the frees
  let L := sharedIns f0 1 ++ sharedOut f0 1 ++ hs (f0 + 3) 504 ++ sharedIns (f0 + 507) prepMasks ++ hs (prepOuts f0) 505
  obtain ⟨I5, r1, r2⟩ := TlsMpc.Node.Flows.Convert.runLocal_freeFields E L I4
  have hL5 : ∀ h ∈ L, f0 ≤ h.id ∧ h.id < prepOuts f0 + 505 := by
    intro h hh
    simp only [L, List.mem_append] at hh
    rw [hfo]
    rcases hh with (((hh | hh) | hh) | hh) | hh <;>
    · obtain ⟨i, hi, e⟩ := mem_hs hh
      rw [e]
      try rw [hpm] at hi
      omega
  have nf : ∀ k, (k < f0 ∨ prepOuts f0 + 505 ≤ k) → ∀ h ∈ L, h.id ≠ k := by
    intro k hk h hh
    have := hL5 h hh
    omega
  -- the K₀ exchange
  have hX := pointExchange_honest E hh offsetTag σA σB I5 s.nonce s.share s.nonce s.share PA PB hnA hsA hnB hsB
    hdA hdB hvA hvB hvS hc
  refine ⟨I5, ?_, fun i hi => ?_, fun k hk => ?_⟩
  · simp only [offsetPrepare, prepBlock, ← seqs_append, seqs_cons, seqs_nil]
    refine hk1 _ _ _ _ I5 σA σB ?_
    refine hk2 _ _ _ _ I5 σA σB ?_
    refine jret_locals E _ _ σA σB _ _ I5 σA σB [.fieldCheck] (fun i hi => by
      simp only [List.mem_singleton] at hi
      subst hi
      rfl) I2 I2 rfl ?_
    refine hk3 _ _ _ _ I5 σA σB ?_
    refine jret_program E _ _ _ _ _ _ _ _ σA σB I3 pp _ _ o op _ _ I5 σA σB hP hins hmask hrun
      (by rw [hol]; simp [hs]) ?_
    refine jret_openFieldThen E _ _ _ _ σA σB I4 zs _ _ I5 σA σB hz ?_
    rw [if_pos hzok, if_pos hzok]
    refine jret_locals E _ _ σA σB _ _ I5 σA σB _ (freeFs_local _) I4 I5 r1 ?_
    refine jret_bind E _ _ _ _ σA σB I5 _ _ I5 σA σB _ _ I5 σA σB hX ?_
    exact jret_done E _ _ σA σB I5
  · rw [r2 _ (nf _ (Or.inr (by omega))), show prepOuts f0 + 505 + i = prepOuts f0 + (505 + i) by omega,
      c3 (505 + i) (by omega)]
  · rw [r2 _ (nf _ (Or.inl hk)), c2 _ (Or.inl (by rw [hfo]; omega)), i3o _ (Or.inl (by omega)),
      i2o _ (Or.inl (by omega)), i1o _ (Or.inl hk)]

end Prepare

end TlsMpc.Node.Flows.Curve
