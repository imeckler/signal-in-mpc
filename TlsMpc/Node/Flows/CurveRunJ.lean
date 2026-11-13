import TlsMpc.Node.Flows.CurveRunI
import TlsMpc.Node.Flows.CurveProgLive

/-!
# Honest curve runs without per-program hypotheses (PROOF_GAPS F22a, F22b)

Stage S11. The honest-run theorems of `CurveRun*.lean` restated with the program hypotheses
discharged (`CurveProgLive.lean`):

  * `ComputesD` / `Conv.Computes` from the loader's facts only: the program under the name is the V3
    program of its declaration (`dX.program = some p`) with the mask count the shell checks;
  * `Live` from the per-program INPUT CONDITION (`PL.OffsetSumIn`, `PL.PrepareIn`, `PL.LiftPointIn`,
    `PL.BitTableIn`, `PL.SignatureIn`, `PL.TorsionIn`: curve points, bits, the few nonzero
    denominators that are not the addition law's), under the named group facts `CompleteAddition`,
    `AddClosed`, `ExtClosed`, `RecipientOnCurve` (theorems of `proofs/`);
  * F22b, "the program's checks vanish on honest inputs": DERIVED for `offsetPrepare` (the masked
    recipient check is zero for a valid `u`, the bit checks for bits: `prepare_checks`) and for
    `lift` (the bit checks for bits, the curve checks for curve mask points: `liftOpen_checks`);
    REDUCED for `tables` to the program's own link predicate `EdwardsHinted.LinkedFrom` (each hinted
    window base is 16 times the one before, the hypothesis of `EdwardsHinted.bitTable_sound`:
    `bitTable_checks`); "the opened `Z` is a curve point" for `lift` DERIVED (`Z = M_A + M_B + P`,
    `AddClosed`: `liftPoint_Z_onCurve`).

New theorem names (the old ones stay): `agree_honest'`, `offsetStep_value'`, `offsetStepFast_honest'`,
`offsetPrepare_honest'`, `signatures_honest'`, `torsion_honest'`, `agreeAffine_honest'`,
`agreeHinted_honest'`, `tables_honest'`, `lift_honest'`, `splitAgree_montU'`.
-/

namespace TlsMpc.Node.Flows.Curve

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Run
open TlsMpc.FieldDag (F modulus ofNat inverse Expr)
open TlsMpc.FieldDag.V3 (FieldInverse quotient Program)
open TlsMpc.FieldDag.Compiled (DivOk)
open TlsMpc.Node.Local.Edwards (curveValue)

/-! ## Checks that vanish -/

theorem getD_append_left {α : Type} (l l' : List α) (d : α) (i : Nat) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_zero_of_all {l : List F} (h : ∀ v ∈ l, v = 0) (i : Nat) : l.getD i 0 = 0 :=
  PL.getD_ok (fun v => v = 0) h rfl i

theorem bitCheck_zero (v : F) (h : PL.IsBit v) : v * (v - ofNat 1) = 0 := by
  rcases h with h | h <;> rw [h] <;> decide

/-- **F22b for `offsetPrepare`**: on `PrepareIn` inputs the 505 leading outputs of `edwards-prepare`
(the masked recipient check and the 504 bit checks) are zero. -/
theorem prepare_checks (input : Nat → F) (h : PL.PrepareIn input) :
    ∀ i, i < 505 → (TlsMpc.EdwardsAffine.prepare.map (Expr.eval input)).getD i 0 = 0 := by
  intro i hi
  rw [PL.prepare_eq, List.append_assoc, List.map_append]
  have hl : (([TlsMpc.EdwardsAffine.mul (TlsMpc.EdwardsAffine.mul (TlsMpc.EdwardsAffine.sub PL.rCC PL.rXX)
      (TlsMpc.EdwardsAffine.add PL.rCC PL.rXX)) (.input 1)] ++
      ((List.range (2 * TlsMpc.EdwardsAffine.scalarBits)).map (fun i => Expr.input (2 + i))).map
        TlsMpc.EdwardsAffine.bitCheck).map (Expr.eval input)).length = 505 := by
    simp only [List.length_map, List.length_append, List.length_singleton, List.length_range]
    decide
  rw [getD_append_left _ _ _ _ (by rw [hl]; exact hi)]
  apply getD_zero_of_all
  intro v hv
  simp only [List.map_append, List.map_map, List.mem_append, List.mem_map, List.mem_singleton, List.mem_range,
    Function.comp_def] at hv
  rcases hv with ⟨a, rfl, rfl⟩ | ⟨k, hk, rfl⟩
  · have hv := h.valid
    rw [PL.recipient_eq] at hv
    dsimp only at hv
    show Expr.eval input (TlsMpc.EdwardsAffine.mul (TlsMpc.EdwardsAffine.sub PL.rCC PL.rXX)
      (TlsMpc.EdwardsAffine.add PL.rCC PL.rXX)) * input 1 = 0
    rw [hv]
    exact PL.zero_mul' _
  · exact bitCheck_zero _ (h.bits k hk)

/-- The link differences of a linked chain of bases are zero. -/
theorem linksFrom_zero {ε : Type} (input : Nat → F) (step : PL.Pt → List ε × PL.Pt) :
    ∀ (b : PL.Pt) (rest : List PL.Pt), TlsMpc.EdwardsHinted.LinkedFrom (TlsMpc.EdwardsAffine.evalPoint input) step b rest →
      ∀ d ∈ TlsMpc.EdwardsHinted.linksFrom step b rest, d.1.eval input = 0 ∧ d.2.eval input = 0
  | _, [], _ => fun d hd => by simp [TlsMpc.EdwardsHinted.linksFrom] at hd
  | b, c :: rest, h => by
    intro d hd
    simp only [TlsMpc.EdwardsHinted.linksFrom, List.mem_cons] at hd
    rcases hd with rfl | hd
    · have e := h.1
      simp only [TlsMpc.EdwardsAffine.evalPoint, Prod.mk.injEq] at e
      show (step b).2.1.eval input - c.1.eval input = 0 ∧ (step b).2.2.eval input - c.2.eval input = 0
      rw [e.1, e.2]
      constructor <;> grind
    · exact linksFrom_zero input step c rest h.2 d hd

/-- The masked links of a linked chain open to zero. -/
theorem masked_zero (input : Nat → F) (m : Nat) (ds : List (Expr × Expr))
    (h : ∀ d ∈ ds, d.1.eval input = 0 ∧ d.2.eval input = 0) :
    ∀ v ∈ (TlsMpc.EdwardsHinted.masked m ds).map (Expr.eval input), v = 0 := by
  intro v hv
  simp only [List.mem_map] at hv
  obtain ⟨e, he, rfl⟩ := hv
  simp only [TlsMpc.EdwardsHinted.masked, List.mem_flatMap] at he
  obtain ⟨⟨d, i⟩, hx, he⟩ := he
  have hd : d ∈ ds := by
    have := List.mem_map_of_mem (f := Prod.fst) hx
    rw [List.zipIdx_map_fst] at this
    exact this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · show d.1.eval input * input _ = 0
    rw [(h d hd).1]
    exact PL.zero_mul' _
  · show d.2.eval input * input _ = 0
    rw [(h d hd).2]
    exact PL.zero_mul' _

/-- The window bases of `edwards-bit-table` are linked: each hinted base is `16·` the one before
(`doublings`), the hypothesis of `EdwardsHinted.bitTable_sound`. For honest hints (A's
`16^w·(Z − M_A)`, B's `16^w·M_B`) this is the group law (`proofs/` `bitTable_entries`,
`doublings_multiples`). -/
def TableLinked (input : Nat → F) : Prop :=
  TlsMpc.EdwardsHinted.LinkedFrom (TlsMpc.EdwardsAffine.evalPoint input) TlsMpc.EdwardsHinted.doublings
    (TlsMpc.EdwardsAffine.inputPoint 0) ((List.range (TlsMpc.EdwardsAffine.windows - 1)).map
      (fun i => TlsMpc.EdwardsHinted.hinted (2 + 4 * i)))

set_option maxRecDepth 100000 in
theorem bitTable_masked_length :
    (TlsMpc.EdwardsHinted.masked (2 + 4 * (TlsMpc.EdwardsAffine.windows - 1))
      (TlsMpc.EdwardsHinted.links TlsMpc.EdwardsHinted.doublings (TlsMpc.EdwardsHinted.bitTableBases ()))).length = 126 := by
  decide +kernel

/-- **F22b for `tables`, reduced to the links**: when the window bases are linked, the 126 link
checks of `edwards-bit-table` are zero. -/
theorem bitTable_checks (input : Nat → F) (h : TableLinked input) :
    ∀ i, i < 126 → ((TlsMpc.EdwardsHinted.bitTable ()).map (Expr.eval input)).getD i 0 = 0 := by
  intro i hi
  unfold TlsMpc.EdwardsHinted.bitTable
  rw [List.map_append, getD_append_left _ _ _ _ (by rw [List.length_map, bitTable_masked_length]; exact hi)]
  apply getD_zero_of_all
  apply masked_zero
  exact linksFrom_zero input TlsMpc.EdwardsHinted.doublings _ _ h

/-- **F22b for `lift`**: on bits and curve mask points the four checks of `lift-open` are zero. -/
theorem liftOpen_checks (input : Nat → F) (hb2 : PL.IsBit (input 2)) (hb3 : PL.IsBit (input 3))
    (hA : curveValue (input 4, input 5) = 0) (hB : curveValue (input 6, input 7) = 0) :
    ∀ i, i < 4 → ((TlsMpc.EdwardsHinted.liftOpen ()).map (Expr.eval input)).getD (1 + i) 0 = 0 := by
  intro i hi
  rw [TlsMpc.EdwardsHinted.liftOpen_eval]
  rcases i with _ | _ | _ | _ | i
  · exact bitCheck_zero _ hb2
  · exact bitCheck_zero _ hb3
  · exact hA
  · exact hB
  · omega

/-- **The opened `Z = M_A + M_B + P` of `lift-point` is a curve point** (`AddClosed`). -/
theorem liftPoint_Z_onCurve (hA : AddClosed) (input : Nat → F) (h : PL.LiftPointIn input) :
    TlsMpc.Node.Local.Edwards.onCurve (((TlsMpc.EdwardsHinted.liftPoint ()).map (Expr.eval input)).getD 3 0,
      ((TlsMpc.EdwardsHinted.liftPoint ()).map (Expr.eval input)).getD 4 0) = true := by
  rw [TlsMpc.EdwardsHinted.liftPoint_eval]
  have hz := hA _ _ (hA _ _ h.maskA h.maskB) h.point
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  simp only [TlsMpc.Node.Local.Edwards.onCurve, beq_iff_eq]
  exact hz

/-! ## The restated honest runs -/

section Restated

variable (E : Env)

/-- **`agree_honest` without program hypotheses**: `x25519-fast` loaded as its declaration's
program (no mask). -/
theorem agree_honest' (hinv : FieldInverse) (px : Program) (hP : E.programs x25519Name = some px)
    (hd : dX25519.program = some px) (hm0 : px.masks = 0)
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
      (∀ k, k < f0 → J.fields k = I.fields k) :=
  agree_honest E hinv px hP (x25519_computes hinv px hd hm0) hq σA σB I f0 slot jobs bits u mA mB hsw hu hlo hA hB hm

/-- **`offsetStep_value` without program hypotheses**: `edwards-offset-sum` loaded as its
declaration's program (128 masks), the step's inputs satisfying `OffsetSumIn` (curve points, the
sum not the neutral element). -/
theorem offsetStep_value' (hinv : FieldInverse) (hCA : CompleteAddition) (hAC : AddClosed) (po : Program)
    (hP : E.programs offsetSumName = some po) (hd : dOffsetSum.program = some po) (hm128 : po.masks = 128)
    (σA σB : Store) (I : Ideal) (f0 maskSlot : Nat) (st : OffsetState) (τ : Nat)
    (u : F) (hkey : ephemeralKey st.key τ = some u) (hτ : τ < 2 ^ 252) (hst : StateBelow I f0 st)
    (mA mB : Nat → F) (hA : σA.elems maskSlot = (List.range 128).map mA)
    (hB : σB.elems maskSlot = (List.range 128).map mB) (hm : ∀ i, i < 128 → mA i + mB i ≠ 0)
    (hin : PL.OffsetSumIn (fun i => (stepVals I f0 st τ).getD i 0)) :
    ∃ J, JRet (jointRun E (offsetStep f0 maskSlot st τ) (offsetStep f0 maskSlot st τ) σA σB I)
        (u, ⟨f0 + 387⟩) (u, ⟨f0 + 387⟩) J σA σB ∧
      J.fields (f0 + 387) = some
        (let input := fun i => (stepVals I f0 st τ).getD i 0
         let sum := TlsMpc.EdwardsAffine.sumTreeValue ((input 0, input 1) :: (List.range TlsMpc.EdwardsAffine.windows).map
            (fun w => (input (2 + 3 * w + 2) * input (2 + 3 * w), input (2 + 3 * w + 1))))
         (ofNat 1 + sum.2) * inverse (ofNat 1 - sum.2)) ∧
      u = TlsMpc.Node.Local.Edwards.montU
        (TlsMpc.Node.Local.Edwards.add st.key (TlsMpc.Node.Local.Edwards.mul τ TlsMpc.Node.Local.Edwards.base)) ∧
      (∀ k, k < f0 → J.fields k = I.fields k) :=
  offsetStep_value E po hP (offsetSum_computesD hinv po hd hm128) σA σB I f0 maskSlot st τ u hkey hτ hst mA mB hA hB hm
    (offsetSum_live hinv hCA hAC po hd _ hin)

/-- **`offsetStepFast_honest` without program hypotheses** (`edwards-offset-sum-fast`, no mask). -/
theorem offsetStepFast_honest' (hinv : FieldInverse) (po : Program)
    (hP : E.programs offsetSumFastName = some po) (hd : dOffsetSumFast.program = some po) (hm0 : po.masks = 0)
    (hq : E.programs Inversion.quotientName = some quotient)
    (σA σB : Store) (I : Ideal) (f0 slot : Nat) (st : OffsetState) (τ : Nat) (u : F)
    (hkey : ephemeralKey st.key τ = some u) (hτ : τ < 2 ^ 252) (hst : StateBelow I f0 st)
    (mA mB : F) (hA : σA.elems slot = [mA]) (hB : σB.elems slot = [mB]) (hm : mA + mB ≠ 0)
    (hz : ((TlsMpc.EdwardsHinted.offsetSumFast ()).map (Expr.eval (fun i => (stepVals I f0 st τ).getD i 0))).getD 1 0 ≠ 0) :
    ∃ J, JRet (jointRun E (offsetStepFast f0 slot st τ) (offsetStepFast f0 slot st τ) σA σB I)
        (u, ⟨f0 + 8⟩) (u, ⟨f0 + 8⟩) J σA σB ∧
      J.fields (f0 + 8) =
        some (((TlsMpc.EdwardsHinted.offsetSumFast ()).map (Expr.eval (fun i => (stepVals I f0 st τ).getD i 0))).getD 0 0 *
          inverse (((TlsMpc.EdwardsHinted.offsetSumFast ()).map (Expr.eval (fun i => (stepVals I f0 st τ).getD i 0))).getD 1 0)) ∧
      u = TlsMpc.Node.Local.Edwards.montU
        (TlsMpc.Node.Local.Edwards.add st.key (TlsMpc.Node.Local.Edwards.mul τ TlsMpc.Node.Local.Edwards.base)) ∧
      (∀ k, k < f0 → J.fields k = I.fields k) :=
  offsetStepFast_honest E hinv po _ hP (offsetSumFast_computes hinv po hd hm0) hq σA σB I f0 slot st τ u hkey hτ hst
    mA mB hA hB hm hz

/-- **`offsetPrepare_honest` without program hypotheses** (F22a and F22b): `edwards-prepare` loaded
as its declaration's program (2031 masks); the honest inputs satisfy `PrepareIn` (`u` valid with
its three denominators nonzero, the scalar bits bits); the 505 checks vanish there
(`prepare_checks`), no longer a hypothesis. -/
theorem offsetPrepare_honest' (hinv : FieldInverse) (hCA : CompleteAddition) (hAC : AddClosed) (hR : RecipientOnCurve)
    (hh : ∀ m, (E.hash m).length = 32) (pp : Program)
    (hP : E.programs prepareName = some pp) (hd : dPrepare.program = some pp) (hm2031 : pp.masks = 2031)
    (σA σB : Store) (I : Ideal) (f0 : Nat) (s : OffsetSlots) (u : FieldH) (uv : F)
    (hu : I.fields u.id = some uv) (hul : u.id < f0)
    (rA rB : F) (hrA : σA.elems s.r = [rA]) (hrB : σB.elems s.r = [rB])
    (bA bB : Nat → Bool) (hbA : σA.elems s.bits = (List.range 252).map fun i => X25519.bitValue (bA i))
    (hbB : σB.elems s.bits = (List.range 252).map fun i => X25519.bitValue (bB i))
    (mA mB : Nat → F) (hmA : σA.elems s.masks = (List.range 2031).map mA)
    (hmB : σB.elems s.masks = (List.range 2031).map mB) (hm : ∀ i, i < 2031 → mA i + mB i ≠ 0)
    (hin : PL.PrepareIn (fun i => (prepVals uv rA rB bA bB).getD i 0))
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
        some ((TlsMpc.EdwardsAffine.prepare.map (Expr.eval (fun i => (prepVals uv rA rB bA bB).getD i 0))).getD (505 + i) 0)) ∧
      (∀ k, k < f0 → J.fields k = I.fields k) :=
  offsetPrepare_honest E hh pp _ hP (prepare_computesD hinv pp hd hm2031) σA σB I f0 s u uv hu hul rA rB hrA hrB
    bA bB hbA hbB mA mB hmA hmB hm (prepare_live hinv hCA hAC hR pp hd _ hin)
    (prepare_checks _ hin) PA PB hnA hsA hnB hsB hdA hdB hvA hvB hvS hc

/-- **`signatures_honest` without program hypotheses** (`edwards-signature-sum`, 2 masks; every
job's inputs satisfy `SignatureIn`). -/
theorem signatures_honest' (hinv : FieldInverse) (hX : ExtClosed) (ps : Program)
    (hP : E.programs signatureSumName = some ps) (hd : dSignatureSum.program = some ps) (hm2 : ps.masks = 2)
    (σA σB : Store) (I : Ideal) (f0 maskSlot : Nat) (baseT : List FieldH)
    (jobs : List (List FieldH × List FieldH))
    (hjobs : ∀ j, j < jobs.length → (jobs.getD j ([], [])).1.length = 1024 ∧ (jobs.getD j ([], [])).2.length = 510)
    (hbase : baseT.length = 1024)
    (hdef : ∀ j, j < jobs.length → ∀ h ∈ sigIns baseT (jobs.getD j ([], [])), h.id < f0 ∧ (I.fields h.id).isSome)
    (mA mB : Nat → F) (hA : σA.elems maskSlot = (List.range (2 * jobs.length)).map mA)
    (hB : σB.elems maskSlot = (List.range (2 * jobs.length)).map mB)
    (hm : ∀ i, i < 2 * jobs.length → mA i + mB i ≠ 0)
    (hin : ∀ j, j < jobs.length → PL.SignatureIn (fun i => (valsOf I (sigIns baseT (jobs.getD j ([], [])))).getD i 0)) :
    ∃ J, JRet (jointRun E (signatures f0 maskSlot baseT jobs) (signatures f0 maskSlot baseT jobs) σA σB I)
        ((List.range jobs.length).map fun j => (⟨f0 + 6 * jobs.length + 2 * j⟩, ⟨f0 + 6 * jobs.length + 2 * j + 1⟩))
        ((List.range jobs.length).map fun j => (⟨f0 + 6 * jobs.length + 2 * j⟩, ⟨f0 + 6 * jobs.length + 2 * j + 1⟩))
        J σA σB ∧
      (∀ j t, j < jobs.length → t < 2 → J.fields (f0 + 6 * jobs.length + (j * 2 + t)) =
        some (((TlsMpc.EdwardsHinted.signatureSum ()).map
          (Expr.eval (fun i => (valsOf I (sigIns baseT (jobs.getD j ([], [])))).getD i 0))).getD t 0)) ∧
      (∀ k, k < f0 → J.fields k = I.fields k) :=
  signatures_honest E ps _ hP (signatureSum_computesD hinv ps hd hm2) σA σB I f0 maskSlot baseT jobs hjobs hbase hdef
    mA mB hA hB hm (fun j hj => signatureSum_live hinv hX ps hd _ (hin j hj))

/-- **`torsion_honest` without program hypotheses** (`edwards-torsion-hinted`, 4 masks; each
point's hints are curve points: `TorsionIn`). -/
theorem torsion_honest' (hinv : FieldInverse) (hCA : CompleteAddition) (hAC : AddClosed) (hX : ExtClosed) (pt : Program)
    (hP : E.programs torsionName = some pt) (hd : dTorsion.program = some pt) (hm4 : pt.masks = 4)
    (σA σB : Store) (I : Ideal) (f0 hintSlot rSlot maskSlot : Nat) (pts : List Lifted)
    (hpts : ∀ j, j < pts.length → (pts.getD j liftedD).x.id < f0 ∧ (pts.getD j liftedD).y.id < f0 ∧
      (I.fields (pts.getD j liftedD).x.id).isSome ∧ (I.fields (pts.getD j liftedD).y.id).isSome)
    (ha hb rA rB mA mB : Nat → F)
    (hhA : σA.elems hintSlot = (List.range (2 * pts.length)).map ha)
    (hhB : σB.elems hintSlot = (List.range (2 * pts.length)).map hb)
    (hrA : σA.elems rSlot = (List.range pts.length).map rA) (hrB : σB.elems rSlot = (List.range pts.length).map rB)
    (hmA : σA.elems maskSlot = (List.range (4 * pts.length)).map mA)
    (hmB : σB.elems maskSlot = (List.range (4 * pts.length)).map mB)
    (hm : ∀ i, i < 4 * pts.length → mA i + mB i ≠ 0)
    (hin : ∀ j, j < pts.length → curveValue (ha (2 * j), ha (2 * j + 1)) = 0 ∧ curveValue (hb (2 * j), hb (2 * j + 1)) = 0) :
    ∃ J, JRet (jointRun E (torsion f0 hintSlot rSlot maskSlot pts) (torsion f0 hintSlot rSlot maskSlot pts) σA σB I)
        ((List.range pts.length).map fun j =>
          (⟨f0 + 4 * pts.length + 3 * pts.length + 12 * pts.length + 2 * j⟩,
           ⟨f0 + 4 * pts.length + 3 * pts.length + 12 * pts.length + 2 * j + 1⟩))
        ((List.range pts.length).map fun j =>
          (⟨f0 + 4 * pts.length + 3 * pts.length + 12 * pts.length + 2 * j⟩,
           ⟨f0 + 4 * pts.length + 3 * pts.length + 12 * pts.length + 2 * j + 1⟩)) J σA σB ∧
      (∀ j t, j < pts.length → t < 2 → J.fields (f0 + 4 * pts.length + 3 * pts.length + 12 * pts.length + (j * 2 + t)) =
        some (((TlsMpc.EdwardsHinted.torsionHinted ()).map
          (Expr.eval (fun i => (torsionVals I (pts.getD j liftedD) ha hb (fun j => rA j + rB j) j).getD i 0))).getD t 0)) ∧
      (∀ k, k < f0 → J.fields k = I.fields k) :=
  torsion_honest E pt _ hP (torsion_computesD hinv pt hd hm4) σA σB I f0 hintSlot rSlot maskSlot pts hpts
    ha hb rA rB mA mB hhA hhB hrA hrB hmA hmB hm
    (fun j hj => torsion_live hinv hCA hAC hX pt hd _ ⟨(hin j hj).1, (hin j hj).2⟩)

/-- **`agreeAffine_honest` without program hypotheses** (`edwards-affine-bit-sum`, no mask). -/
theorem agreeAffine_honest' (hinv : FieldInverse) (pa : Program)
    (hP : E.programs affineBitSumName = some pa) (hd : dAffineBitSum.program = some pa) (hm0 : pa.masks = 0)
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
          some (((TlsMpc.EdwardsHinted.affineBitSum ()).map
              (Expr.eval (fun i => (affineVals I (jobs.getD j ([], [])) (ρA j + ρB j)).getD i 0))).getD 0 0 *
            inverse (((TlsMpc.EdwardsHinted.affineBitSum ()).map
              (Expr.eval (fun i => (affineVals I (jobs.getD j ([], [])) (ρA j + ρB j)).getD i 0))).getD 1 0))) ∧
      (∀ k, k < f0 → J.fields k = I.fields k) :=
  agreeAffine_honest E hinv pa _ hP (affineBitSum_computes hinv pa hd hm0) hq σA σB I f0 rho qslot jobs hjobs hdef
    ρA ρB qA qB hrA hrB hqA hqB hqm

/-- **`agreeHinted_honest` without program hypotheses** (`edwards-bit-sum`, no mask). -/
theorem agreeHinted_honest' (hinv : FieldInverse) (pb : Program)
    (hP : E.programs bitSumName = some pb) (hd : dBitSum.program = some pb) (hm0 : pb.masks = 0)
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
          some (((TlsMpc.EdwardsHinted.bitSum ()).map
              (Expr.eval (fun k => (hintedVals I ((liveJobs jobs).getD i liveD) (ρA i + ρB i)).getD k 0))).getD 0 0 *
            inverse (((TlsMpc.EdwardsHinted.bitSum ()).map
              (Expr.eval (fun k => (hintedVals I ((liveJobs jobs).getD i liveD) (ρA i + ρB i)).getD k 0))).getD 1 0))) ∧
      (∀ k, k < f0 → J.fields k = I.fields k) :=
  agreeHinted_honest E hinv pb _ hP (bitSum_computes hinv pb hd hm0) hq σA σB I f0 rho qslot jobs hjobs hdef
    ρA ρB qA qB hrA hrB hqA hqB hqm

/-- **`tables_honest` without program hypotheses** (`edwards-bit-table`, 252 masks; each point's
values satisfy `BitTableIn` and its window bases are linked, `TableLinked`, which makes the 126
link checks vanish: `bitTable_checks`). -/
theorem tables_honest' (hinv : FieldInverse) (hCA : CompleteAddition) (hAC : AddClosed) (hX : ExtClosed) (pb : Program)
    (hP : E.programs bitTableName = some pb) (hd : dBitTable.program = some pb) (hm252 : pb.masks = 252)
    (σA σB : Store) (I : Ideal) (f0 : Nat) (s : TableSlots) (pts : List Lifted)
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
    (hin : ∀ j, j < pts.length → PL.BitTableIn (fun i => (tableVals I (pts.getD j liftedD) ha hb (fun i => lA i + lB i) j).getD i 0))
    (hlink : ∀ j, j < pts.length → TableLinked (fun i => (tableVals I (pts.getD j liftedD) ha hb (fun i => lA i + lB i) j).getD i 0)) :
    ∃ J, JRet (jointRun E (tables f0 s pts) (tables f0 s pts) σA σB I)
        ((List.range pts.length).map fun j =>
          hs (f0 + 252 * pts.length + 378 * pts.length + 756 * pts.length + 1150 * j + 126) 1024)
        ((List.range pts.length).map fun j =>
          hs (f0 + 252 * pts.length + 378 * pts.length + 756 * pts.length + 1150 * j + 126) 1024) J σA σB ∧
      (∀ j t, j < pts.length → t < 1024 →
        J.fields (f0 + 252 * pts.length + 378 * pts.length + 756 * pts.length + 1150 * j + 126 + t) =
          some (((TlsMpc.EdwardsHinted.bitTable ()).map
            (Expr.eval (fun i => (tableVals I (pts.getD j liftedD) ha hb (fun i => lA i + lB i) j).getD i 0))).getD
            (126 + t) 0)) ∧
      (∀ k, k < f0 → J.fields k = I.fields k) :=
  tables_honest E pb _ hP (bitTable_computesD hinv pb hd hm252) σA σB I f0 s pts hpts ha hb lA lB mA mB
    hhA hhB hlA hlB hmA hmB hm (fun j hj => bitTable_live hinv hCA hAC hX pb hd _ (hin j hj))
    (fun j hj => bitTable_checks _ (hlink j hj))

/-- **`lift_honest` without program hypotheses** (F22a, F22b): `lift-open` (no mask) and
`lift-point` (5 masks) loaded as their declarations' programs; the parties' mask points are curve
points, which (with their bits being bits) makes `lift-open`'s four checks vanish
(`liftOpen_checks`); `lift-point`'s inputs satisfy `LiftPointIn`, which makes it live and the opened
`Z` a curve point (`liftPoint_Z_onCurve`). -/
theorem lift_honest' (hinv : FieldInverse) (hCA : CompleteAddition) (hAC : AddClosed) (po pp : Program)
    (hPo : E.programs liftOpenName = some po) (hdo : dLiftOpen.program = some po) (hmo : po.masks = 0)
    (hPp : E.programs liftPointName = some pp) (hdp : dLiftPoint.program = some pp) (hmp : pp.masks = 5)
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
    (hpts : ∀ j, j < us.length → curveValue (pA (2 * j), pA (2 * j + 1)) = 0 ∧ curveValue (pB (2 * j), pB (2 * j + 1)) = 0)
    (rs : List (F × F × Bool))
    (hroots : roots ((List.range us.length).map fun j =>
      ((TlsMpc.EdwardsHinted.liftOpen ()).map (Expr.eval (fun i => (liftOpenVals uv rA rB pA pB bA bB j).getD i 0))).getD 0 0) = some rs)
    (hin : ∀ j, j < us.length → PL.LiftPointIn (fun i => (liftPointVals uv rA rB pA pB
      (fun j => (TlsMpc.EdwardsHinted.liftOpen ()).map (Expr.eval (fun i => (liftOpenVals uv rA rB pA pB bA bB j).getD i 0)))
      rs j).getD i 0)) :
    let ov : Nat → List F := fun j =>
      (TlsMpc.EdwardsHinted.liftOpen ()).map (Expr.eval (fun i => (liftOpenVals uv rA rB pA pB bA bB j).getD i 0))
    let pv : Nat → List F := fun j =>
      (TlsMpc.EdwardsHinted.liftPoint ()).map (Expr.eval (fun i => (liftPointVals uv rA rB pA pB ov rs j).getD i 0))
    ∃ J, JRet (jointRun E (lift f0 s us) (lift f0 s us) σA σB I)
        (liftResult f0 us.length ((List.range us.length).map fun j => [(pv j).getD 3 0, (pv j).getD 4 0]).flatten rs)
        (liftResult f0 us.length ((List.range us.length).map fun j => [(pv j).getD 3 0, (pv j).getD 4 0]).flatten rs)
        J σA σB ∧
      (∀ j t, j < us.length → t < 3 → J.fields (lfl f0 us.length + 5 * j + t) = some ((pv j).getD t 0)) ∧
      (∀ k, k < f0 → J.fields k = I.fields k) := by
  intro ov pv
  have hbit : ∀ b : Bool, PL.IsBit (X25519.bitValue b) := by
    intro b
    cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hchk : ∀ j, j < us.length → ∀ i, i < 4 → (ov j).getD (1 + i) 0 = 0 := by
    intro j hj i hi
    exact liftOpen_checks (fun i => (liftOpenVals uv rA rB pA pB bA bB j).getD i 0) (hbit (bA j)) (hbit (bB j))
      (hpts j hj).1 (hpts j hj).2 i hi
  have hL : ∀ j, j < us.length → Live pp (fun i => (liftPointVals uv rA rB pA pB ov rs j).getD i 0) :=
    fun j hj => liftPoint_live hinv hCA hAC pp hdp (fun i => (liftPointVals uv rA rB pA pB ov rs j).getD i 0) (hin j hj)
  have hZ : ∀ j, j < us.length → TlsMpc.Node.Local.Edwards.onCurve ((pv j).getD 3 0, (pv j).getD 4 0) = true :=
    fun j hj => liftPoint_Z_onCurve hAC (fun i => (liftPointVals uv rA rB pA pB ov rs j).getD i 0) (hin j hj)
  exact lift_honest E po pp (fun i => (TlsMpc.EdwardsHinted.liftOpen ()).map (Expr.eval i))
    (fun i => (TlsMpc.EdwardsHinted.liftPoint ()).map (Expr.eval i)) [.pub, .pub, .pub, .pub, .pub, .never]
    hPo (liftOpen_computes hinv po hdo hmo) rfl
    hPp (liftPoint_computesD hinv pp hdp hmp) σA σB I f0 s us uv rA rB pA pB mA mB bA bB hu hcA hcB hpA hpB hrA hrB
    hmA hmB hm ov (fun _ => rfl) hchk rs hroots pv (fun _ => rfl) hL hZ

/-- **`splitAgree_montU` without program hypotheses** (`edwards-on-curve`, `edwards-add-u`, no
mask). -/
theorem splitAgree_montU' (hinv : FieldInverse) (hCA : CompleteAddition)
    (pOn pAdd : Program)
    (hOn : E.programs onCurveName = some pOn) (hdOn : dOnCurve.program = some pOn) (hmOn : pOn.masks = 0)
    (hAdd : E.programs addUName = some pAdd) (hdAdd : dAddU.program = some pAdd) (hmAdd : pAdd.masks = 0)
    (hq : E.programs Inversion.quotientName = some quotient)
    (σA σB : Store) (I : Ideal) (f0 tSlot maskSlot : Nat) (xA yA xB yB mA mB : F)
    (hA : σA.elems tSlot = [xA, yA]) (hB : σB.elems tSlot = [xB, yB])
    (hmA : σA.elems maskSlot = [mA]) (hmB : σB.elems maskSlot = [mB]) (hm : mA + mB ≠ 0)
    (hcA : curveValue (xA, yA) = 0) (hcB : curveValue (xB, yB) = 0) :
    (jointRun E (splitAgree f0 tSlot maskSlot) (splitAgree f0 tSlot maskSlot) σA σB I).ideal.fields (f0 + 11) =
      some (TlsMpc.Node.Local.Edwards.montU (TlsMpc.Node.Local.Edwards.add (xA, yA) (xB, yB))) :=
  splitAgree_montU hinv hCA E pOn pAdd hOn hAdd (onCurve_computes hinv pOn hdOn hmOn) (addU_computes hinv pAdd hdAdd hmAdd)
    hq σA σB I f0 tSlot maskSlot xA yA xB yB mA mB hA hB hmA hmB hm hcA hcB

end Restated

end TlsMpc.Node.Flows.Curve
