import TlsMpc.Node.Flows.Convert

/-!
# `Inversion.quotient`: masked inversion / division (P-INV)

REORGANIZATION_PLAN.md 7.1 P-INV and 5.5, stage S10. The masked quotient x / z of `x25519_fast.h`
(`quotient`, `evaluate_many`, lines 43-64) and `hinted_points.h` (162-174) as a script: the
natively V3 program `field-quotient` (`FieldDagV3.quotient`: a `Z` row with an explicit mask and its
public zero flag), with a fresh multiplicative mask.

THE MASK. A program mask must be a field handle marked `never` and is consumed by the instruction
(Engine.lean design note item 5). It is NOT a cut-and-choose word mask (those are `revealable`
and need no Boolean side here): each party inputs a fresh random element (its store slot, drawn by
`Channels.random`, rule 5) with `fieldInput` (marked never), and the mask is their sum m = m_A + m_B
(decision D14). For the honest party's uniform m_H, m is uniform whatever the other party inputs
(`mask_uniform`: m_H ↦ m_H + v is a bijection).

THE SCRIPT (field ids from `f0`): input m_A, m_B; m = m_A + m_B; `field-quotient` on (x, z) with
mask m: it opens o = z·m (released to both, label `maskedDenominator`) and defines q (secret) and
the zero flag (public); open the flag (`maskedDenominator`); free the contributions and the flag.
Result: the quotient handle and whether z·m was 0.

PROVED:
  * `quotient_disclosure` (T3): against any adversary, the adversary's view is a prefix of
    [o = z·m, the flag], for the m the engine holds (both labelled `maskedDenominator`), and the
    flag is 1 exactly when o = 0, so it adds nothing to o.
  * `quotient_honest` (P-INV (a), run level): two honest parties with a nonzero mask end with the
    handle `f0 + 3` holding x·z⁻¹ (0 for z = 0) and agree on the flag (z = 0).
  * P-INV (a)–(c) as field facts (`FieldDagV3.masked_div`, `opening_zero_iff`, `opening_bijective`),
    restated with the mask's provenance: `mask_uniform` (m_H ↦ m_H + v bijective), `inv_hides`
    (for z ≠ 0, m ↦ z·m is a bijection: the opening is uniform for a uniform mask).
  * P-INV (d): `FieldDagV3.quotient_masksOk` (by `decide` on its rows), and the engine consumes the
    mask (`check_program`).
  * `quotient_reveals` (kind `maskedDenominator`), `quotient_wf`.
-/

namespace TlsMpc.Node.Flows.Inversion

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs Silent blankWire every_seq every_seqs)
open TlsMpc.Node.Flows.Run
open TlsMpc.Node.Flows.Conv
open TlsMpc.FieldDag (F modulus ofNat inverse)
open TlsMpc.FieldDag.V3 (FieldInverse quotient)

/-- The program name (`loader.rs` FIELD_PROGRAMS: `field-quotient`, pinned by Lean's render). -/
def quotientName : Bytes := ascii "field-quotient"

def quotientTail (f0 : Nat) : List Instr := [.freeField ⟨f0⟩, .freeField ⟨f0 + 1⟩, .freeField ⟨f0 + 4⟩]

def quotientRest (f0 : Nat) (fl : List F) : Script (FieldH × Bool) :=
  match fl with
  | [flag] => seqs (quotientTail f0) (.done (⟨f0 + 3⟩, flag == ofNat 1))
  | _ => .abort "reply shape"

/-- **The masked quotient** x / z (0 when z = 0), with the zero flag. `slot`: this party's store
slot holding its one random mask contribution. -/
def quotientScript (f0 slot : Nat) (x z : FieldH) : Script (FieldH × Bool) :=
  seq (.fieldInput [⟨f0⟩] [⟨f0 + 1⟩] .elements false slot) <|
  seq (.fieldAdd ⟨f0 + 2⟩ ⟨f0⟩ ⟨f0 + 1⟩) <|
  seq (.program quotientName 1 [x, z] [⟨f0 + 2⟩] [⟨f0 + 3⟩, ⟨f0 + 4⟩] Label.maskedDenominator) <|
  openFieldThen [⟨f0 + 4⟩] Label.maskedDenominator (quotientRest f0)

def inversionKinds : List TlsMpc.Node.RevealKind := [.maskedDenominator]

theorem quotientTail_local (f0 : Nat) : ∀ i ∈ quotientTail f0, isLocal i = true := by
  intro i hi
  simp only [quotientTail, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> rfl

theorem quotient_reveals (f0 slot : Nat) (x z : FieldH) : Reveals inversionKinds (quotientScript f0 slot x z) := by
  unfold quotientScript
  refine every_seq (LabelIn.of_none rfl) (every_seq (LabelIn.of_none rfl)
    (every_seq (LabelIn.of_mem (k := .maskedDenominator) (by simp [inversionKinds]) rfl)
      (every_openFieldThen (LabelIn.of_mem (k := .maskedDenominator) (by simp [inversionKinds]) rfl) fun fl => ?_)))
  unfold quotientRest
  split
  · exact every_seqs (Every.done _) _ (fun i hi => LabelIn.of_none (label_local i (quotientTail_local f0 i hi)))
  · exact Every.abort _

/-- The quotient program on (x, z) with mask m. -/
theorem quotient_run (xv zv mv : F) :
    runProgram quotient 1 [xv, zv] [mv] =
      some ([if zv * mv = 0 then ofNat 0 else xv * mv * inverse (zv * mv), if zv * mv = 0 then ofNat 1 else ofNat 0],
        [zv * mv]) := by
  unfold runProgram
  rw [if_pos ⟨rfl, rfl⟩, ← TlsMpc.FieldDag.V3.inverseFast_eq]
  rfl

section Adv

variable (E : Env) (me : Party) (adv : Adversary) (f0 slot : Nat) (x z : FieldH)

/-- An input step releases nothing: the run's view is the rest's view from the state the inputs
define, for some values the two parties gave. -/
theorem viewD_fieldInput {α : Type} (oa ob : List FieldH) (k : FieldIn) (rev : Bool) (s : Script α) (σ : Store)
    (I : Ideal) (vD : List Release) (L : List F → List F → List Release)
    (h : ∀ va vb, va.length = oa.length → vb.length = ob.length →
      (withAdv E me adv s σ ((I.setFields oa va).setFields ob vb) vD).viewD <+: L va vb) :
    ∃ va vb, (withAdv E me adv (seq (.fieldInput oa ob k rev slot) s) σ I vD).viewD <+: L va vb := by
  unfold seq
  by_cases hc : (σ.elems slot).length = oa.length ∧ coinsOk k (σ.elems slot) = true
  · have hf : fill E.hash me σ (.fieldInput oa ob k rev slot) = some (.fieldInput oa ob k rev (σ.elems slot)) := by
      simp [fill, hc]
    simp only [withAdv, hf, Wire.early, Option.toList_none, List.append_nil]
    split
    · exact ⟨[], [], List.nil_prefix⟩
    · split
      · exact ⟨[], [], List.nil_prefix⟩
      · next I' toH toD hst =>
        have hst2 : ∃ va vb, va.length = oa.length ∧ vb.length = ob.length ∧
            (I.setFields oa va).setFields ob vb = I' ∧ toH = none ∧ toD = none := by
          cases me with
          | a =>
            simp only [idealStep, if_true] at hst
            split at hst
            · next hc' =>
              simp only [Option.some.injEq, Prod.mk.injEq] at hst
              exact ⟨_, _, hc'.1, hc'.2.1, hst.1, hst.2.1.symm, hst.2.2.symm⟩
            · simp at hst
          | b =>
            simp only [idealStep, reduceCtorEq, if_false] at hst
            split at hst
            · next hc' =>
              simp only [Option.some.injEq, Prod.mk.injEq] at hst
              exact ⟨_, _, hc'.1, hc'.2.1, hst.1, hst.2.1.symm, hst.2.2.symm⟩
            · simp at hst
        obtain ⟨va, vb, hva, hvb, rfl, rfl, rfl⟩ := hst2
        simp only [TlsMpc.Node.Flows.Contacts.absorb_none, Option.toList_none, List.nil_append]
        exact ⟨va, vb, by simpa using h va vb hva hvb⟩
  · have hf : fill E.hash me σ (.fieldInput oa ob k rev slot) = none := by
      simp only [fill]
      rw [if_neg hc]
    simp only [withAdv, hf]
    exact ⟨[], [], List.nil_prefix⟩

/-- **T3 for the masked quotient.** Against any adversary, from a state where x and z hold values
(and the script's handles are fresh), the adversary's view is a prefix of [z·m, the zero flag]
for the mask m the engine holds, both labelled `maskedDenominator`; the flag is 1 exactly when
z·m = 0. -/
theorem quotient_disclosure (hq : E.programs quotientName = some quotient) (σ : Store) (I : Ideal)
    (vD : List Release) (xv zv : F) (hx : I.fields x.id = some xv) (hz : I.fields z.id = some zv)
    (hfx : x.id ≠ f0 ∧ x.id ≠ f0 + 1 ∧ x.id ≠ f0 + 2) (hfz : z.id ≠ f0 ∧ z.id ≠ f0 + 1 ∧ z.id ≠ f0 + 2) :
    ∃ mv : F, (withAdv E me adv (quotientScript f0 slot x z) σ I vD).viewD <+:
      [⟨Label.maskedDenominator, .elems [zv * mv]⟩,
       ⟨Label.maskedDenominator, .elems [if zv * mv = 0 then ofNat 1 else ofNat 0]⟩] := by
  suffices key : ∃ va vb : List F, (withAdv E me adv (quotientScript f0 slot x z) σ I vD).viewD <+:
      [⟨Label.maskedDenominator, .elems [zv * (va.getD 0 0 + vb.getD 0 0)]⟩,
       ⟨Label.maskedDenominator, .elems [if zv * (va.getD 0 0 + vb.getD 0 0) = 0 then ofNat 1 else ofNat 0]⟩] by
    obtain ⟨va, vb, h⟩ := key
    exact ⟨_, h⟩
  unfold quotientScript
  refine viewD_fieldInput E me adv slot [⟨f0⟩] [⟨f0 + 1⟩] .elements false _ σ I vD
    (fun va vb => [⟨Label.maskedDenominator, .elems [zv * (va.getD 0 0 + vb.getD 0 0)]⟩,
       ⟨Label.maskedDenominator, .elems [if zv * (va.getD 0 0 + vb.getD 0 0) = 0 then ofNat 1 else ofNat 0]⟩])
    (fun va vb ha hb => ?_)
  · match va, vb, ha, hb with
    | [ma], [mb], _, _ =>
      simp only [List.getD_cons_zero]
      have hI1x : (((I.setFields [⟨f0⟩] [ma]).setFields [⟨f0 + 1⟩] [mb])).fields x.id = some xv := by
        simp [Ideal.setFields, Ideal.setField, hfx.1, hfx.2.1, hx]
      have hI1z : (((I.setFields [⟨f0⟩] [ma]).setFields [⟨f0 + 1⟩] [mb])).fields z.id = some zv := by
        simp [Ideal.setFields, Ideal.setField, hfz.1, hfz.2.1, hz]
      refine viewD_locals E me adv _ σ _ [.fieldAdd ⟨f0 + 2⟩ ⟨f0⟩ ⟨f0 + 1⟩] (by simp [isLocal]) _ vD (fun I2 h2 => ?_)
      have hI2 : I2 = ((I.setFields [⟨f0⟩] [ma]).setFields [⟨f0 + 1⟩] [mb]).setField ⟨f0 + 2⟩ (ma + mb) := by
        simp [runLocal, localStep, idealStep, blankWire, InstrP.map, Ideal.setFields, Ideal.setField] at h2
        exact h2.symm
      subst hI2
      refine viewD_program E me adv _ _ _ _ _ _ _ σ _ vD _ quotient [xv, zv] [ma + mb] _ _ hq
        (by simp [Ideal.setField, hfx.2.2, hfz.2.2, hI1x, hI1z]) (by simp [Ideal.setField]) (quotient_run xv zv (ma + mb))
        rfl ?_
      refine viewD_openFieldThen E me adv _ _ _ σ _ _ [if zv * (ma + mb) = 0 then ofNat 1 else ofNat 0] _
        (by simp [Ideal.setFields, Ideal.setField]) ?_
      simp only [quotientRest]
      exact TlsMpc.Node.Flows.Contacts.silent_prefix E me adv _
        (silent_locals (Silent.done _) _ (quotientTail_local f0)) _ _ _ _

end Adv

/-! ## Two honest parties -/

/-- **P-INV (a), run level.** Two honest parties whose mask contributions sum to a nonzero m end
with the handle `f0 + 3` holding x·z⁻¹ (0 when z = 0), and both return the flag "z = 0". -/
theorem quotient_honest (hinv : FieldInverse) (E : Env) (hq : E.programs quotientName = some quotient)
    (σA σB : Store) (I : Ideal) (f0 slot : Nat) (x z : FieldH) (xv zv mA mB : F)
    (hx : I.fields x.id = some xv) (hz : I.fields z.id = some zv)
    (hfx : x.id ≠ f0 ∧ x.id ≠ f0 + 1 ∧ x.id ≠ f0 + 2) (hfz : z.id ≠ f0 ∧ z.id ≠ f0 + 1 ∧ z.id ≠ f0 + 2)
    (hA : σA.elems slot = [mA]) (hB : σB.elems slot = [mB]) (hm : mA + mB ≠ 0) :
    (jointRun E (quotientScript f0 slot x z) (quotientScript f0 slot x z) σA σB I).result =
      some ((⟨f0 + 3⟩, decide (zv = 0)), (⟨f0 + 3⟩, decide (zv = 0))) ∧
    (jointRun E (quotientScript f0 slot x z) (quotientScript f0 slot x z) σA σB I).ideal.fields (f0 + 3) =
      some (xv * inverse zv) := by
  have hspec := TlsMpc.FieldDag.V3.quotient_spec hinv (fun j => if j = 0 then xv else zv) (fun _ => mA + mB) hm
  have hz0 : (zv * (mA + mB) = 0) ↔ zv = 0 := by
    rw [TlsMpc.FieldDag.V3.opening_zero_iff hinv]
    exact ⟨fun h => h.resolve_right hm, Or.inl⟩
  have hrun : runProgram quotient 1 [xv, zv] [mA + mB] =
      some ([xv * inverse zv, if zv = 0 then ofNat 1 else ofNat 0], [zv * (mA + mB)]) := by
    unfold runProgram
    rw [if_pos ⟨rfl, rfl⟩]
    simp only [List.range_one, List.mapM_cons, List.mapM_nil]
    have e : TlsMpc.FieldDag.V3.eval quotient (instanceAt [xv, zv] quotient.inputs 0) (instanceAt [mA + mB] quotient.masks 0) =
        TlsMpc.FieldDag.V3.eval quotient (fun j => if j = 0 then xv else zv) (fun _ => mA + mB) := by
      rw [TlsMpc.FieldDag.V3.quotient_eval, TlsMpc.FieldDag.V3.quotient_eval]
      rfl
    rw [e, hspec]
    rfl
  unfold quotientScript
  -- the input step
  have hI1 : idealStep E .a (.fieldInput [⟨f0⟩] [⟨f0 + 1⟩] .elements false [mA]) { elems := [mB] } I =
      some (((I.setFields [⟨f0⟩] [mA]).setFields [⟨f0 + 1⟩] [mB]), none, none) := by
    simp [idealStep, coinsOk]
  obtain ⟨r1, i1⟩ := TlsMpc.Node.Flows.Contacts.jointRun_seq E (.fieldInput [⟨f0⟩] [⟨f0 + 1⟩] .elements false slot)
    (.fieldInput [⟨f0⟩] [⟨f0 + 1⟩] .elements false slot) _ _ σA σB I
    ((I.setFields [⟨f0⟩] [mA]).setFields [⟨f0 + 1⟩] [mB])
    (.fieldInput [⟨f0⟩] [⟨f0 + 1⟩] .elements false [mA]) (.fieldInput [⟨f0⟩] [⟨f0 + 1⟩] .elements false [mB]) rfl
    (by simp [fill, hA, coinsOk]) (by simp [fill, hB, coinsOk]) (by simpa [Wire.part] using hI1)
  rw [r1, i1]
  -- the sum
  have hadd : runLocal E [.fieldAdd ⟨f0 + 2⟩ ⟨f0⟩ ⟨f0 + 1⟩] ((I.setFields [⟨f0⟩] [mA]).setFields [⟨f0 + 1⟩] [mB]) =
      some (((I.setFields [⟨f0⟩] [mA]).setFields [⟨f0 + 1⟩] [mB]).setField ⟨f0 + 2⟩ (mA + mB)) := by
    simp [runLocal, localStep, idealStep, blankWire, InstrP.map, Ideal.setFields, Ideal.setField]
  obtain ⟨r2, i2⟩ := jointRun_locals E _ _ σA σB [.fieldAdd ⟨f0 + 2⟩ ⟨f0⟩ ⟨f0 + 1⟩] (by simp [isLocal]) _ _ hadd
  simp only [TlsMpc.Node.Flows.Contacts.seqs_cons, TlsMpc.Node.Flows.Contacts.seqs_nil] at r2 i2
  rw [r2, i2]
  -- the program
  have hins : [x, z].mapM (fun h => ((((I.setFields [⟨f0⟩] [mA]).setFields [⟨f0 + 1⟩] [mB]).setField ⟨f0 + 2⟩
      (mA + mB))).fields h.id) = some [xv, zv] := by
    simp [Ideal.setFields, Ideal.setField, hfx.1, hfx.2.1, hfx.2.2, hfz.1, hfz.2.1, hfz.2.2, hx, hz]
  have hmask : [(⟨f0 + 2⟩ : FieldH)].mapM (fun h => ((((I.setFields [⟨f0⟩] [mA]).setFields [⟨f0 + 1⟩] [mB]).setField
      ⟨f0 + 2⟩ (mA + mB))).fields h.id) = some [mA + mB] := by
    simp only [List.mapM_cons, List.mapM_nil, Ideal.setField]
    rfl
  obtain ⟨r3, i3⟩ := jointRun_program E quotientName 1 [x, z] [⟨f0 + 2⟩] [⟨f0 + 3⟩, ⟨f0 + 4⟩] Label.maskedDenominator
    _ _ σA σB (((I.setFields [⟨f0⟩] [mA]).setFields [⟨f0 + 1⟩] [mB]).setField ⟨f0 + 2⟩ (mA + mB))
    quotient [xv, zv] [mA + mB] [xv * inverse zv, if zv = 0 then ofNat 1 else ofNat 0] [zv * (mA + mB)]
    hq hins hmask hrun (by simp)
  rw [r3, i3]
  -- the flag
  obtain ⟨r4, i4⟩ := jointRun_openFieldThen E [⟨f0 + 4⟩] Label.maskedDenominator (quotientRest f0) (quotientRest f0)
    σA σB ((((I.setFields [⟨f0⟩] [mA]).setFields [⟨f0 + 1⟩] [mB]).setField ⟨f0 + 2⟩ (mA + mB)).setFields
      [⟨f0 + 3⟩, ⟨f0 + 4⟩] [xv * inverse zv, if zv = 0 then ofNat 1 else ofNat 0])
    [if zv = 0 then ofNat 1 else ofNat 0] (by simp [Ideal.setFields, Ideal.setField])
  rw [r4, i4]
  simp only [quotientRest]
  have htail := jointRun_locals E (.done ((⟨f0 + 3⟩ : FieldH), ((if zv = 0 then ofNat 1 else ofNat 0) == ofNat 1)))
    (.done ((⟨f0 + 3⟩ : FieldH), ((if zv = 0 then ofNat 1 else ofNat 0) == ofNat 1))) σA σB (quotientTail f0)
    (quotientTail_local f0)
  obtain ⟨r5, i5⟩ := htail _ _ (by simp [quotientTail, runLocal, localStep, idealStep, blankWire, InstrP.map]; rfl)
  rw [r5, i5]
  have hflag : ((if zv = 0 then ofNat 1 else ofNat 0) == ofNat 1) = decide (zv = 0) := by
    by_cases h : zv = 0 <;> simp [h] <;> decide
  refine ⟨by simp [jointRun, hflag], ?_⟩
  simp [jointRun, Ideal.dropField, Ideal.setFields, Ideal.setField]

/-! ## Well-formedness -/

/-- **`quotientScript` is well formed**: the shell's `check` accepts every instruction on every
branch, from any context where x and z are live and none of the five field ids from `f0` was
ever defined, with `field-quotient` loaded (its V3 signature: 2 inputs, 1 mask, outputs never and
public). -/
theorem quotient_wf (sigs : Bytes → Option Sig) (c : Ctx) (f0 slot : Nat) (x z : FieldH)
    (hp : c.progs quotientName = some (ProgSig.ofProgram quotient))
    (hx : (c.field? x).isSome) (hz : (c.field? z).isSome)
    (hfx : x.id ≠ f0 ∧ x.id ≠ f0 + 1 ∧ x.id ≠ f0 + 2) (hfz : z.id ≠ f0 ∧ z.id ≠ f0 + 1 ∧ z.id ≠ f0 + 2)
    (hfresh : ∀ k < 5, f0 + k ∉ c.seenF) :
    WF sigs c (quotientScript f0 slot x z) := by
  have h0 := hfresh 0 (by omega)
  have h1 := hfresh 1 (by omega)
  have h2 := hfresh 2 (by omega)
  have h3 := hfresh 3 (by omega)
  have h4 := hfresh 4 (by omega)
  simp only [Nat.add_zero] at h0
  obtain ⟨mx, hmx⟩ := Option.isSome_iff_exists.mp hx
  obtain ⟨mz, hmz⟩ := Option.isSome_iff_exists.mp hz
  have hsig : ProgSig.ofProgram quotient = ⟨2, 1, [.never, .pub]⟩ := rfl
  have n01 : f0 + 1 ≠ f0 := by omega
  have n02 : f0 + 2 ≠ f0 := by omega
  have n12 : f0 + 2 ≠ f0 + 1 := by omega
  have n03 : f0 + 3 ≠ f0 := by omega
  have n13 : f0 + 3 ≠ f0 + 1 := by omega
  have n23 : f0 + 3 ≠ f0 + 2 := by omega
  have n04 : f0 + 4 ≠ f0 := by omega
  have n14 : f0 + 4 ≠ f0 + 1 := by omega
  have n24 : f0 + 4 ≠ f0 + 2 := by omega
  have n34 : f0 + 4 ≠ f0 + 3 := by omega
  unfold quotientScript
  refine TlsMpc.Node.Flows.Contacts.WF_seq sigs c _ _ _
    (by simp [check, InstrP.skel, InstrP.map, Ctx.defFields, Ctx.defField, h0, h1, n01, Mark.ofInput]; rfl) ?_
  have bne : ∀ a b : Nat, a ≠ b → (a == b) = false := fun a b h => by rw [beq_eq_false_iff_ne]; exact h
  refine TlsMpc.Node.Flows.Contacts.WF_seq sigs _ _ _ _
    (by simp [check, InstrP.skel, InstrP.map, Ctx.field?, Ctx.defField, h2, n12, n02, Mark.join, List.lookup_cons,
      bne f0 (f0 + 1) (by omega)]; rfl) ?_
  have lx : ∀ k, x.id ≠ k → ∀ (m : Mark) (l : List (Nat × Mark)), ((k, m) :: l).lookup x.id = l.lookup x.id :=
    fun k h m l => by simp [List.lookup_cons, bne x.id k h]
  have lz : ∀ k, z.id ≠ k → ∀ (m : Mark) (l : List (Nat × Mark)), ((k, m) :: l).lookup z.id = l.lookup z.id :=
    fun k h m l => by simp [List.lookup_cons, bne z.id k h]
  have hmx' : c.fields.lookup x.id = some mx := hmx
  have hmz' : c.fields.lookup z.id = some mz := hmz
  refine TlsMpc.Node.Flows.Contacts.WF_seq sigs _ _ _ _
    (by
      simp only [check, InstrP.skel, InstrP.map]
      simp [hp, hsig, guard, Ctx.useMasks, Ctx.field?, Ctx.dropField, Ctx.defFields, Ctx.defField, Mark.join, h3, h4,
        List.lookup_cons, bne (f0 + 2) (f0 + 1) n12, bne (f0 + 2) f0 n02, Ctx.lookup_filter_ne,
        hfx.1, hfx.2.1, hfx.2.2, hfz.1, hfz.2.1, hfz.2.2, lx f0 hfx.1, lx (f0 + 1) hfx.2.1, lx (f0 + 2) hfx.2.2,
        lz f0 hfz.1, lz (f0 + 1) hfz.2.1, lz (f0 + 2) hfz.2.2, hmx', hmz', n34, Label.maskedDenominator,
        n03, n13, n23, n04, n14, n24]
      rfl) ?_
  · refine WF.step _ _ (.elems 1) _ _
      (by simp [check, InstrP.skel, InstrP.map, Ctx.field?, Mark.openable, Label.maskedDenominator, guard]; rfl)
      (fun r hr => ?_)
    · cases r with
      | elems v =>
        simp only [Shape.Fits] at hr
        match v, hr with
        | [flag], _ =>
          simp only [quotientRest, quotientTail]
          refine TlsMpc.Node.Flows.Contacts.WF_seq sigs _ _ _ _
            (by simp [check, InstrP.skel, InstrP.map, Ctx.field?, List.lookup_cons, bne f0 (f0 + 4) (by omega),
              bne f0 (f0 + 3) (by omega), bne f0 (f0 + 1) (by omega)]; rfl) ?_
          refine TlsMpc.Node.Flows.Contacts.WF_seq sigs _ _ _ _
            (by simp [check, InstrP.skel, InstrP.map, Ctx.field?, Ctx.dropField, Ctx.lookup_filter_ne, n01,
              List.lookup_cons, bne (f0 + 1) (f0 + 4) (by omega), bne (f0 + 1) (f0 + 3) (by omega)]; rfl) ?_
          refine TlsMpc.Node.Flows.Contacts.WF_seq sigs _ _ _ _
            (by simp [check, InstrP.skel, InstrP.map, Ctx.field?, Ctx.dropField, Ctx.lookup_filter_ne, n04, n14,
              List.lookup_cons]; rfl) ?_
          exact WF.done _ _
      | _ => simp [Shape.Fits] at hr

/-! ## P-INV (b), (c) with the mask's provenance -/

/-- **The mask is uniform for an honest party**: for any contribution v of the other party,
m_H ↦ m_H + v is a bijection of F (inverse m ↦ m − v). -/
theorem mask_uniform (v : F) : (∀ a b : F, a + v = b + v → a = b) ∧ ∀ m : F, (m - v) + v = m := by
  refine ⟨fun a b h => ?_, fun m => by grind⟩
  have : a + v - v = b + v - v := by rw [h]
  grind

/-- **P-INV (c).** For z ≠ 0, m ↦ z·m is a bijection of F (`FieldDagV3.opening_bijective`): with
the uniform mask of `mask_uniform`, the opening is uniform, whatever z. (b): it is 0 iff z = 0 or
m = 0 (`opening_zero_iff`); (a): for z·m ≠ 0 the evaluator's value is x·z⁻¹ (`masked_div`). -/
theorem inv_hides (hinv : FieldInverse) (zv : F) (hz : zv ≠ 0) :
    (∀ m m' : F, zv * m = zv * m' → m = m') ∧ (∀ o : F, zv * (inverse zv * o) = o) :=
  TlsMpc.FieldDag.V3.opening_bijective hinv zv hz

end TlsMpc.Node.Flows.Inversion
