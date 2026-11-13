import TlsMpc.Node.Flows.CurveWFBase
import TlsMpc.Node.Flows.CurveProofs

/-!
# The curve scripts are well formed (PROOF_GAPS F23)

Stage S11. For every script of `Flows/Curve.lean`: from any context in which no field id from
the script's first handle `f0` on was ever defined (the session's field counter is ahead,
`Counters.Ahead`), with the curve programs loaded under their V3 signatures (`WFB.CurveProgs`)
and the handles the script reads (its private inputs, tables, points) live below `f0`, every
instruction on every branch passes the shell's `check` in the context the branch has built
(`WF`; the S10 judgement, decision D14 for `program`): handles live when read, fresh when
defined, masks live `never` handles consumed once, openings only of `pub` outputs (the programs'
check outputs, `w`, `Z`, the validity bits, the quotient flags), widths within the limits.

`prepareContacts` is a `Staged` flow: `Staged.WF` asks the first script to be well formed with a
postcondition, and the second script to be well formed from every context satisfying it (the
local step changes only the store, never the shell's handle table).
-/

namespace TlsMpc.Node.Flows.Curve

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts (seq seqs checkAll WFP_seq)
open TlsMpc.Node.Flows.Run (openFieldThen)
open TlsMpc.FieldDag (F ofNat)
open WFB

/-! ## The masked quotient of many pairs -/

theorem quotFlags_eq (f n : Nat) :
    quotFlags f n = (List.range n).flatMap fun i => hs (f + 3 * n + 1 + 2 * i) 1 := by
  rw [← map_eq_flatMap_hs]
  unfold quotFlags quotFlag
  apply List.map_congr_left
  intro i _
  congr 1
  omega

theorem quotientMany_wfp (sigs : Bytes → Option Sig) {c : Ctx} {g : Nat → Option Mark} {n : Nat}
    {P : Bytes → Option ProgSig} (h : St c g n P) (hq : P Inversion.quotientName = some ⟨2, 1, [.never, .pub]⟩)
    (f slot : Nat) (pairs : List (FieldH × FieldH)) (hf : n ≤ f) (hw : pairs.length ≤ maxWidth)
    (hp : ∀ p ∈ pairs, (g p.1.id).isSome = true ∧ (g p.2.id).isSome = true ∧ p.1.id < f ∧ p.2.id < f) :
    WFP sigs (fun c' _ => Post g f (f + 5 * pairs.length) P c') c (quotientMany f slot pairs) := by
  unfold quotientMany
  dsimp only
  split
  · exact WFP.done _ _ ⟨g, h.mono (by omega), fun _ _ => rfl⟩
  · next hn =>
    obtain ⟨c1, e1, h1⟩ := st_shared sigs h f pairs.length slot hf
    obtain ⟨c2, e2, h2⟩ := st_program sigs h1 Inversion.quotientName pairs.length (pairs.flatMap fun p => [p.1, p.2])
      (f + 2 * pairs.length) pairs.length (f + 3 * pairs.length) (2 * pairs.length) Label.maskedDenominator
      ⟨2, 1, [.never, .pub]⟩ (by decide) hq (by omega) hw
      (by rw [Masks.length_flatMap_const _ 2 _ (fun _ _ => rfl)]) (by simp)
      (by simp only [List.length_cons, List.length_nil]; omega)
      (fun i hi => upd_in (by omega)) (fun x hx => by
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
        obtain ⟨p, hpm, hx⟩ := hx
        obtain ⟨a1, a2, a3, a4⟩ := hp p hpm
        rcases hx with rfl | rfl
        · rw [gone_out (by omega), upd_out (by omega)]; exact a1
        · rw [gone_out (by omega), upd_out (by omega)]; exact a2) (by omega) _ _ rfl rfl
    refine Masks.WFP_seqs sigs _ _ c c2 (checkAll_two sigs c c1 c2 _ _ e1 (checkAll_of_check sigs c1 c2 _ e2)) ?_
    refine Masks.WFP_openFieldThen sigs c2 c2 _ _ _ _ (st_open sigs h2 _ (by decide) _ fun x hx => ?_) (fun fl _ => ?_)
    · simp only [quotFlags, List.mem_map, List.mem_range] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      exact ⟨.pub, by
        rw [updL_flat _ _ pairs.length _ _ 2 rfl (by omega) j 1 _ hj (by omega) (by unfold quotFlag; dsimp only; try omega)]
        rfl, rfl⟩
    · split
      · obtain ⟨c3, e3, h3⟩ := st_free sigs (2 * pairs.length) h2 f (fun i hi => by wf_marks)
        obtain ⟨c4, e4, h4⟩ := st_freeS sigs (f + 3 * pairs.length + 1) 2 1 (by omega) pairs.length h3
          (fun i t hi ht => by wf_marks)
        rw [← quotFlags_eq] at e4
        exact Masks.WFP_seqs sigs _ _ c2 c4 (checkAll_two sigs c2 c3 c4 _ _ e3 e4)
          (WFP.done _ _ ⟨_, h4.mono (by omega), fun j hj => by wf_marks⟩)
      · exact WFP.abort _ _

/-! ## Split ECDH -/

theorem splitAgree_wf (sigs : Bytes → Option Sig) (c : Ctx) (f0 tSlot maskSlot : Nat)
    (hfresh : ∀ j, f0 ≤ j → j ∉ c.seenF) (hP : CurveProgs c.progs) :
    WF sigs c (splitAgree f0 tSlot maskSlot) := by
  suffices hh : WFP sigs (fun _ _ => True) c (splitAgree f0 tSlot maskSlot) from hh.wf
  have h0 := St.init c f0 hfresh
  obtain ⟨c1, e1, h1⟩ := st_input sigs h0 f0 2 .elements tSlot (Nat.le_refl _)
  obtain ⟨c2, e2, h2⟩ := st_program sigs h1 onCurveName 2 (hs f0 4) (f0 + 4) 0 (f0 + 4) 2 Label.curveChecks
    ⟨2, 0, marksPN 1 0⟩ (by decide) hP.onCurve (by omega) (by decide) (by rw [hs_length]; rfl) rfl
    (by rw [marksPN_length]) (fun i hi => absurd hi (Nat.not_lt_zero _))
    (fun x hx => by have := mem_hs.mp hx; wf_marks) (by omega) [] _ rfl rfl
  unfold splitAgree splitBlock
  refine Masks.WFP_seqs sigs _ _ c c2 (by
    rw [Masks.checkAll_cons sigs _ _ _ _ e1, Masks.checkAll_cons sigs c1 c1 _ _ rfl]
    exact checkAll_of_check sigs _ _ _ e2) ?_
  refine Masks.WFP_openFieldThen sigs c2 c2 _ _ _ _ (st_open sigs h2 _ (by decide) _ fun x hx => ?_) (fun z _ => ?_)
  · have := mem_hs.mp hx
    exact ⟨.pub, by
      rw [updL_flat _ _ 2 _ _ 1 (marksPN_length 1 0) rfl (x.id - (f0 + 4)) 0 _ (by omega) (by omega) (by omega),
        marksPN_getD 1 0 0 (by omega)], rfl⟩
  · split
    · obtain ⟨c3, e3, h3⟩ := st_program sigs h2 addUName 1 (hs f0 4) (f0 + 6) 0 (f0 + 6) 2 Label.curveChecks
        ⟨4, 0, marksPN 0 2⟩ (by decide) hP.addU (by omega) (by decide)
        (by rw [hs_length]; rfl) rfl (by rw [marksPN_length]) (fun i hi => absurd hi (Nat.not_lt_zero _))
        (fun x hx => by have := mem_hs.mp hx; wf_marks) (by omega) [] _ rfl rfl
      obtain ⟨c4, e4, h4⟩ := st_free sigs 6 h3 f0 (fun i hi => by by_cases hi4 : i < 4 <;> wf_marks)
      unfold splitTail
      refine Masks.WFP_seqs sigs _ _ c2 c4 (by rw [Masks.checkAll_cons sigs _ _ _ _ e3]; exact e4) ?_
      refine (Inversion.quotient_wf sigs c4 (f0 + 8) maskSlot ⟨f0 + 6⟩ ⟨f0 + 7⟩
        (by rw [h4.progs, ← h0.progs, hP.quotient]; rfl)
        (by rw [h4.marks]; dsimp only; wf_marks) (by rw [h4.marks]; dsimp only; wf_marks)
        (by dsimp only; omega) (by dsimp only; omega) (fun k _ => h4.fresh _ (by omega))).wfp
    · exact WFP.abort _ _

/-! ## X25519 agreements -/

theorem ladderIns_length (zero : FieldH) (swaps : List FieldH) (u : FieldH) (h : swaps.length = 252) :
    (ladderIns zero swaps u).length = 257 := by
  simp [ladderIns, h]

theorem agree_wf (sigs : Bytes → Option Sig) (c : Ctx) (f0 slot : Nat) (jobs : List (List FieldH × FieldH))
    (hfresh : ∀ j, f0 ≤ j → j ∉ c.seenF) (hP : CurveProgs c.progs) (hw : jobs.length ≤ maxWidth)
    (hjobs : ∀ jb ∈ jobs, (∀ x ∈ jb.1, (c.field? x).isSome = true ∧ x.id < f0) ∧
      (c.field? jb.2).isSome = true ∧ jb.2.id < f0) :
    WF sigs c (agree f0 slot jobs) := by
  suffices hh : WFP sigs (fun _ _ => True) c (agree f0 slot jobs) from hh.wf
  have h0 := St.init c f0 hfresh
  unfold agree
  dsimp only
  split
  · exact WFP.done _ _ trivial
  · split
    · next hn hall =>
      have hall' : ∀ jb ∈ jobs, jb.1.length = 252 := fun jb hj => by
        have := List.all_eq_true.mp hall jb hj
        simpa using this
      obtain ⟨c1, e1, h1⟩ := st_public1 sigs h0 f0 (ofNat 0) (Nat.le_refl _)
      obtain ⟨c2, e2, h2⟩ := st_program sigs h1 x25519Name jobs.length
        (jobs.flatMap fun j => ladderIns ⟨f0⟩ j.1 j.2) (f0 + 1) 0 (f0 + 1) (2 * jobs.length) Label.curveChecks
        ⟨257, 0, marksPN 0 2⟩ (by decide) hP.x25519 (by omega) hw
        (by rw [Masks.length_flatMap_const _ 257 _ (fun jb hj => ladderIns_length _ _ _ (hall' jb hj))]) rfl
        (by rw [marksPN_length]; omega) (fun i hi => absurd hi (Nat.not_lt_zero _))
        (fun x hx => by
          simp only [List.mem_flatMap, ladderIns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
          obtain ⟨jb, hjb, hx⟩ := hx
          obtain ⟨hs1, hs2, hs3⟩ := hjobs jb hjb
          rcases hx with ((rfl | rfl) | hx) | (rfl | rfl | rfl)
          · wf_marks
          · wf_marks
          · obtain ⟨a1, a2⟩ := hs1 x hx
            rw [gone_out (by omega), upd_out (by omega)]
            exact a1
          · wf_marks
          · wf_marks
          · rw [gone_out (by omega), upd_out (by omega)]
            exact hs2) (by omega) [] _ rfl rfl
      obtain ⟨c3, e3, h3⟩ := st_free sigs 1 h2 f0 (fun i hi => by wf_marks)
      refine Masks.WFP_seqs sigs _ _ c c3 (by
        rw [Masks.checkAll_cons sigs _ _ _ _ e1, Masks.checkAll_cons sigs _ _ _ _ e2]
        exact e3) ?_
      refine WFP.mono (quotientMany_wfp sigs h3 (by rw [← h0.progs]; exact hP.quotient) _ slot _ (by omega)
        (by simp only [List.length_map, List.length_range]; omega) fun p hp => ?_) (fun _ _ _ => trivial)
      simp only [List.mem_map, List.mem_range] at hp
      obtain ⟨j, hj, rfl⟩ := hp
      refine ⟨by dsimp only; wf_marks, by dsimp only; wf_marks, by dsimp only; omega, by dsimp only; omega⟩
    · exact WFP.abort _ _

/-! ## The offset step -/

/-- An offset state's handles are live below `lo`. -/
def StateLive (c : Ctx) (lo : Nat) (st : OffsetState) : Prop :=
  (c.field? st.initial.1).isSome = true ∧ (c.field? st.initial.2).isSome = true ∧ st.initial.1.id < lo ∧
    st.initial.2.id < lo ∧ ∀ x ∈ st.table, (c.field? x).isSome = true ∧ x.id < lo

theorem mem_stepIns (f0 : Nat) (st : OffsetState) (τ : Nat) (x : FieldH) (hx : x ∈ stepIns f0 st τ) :
    x = st.initial.1 ∨ x = st.initial.2 ∨ x ∈ st.table ∨ (f0 ≤ x.id ∧ x.id < f0 + 3) := by
  unfold stepIns windowInputs at hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap] at hx
  rcases hx with (rfl | rfl) | ⟨e, _, hx⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · right; right
    split at hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> (right; dsimp only; omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · rcases getD_mem_or st.table (entryAt e.2 e.1) ⟨f0⟩ with h | h
        · exact Or.inl h
        · rw [h]; right; dsimp only; omega
      · rcases getD_mem_or st.table (entryAt e.2 e.1 + 1) ⟨f0⟩ with h | h
        · exact Or.inl h
        · rw [h]; right; dsimp only; omega
      · right
        split <;> (dsimp only; omega)

theorem stepIns_live {G : Nat → Option Mark} (c : Ctx) (f0 : Nat) (st : OffsetState) (τ : Nat) (lo : Nat)
    (hst : StateLive c lo st) (hlo : lo ≤ f0) (hG : ∀ j, j < f0 → G j = c.field? ⟨j⟩)
    (hG3 : ∀ j, f0 ≤ j → j < f0 + 3 → (G j).isSome = true) :
    ∀ x ∈ stepIns f0 st τ, (G x.id).isSome = true := by
  intro x hx
  obtain ⟨h1, h2, h3, h4, h5⟩ := hst
  rcases mem_stepIns f0 st τ x hx with rfl | rfl | hx | hx
  · rw [hG _ (by omega)]; exact h1
  · rw [hG _ (by omega)]; exact h2
  · obtain ⟨a1, a2⟩ := h5 x hx
    rw [hG _ (by omega)]; exact a1
  · exact hG3 _ hx.1 hx.2

theorem offsetStep_wf (sigs : Bytes → Option Sig) (c : Ctx) (f0 maskSlot : Nat) (st : OffsetState) (τ : Nat)
    (hfresh : ∀ j, f0 ≤ j → j ∉ c.seenF) (hP : CurveProgs c.progs) (hst : StateLive c f0 st) :
    WF sigs c (offsetStep f0 maskSlot st τ) := by
  suffices hh : WFP sigs (fun _ _ => True) c (offsetStep f0 maskSlot st τ) from hh.wf
  have h0 := St.init c f0 hfresh
  unfold offsetStep
  split
  · exact WFP.abort _ _
  · split
    · obtain ⟨c1, e1, h1⟩ := st_publics sigs h0 f0 [ofNat 0, ofNat 1, ofNat 0 - ofNat 1] (Nat.le_refl _)
      simp only [List.length_cons, List.length_nil] at h1
      obtain ⟨c2, e2, h2⟩ := st_shared sigs h1 (f0 + 3) 128 maskSlot (by omega)
      obtain ⟨c3, e3, h3⟩ := st_program sigs h2 offsetSumName 1 (stepIns f0 st τ) (f0 + 3 + 2 * 128) 128 (f0 + 3 + 384) 1
        Label.maskedDenominator ⟨194, 128, marksPN 0 1⟩ (by decide) hP.offsetSum (by omega) (by decide)
        (by rw [stepIns_length]; rfl) rfl (by rw [marksPN_length]) (fun i hi => by wf_marks)
        (stepIns_live c f0 st τ f0 hst (Nat.le_refl _) (fun j hj => by wf_marks) (fun j hj1 hj2 => by wf_marks))
        (by omega) _ _ rfl rfl
      obtain ⟨c4, e4, h4⟩ := st_free sigs 3 h3 f0 (fun i hi => by wf_marks)
      obtain ⟨c5, e5, h5⟩ := st_free sigs (2 * 128) h4 (f0 + 3) (fun i hi => by wf_marks)
      refine Masks.WFP_seqs sigs _ _ c c5 ?_ (WFP.done _ _ trivial)
      refine checkAll_two sigs c c3 c5 _ _ (checkAll_two sigs c c2 c3 _ _ (checkAll_two sigs c c1 c2 _ _ e1 e2)
        (checkAll_of_check sigs c2 c3 _ e3)) ?_
      rw [freeFs_append]
      exact checkAll_two sigs c3 c4 c5 _ _ e4 e5
    · exact WFP.abort _ _

theorem offsetStepFast_wf (sigs : Bytes → Option Sig) (c : Ctx) (f0 slot : Nat) (st : OffsetState) (τ : Nat)
    (hfresh : ∀ j, f0 ≤ j → j ∉ c.seenF) (hP : CurveProgs c.progs) (hst : StateLive c f0 st) :
    WF sigs c (offsetStepFast f0 slot st τ) := by
  suffices hh : WFP sigs (fun _ _ => True) c (offsetStepFast f0 slot st τ) from hh.wf
  have h0 := St.init c f0 hfresh
  unfold offsetStepFast
  split
  · exact WFP.abort _ _
  · split
    · obtain ⟨c1, e1, h1⟩ := st_publics sigs h0 f0 [ofNat 0, ofNat 1, ofNat 0 - ofNat 1] (Nat.le_refl _)
      simp only [List.length_cons, List.length_nil] at h1
      obtain ⟨c2, e2, h2⟩ := st_program sigs h1 offsetSumFastName 1 (stepIns f0 st τ) (f0 + 3) 0 (f0 + 3) 2
        Label.curveChecks ⟨194, 0, marksPN 0 2⟩ (by decide) hP.offsetSumFast (by omega) (by decide)
        (by rw [stepIns_length]; rfl) rfl (by rw [marksPN_length]) (fun i hi => absurd hi (Nat.not_lt_zero _))
        (stepIns_live c f0 st τ f0 hst (Nat.le_refl _) (fun j hj => by wf_marks) (fun j hj1 hj2 => by wf_marks))
        (by omega) [] _ rfl rfl
      obtain ⟨c3, e3, h3⟩ := st_free sigs 3 h2 f0 (fun i hi => by wf_marks)
      refine Masks.WFP_seqs sigs _ _ c c3 (checkAll_two sigs c c2 c3 _ _
        (checkAll_two sigs c c1 c2 _ _ e1 (checkAll_of_check sigs c1 c2 _ e2)) e3) ?_
      refine WFP.bind (quotientMany_wfp sigs h3 hP.quotient (f0 + 5) slot _ (by omega)
        (by simp only [List.length_cons, List.length_nil]; decide)
        (fun p hp => ?_)) (fun c' r _ => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        subst hp
        exact ⟨by dsimp only; wf_marks, by dsimp only; wf_marks, by dsimp only; omega, by dsimp only; omega⟩
      · split
        · split
          · exact WFP.abort _ _
          · exact WFP.done _ _ trivial
        · exact WFP.abort _ _
    · exact WFP.abort _ _

/-! ## Signatures, torsion, shared bits -/

theorem signatures_wf (sigs : Bytes → Option Sig) (c : Ctx) (f0 maskSlot : Nat) (baseT : List FieldH)
    (jobs : List (List FieldH × List FieldH)) (hfresh : ∀ j, f0 ≤ j → j ∉ c.seenF) (hP : CurveProgs c.progs)
    (hw : jobs.length ≤ maxWidth)
    (hb : ∀ x ∈ baseT, (c.field? x).isSome = true ∧ x.id < f0)
    (hjobs : ∀ jb ∈ jobs, ∀ x ∈ jb.1 ++ jb.2, (c.field? x).isSome = true ∧ x.id < f0) :
    WF sigs c (signatures f0 maskSlot baseT jobs) := by
  suffices hh : WFP sigs (fun _ _ => True) c (signatures f0 maskSlot baseT jobs) from hh.wf
  have h0 := St.init c f0 hfresh
  unfold signatures
  dsimp only
  split
  · exact WFP.done _ _ trivial
  · split
    · next hn hall =>
      simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hall
      obtain ⟨hall, hbl⟩ := hall
      obtain ⟨c1, e1, h1⟩ := st_shared sigs h0 f0 (2 * jobs.length) maskSlot (Nat.le_refl _)
      obtain ⟨c2, e2, h2⟩ := st_program sigs h1 signatureSumName jobs.length
        (jobs.flatMap fun j => j.2.take 1 ++ j.1 ++ (j.2.drop 1).take 256 ++ baseT.take 1012 ++ j.2.drop 257)
        (f0 + 2 * (2 * jobs.length)) (2 * jobs.length) (f0 + 6 * jobs.length) (2 * jobs.length)
        Label.maskedDenominator ⟨2546, 2, marksPN 0 2⟩ (by decide) hP.signatureSum (by omega) hw
        (by
          rw [Masks.length_flatMap_const _ 2546 _ (fun jb hj => by
            obtain ⟨l1, l2⟩ := hall jb hj
            simp only [List.length_append, List.length_take, List.length_drop, l1, l2, hbl]
            omega)])
        (by show 2 * jobs.length = jobs.length * 2; omega) (by rw [marksPN_length]; omega)
        (fun i hi => by wf_marks)
        (fun x hx => by
          simp only [List.mem_flatMap, List.mem_append] at hx
          obtain ⟨jb, hjb, hx⟩ := hx
          have hj := hjobs jb hjb
          have key : (c.field? x).isSome = true ∧ x.id < f0 := by
            rcases hx with (((hx | hx) | hx) | hx) | hx
            · exact hj x (List.mem_append_right _ (List.mem_of_mem_take hx))
            · exact hj x (List.mem_append_left _ hx)
            · exact hj x (List.mem_append_right _ (List.mem_of_mem_drop (List.mem_of_mem_take hx)))
            · exact hb x (List.mem_of_mem_take hx)
            · exact hj x (List.mem_append_right _ (List.mem_of_mem_drop hx))
          rw [gone_out (by omega), upd_out (by omega)]
          exact key.1) (by omega) _ _ rfl rfl
      obtain ⟨c3, e3, h3⟩ := st_free sigs (2 * (2 * jobs.length)) h2 f0 (fun i hi => by wf_marks)
      exact Masks.WFP_seqs sigs _ _ c c3 (checkAll_two sigs c c2 c3 _ _
        (checkAll_two sigs c c1 c2 _ _ e1 (checkAll_of_check sigs c1 c2 _ e2)) e3) (WFP.done _ _ trivial)
    · exact WFP.abort _ _

theorem torsion_wf (sigs : Bytes → Option Sig) (c : Ctx) (f0 hintSlot rSlot maskSlot : Nat) (pts : List Lifted)
    (hfresh : ∀ j, f0 ≤ j → j ∉ c.seenF) (hP : CurveProgs c.progs) (hw : pts.length ≤ maxWidth)
    (hpts : ∀ l ∈ pts, (c.field? l.x).isSome = true ∧ (c.field? l.y).isSome = true ∧ l.x.id < f0 ∧ l.y.id < f0) :
    WF sigs c (torsion f0 hintSlot rSlot maskSlot pts) := by
  suffices hh : WFP sigs (fun _ _ => True) c (torsion f0 hintSlot rSlot maskSlot pts) from hh.wf
  have h0 := St.init c f0 hfresh
  unfold torsion
  dsimp only
  split
  · exact WFP.done _ _ trivial
  · next hn =>
    obtain ⟨c1, e1, h1⟩ := st_input sigs h0 f0 (2 * pts.length) .elements hintSlot (Nat.le_refl _)
    obtain ⟨c2, e2, h2⟩ := st_shared sigs h1 (f0 + 4 * pts.length) pts.length rSlot (by omega)
    obtain ⟨c3, e3, h3⟩ := st_shared sigs h2 (f0 + 4 * pts.length + 3 * pts.length) (4 * pts.length) maskSlot (by omega)
    obtain ⟨c4, e4, h4⟩ := st_program sigs h3 torsionName pts.length
      ((pts.zipIdx).flatMap fun e =>
        [e.1.x, e.1.y, ⟨f0 + 2 * e.2⟩, ⟨f0 + 2 * e.2 + 1⟩, ⟨f0 + 2 * pts.length + 2 * e.2⟩,
          ⟨f0 + 2 * pts.length + 2 * e.2 + 1⟩, ⟨f0 + 4 * pts.length + 2 * pts.length + e.2⟩])
      (f0 + 4 * pts.length + 3 * pts.length + 2 * (4 * pts.length)) (4 * pts.length)
      (f0 + 4 * pts.length + 3 * pts.length + 12 * pts.length) (2 * pts.length)
      Label.maskedDenominator ⟨7, 4, marksPN 0 2⟩ (by decide) hP.torsion (by omega) hw
      (by rw [Masks.length_flatMap_const _ 7 _ (fun _ _ => rfl), List.length_zipIdx])
      (by show 4 * pts.length = pts.length * 4; omega) (by rw [marksPN_length]; omega)
      (fun i hi => by wf_marks)
      (fun x hx => by
        simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
        obtain ⟨e, he, hx⟩ := hx
        have hlt := Masks.zipIdx_snd_lt he
        obtain ⟨a1, a2, a3, a4⟩ := hpts e.1 (List.fst_mem_of_mem_zipIdx he)
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rw [gone_out (by omega), upd_out (by omega), upd_out (by omega), upd_out (by omega)]; exact a1
        · rw [gone_out (by omega), upd_out (by omega), upd_out (by omega), upd_out (by omega)]; exact a2
        all_goals (dsimp only; wf_marks)) (by omega) _ _ rfl rfl
    have L := pts.length
    obtain ⟨c5, e5, h5⟩ := st_free sigs (4 * pts.length) h4 f0 (fun i hi => by wf_marks)
    obtain ⟨c6, e6, h6⟩ := st_free sigs (2 * pts.length) h5 (f0 + 4 * pts.length) (fun i hi => by wf_marks)
    obtain ⟨c7, e7, h7⟩ := st_free sigs pts.length h6 (f0 + 4 * pts.length + 2 * pts.length) (fun i hi => by wf_marks)
    obtain ⟨c8, e8, h8⟩ := st_free sigs (2 * (4 * pts.length)) h7 (f0 + 4 * pts.length + 3 * pts.length)
      (fun i hi => by wf_marks)
    refine Masks.WFP_seqs sigs _ _ c c8 ?_ (WFP.done _ _ trivial)
    refine checkAll_two sigs c c4 c8 _ _ (checkAll_two sigs c c3 c4 _ _ (checkAll_two sigs c c2 c3 _ _
      (checkAll_two sigs c c1 c2 _ _ (checkAll_of_check sigs c c1 _ e1) e2) e3)
      (by rw [Masks.checkAll_cons sigs c3 c3 _ _ rfl]; exact checkAll_of_check sigs c3 c4 _ e4)) ?_
    rw [freeFs_append, freeFs_append, freeFs_append]
    exact checkAll_two sigs _ _ _ _ _ (checkAll_two sigs _ _ _ _ _ (checkAll_two sigs _ _ _ _ _ e5 e6) e7) e8

theorem sharedBits_wf (sigs : Bytes → Option Sig) (c : Ctx) (f0 slot : Nat) (hfresh : ∀ j, f0 ≤ j → j ∉ c.seenF)
    (hp1 : c.progs Conv.bitCheckName = some ⟨1, 0, [.pub]⟩)
    (hp2 : c.progs Conv.bitXorName = some ⟨2, 0, [.never]⟩) :
    WF sigs c (sharedBits f0 slot) :=
  Convert.sharedBits_wf sigs c f0 251 slot (by decide) (by decide) (fun j hj _ => hfresh j hj) hp1 hp2

/-! ## Point exchanges, split ECDH key generation -/

theorem pointExchange_wfp (sigs : Bytes → Option Sig) (c : Ctx) (hash : Bytes → Bytes) (me : Party) (tag : Bytes)
    (nonce points count : Nat) (hcount : 32 + 32 * count ≤ maxExchange) :
    WFP sigs (fun c' _ => c' = c) c (pointExchange hash me tag nonce points count) := by
  unfold pointExchange
  simp only [Script.bind_eq, Script.pure_eq]
  refine WFP.bind (exchange_wfp sigs c 32 _ _ (by decide) (by decide) (by decide)) fun c1 p hc1 => ?_
  subst hc1
  obtain ⟨a, b⟩ := p
  refine WFP.bind (exchange_wfp sigs c1 _ _ _ (by decide) (by omega) hcount) fun c2 q hc2 => ?_
  subst hc2
  obtain ⟨o, o'⟩ := q
  refine WFP.bind (ensure_wfp sigs c2 _ _) fun c3 _ hc3 => ?_
  subst hc3
  repeat' split
  all_goals first | exact WFP.done _ _ rfl | exact WFP.abort _ _

theorem splitBegin_wf (sigs : Bytes → Option Sig) (c : Ctx) (hash : Bytes → Bytes) (me : Party) (nonce share : Nat) :
    WF sigs c (splitBegin hash me nonce share) := by
  unfold splitBegin
  refine (WFP.bind (R := fun _ _ => True) (pointExchange_wfp sigs c hash me splitTag nonce share 1 (by decide))
    fun c' sums _ => ?_).wf
  split
  · exact WFP.done _ _ trivial
  · exact WFP.abort _ _

/-! ## The offset preparation -/

theorem offsetPrepare_wf (sigs : Bytes → Option Sig) (c : Ctx) (hash : Bytes → Bytes) (me : Party) (f0 : Nat)
    (s : OffsetSlots) (u : FieldH) (hfresh : ∀ j, f0 ≤ j → j ∉ c.seenF) (hP : CurveProgs c.progs)
    (hu : (c.field? u).isSome = true ∧ u.id < f0) :
    WF sigs c (offsetPrepare hash me f0 s u) := by
  suffices hh : WFP sigs (fun _ _ => True) c (offsetPrepare hash me f0 s u) from hh.wf
  have h0 := St.init c f0 hfresh
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨c1, e1, h1⟩ := st_shared sigs h0 f0 1 s.r (Nat.le_refl _)
  obtain ⟨c2, e2, h2⟩ := st_input sigs h1 (f0 + 3) 252 .coins s.bits (by omega)
  obtain ⟨c3, e3, h3⟩ := st_shared sigs h2 (f0 + 3 + 504) 2031 s.masks (by omega)
  obtain ⟨c4, e4, h4⟩ := st_program sigs h3 prepareName 1 (u :: sharedOut f0 1 ++ hs (f0 + 3) 504)
    (f0 + 3 + 504 + 2 * 2031) 2031 (f0 + 3 + 504 + 3 * 2031) 1531 Label.maskedDenominator ⟨506, 2031, marksPN 505 1026⟩
    (by decide) hP.prepare (by omega) (by decide) (by simp [sharedOut, hs_length]) rfl (by rw [marksPN_length])
    (fun i hi => by wf_marks)
    (fun x hx => by
      simp only [List.mem_append, List.mem_cons, sharedOut] at hx
      rcases hx with (rfl | hx) | hx
      · wf_marks; exact hu1
      · have := mem_hs.mp hx; wf_marks
      · have := mem_hs.mp hx; wf_marks) (by omega) _ _ rfl rfl
  unfold offsetPrepare prepBlock prepOuts prepMasks
  refine Masks.WFP_seqs sigs _ _ c c4 (checkAll_two sigs c c3 c4 _ _ (checkAll_two sigs c c2 c3 _ _
    (checkAll_two sigs c c1 c2 _ _ e1 (by rw [Masks.checkAll_cons sigs c1 c2 _ _ e2]; rfl)) e3)
    (checkAll_of_check sigs c3 c4 _ e4)) ?_
  refine Masks.WFP_openFieldThen sigs c4 c4 _ _ _ _ (st_open sigs h4 _ (by decide) _ fun x hx => ?_) (fun z _ => ?_)
  · have := mem_hs.mp hx
    exact ⟨.pub, by
      rw [updL_flat _ _ 1 _ _ 1531 (marksPN_length 505 1026) rfl 0 (x.id - (f0 + 3 + 504 + 3 * 2031)) _ (by omega)
        (by omega) (by omega), marksPN_getD 505 1026 _ (by omega)], rfl⟩
  · split
    · obtain ⟨c5, e5, h5⟩ := st_free sigs (2 * 1) h4 f0 (fun i hi => by wf_marks)
      obtain ⟨c6, e6, h6⟩ := st_free sigs 1 h5 (f0 + 2 * 1) (fun i hi => by wf_marks)
      obtain ⟨c7, e7, h7⟩ := st_free sigs 504 h6 (f0 + 3) (fun i hi => by wf_marks)
      obtain ⟨c8, e8, h8⟩ := st_free sigs (2 * 2031) h7 (f0 + 507) (fun i hi => by wf_marks)
      obtain ⟨c9, e9, h9⟩ := st_free sigs 505 h8 (f0 + 3 + 504 + 3 * 2031) (fun i hi => by wf_marks)
      refine Masks.WFP_seqs sigs _ _ c4 c9 ?_ ?_
      · rw [freeFs_append, freeFs_append, freeFs_append, freeFs_append]
        exact checkAll_two sigs _ _ _ _ _ (checkAll_two sigs _ _ _ _ _ (checkAll_two sigs _ _ _ _ _
          (checkAll_two sigs _ _ _ _ _ e5 e6) e7) e8) e9
      · refine WFP.bind (R := fun _ _ => True) (pointExchange_wfp sigs c9 hash me offsetTag s.nonce s.share 1 (by decide))
          fun c' keys _ => ?_
        split
        · exact WFP.done _ _ trivial
        · exact WFP.abort _ _
    · exact WFP.abort _ _

/-! ## Agreements from tables -/

theorem agreeAffine_wfp (sigs : Bytes → Option Sig) {c : Ctx} {g : Nat → Option Mark} {n : Nat}
    {P : Bytes → Option ProgSig} (h : St c g n P) (hP : CurveProgs P) (f0 rho qslot : Nat)
    (jobs : List (List FieldH × List FieldH)) (hf : n ≤ f0) (hw : jobs.length ≤ maxWidth)
    (hjobs : ∀ jb ∈ jobs, ∀ x ∈ jb.1 ++ jb.2, (g x.id).isSome = true ∧ x.id < f0) :
    WFP sigs (fun _ _ => True) c (agreeAffine f0 rho qslot jobs) := by
  unfold agreeAffine
  dsimp only
  split
  · exact WFP.done _ _ trivial
  · split
    · next hn hall =>
      simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hall
      obtain ⟨c1, e1, h1⟩ := st_public1 sigs h f0 (ofNat 1) hf
      obtain ⟨c2, e2, h2⟩ := st_shared sigs h1 (f0 + 1) jobs.length rho (by omega)
      obtain ⟨c3, e3, h3⟩ := st_program sigs h2 affineBitSumName jobs.length
        ((jobs.zipIdx).flatMap fun e => [⟨f0⟩, ⟨f0 + 1 + 2 * jobs.length + e.2⟩] ++ e.1.2 ++ e.1.1)
        (f0 + 1 + 3 * jobs.length) 0 (f0 + 1 + 3 * jobs.length) (2 * jobs.length) Label.curveChecks
        ⟨757, 0, marksPN 0 2⟩ (by decide) hP.affineBitSum (by omega) hw
        (by
          rw [Masks.length_flatMap_const _ 757 _ (fun e he => by
            obtain ⟨l1, l2⟩ := hall e.1 (List.fst_mem_of_mem_zipIdx he)
            simp only [List.length_append, List.length_cons, List.length_nil, l1, l2]), List.length_zipIdx])
        rfl (by rw [marksPN_length]; omega) (fun i hi => absurd hi (Nat.not_lt_zero _))
        (fun x hx => by
          simp only [List.mem_flatMap, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
          obtain ⟨e, he, hx⟩ := hx
          have hlt := Masks.zipIdx_snd_lt he
          have hj := hjobs e.1 (List.fst_mem_of_mem_zipIdx he)
          rcases hx with ((rfl | rfl) | hx) | hx
          · wf_marks
          · dsimp only; wf_marks
          · obtain ⟨a1, a2⟩ := hj x (List.mem_append_right _ hx)
            wf_marks; exact a1
          · obtain ⟨a1, a2⟩ := hj x (List.mem_append_left _ hx)
            wf_marks; exact a1) (by omega) [] _ rfl rfl
      obtain ⟨c4, e4, h4⟩ := st_free sigs (2 * jobs.length + 1) h3 f0 (fun i hi => by
        by_cases hi0 : i = 0
        · subst hi0; wf_marks
        · wf_marks)
      obtain ⟨c5, e5, h5⟩ := st_free sigs jobs.length h4 (f0 + 1 + 2 * jobs.length) (fun i hi => by wf_marks)
      refine Masks.WFP_seqs sigs _ _ c c5 ?_ ?_
      · refine checkAll_two sigs c c3 c5 _ _ (checkAll_two sigs c c2 c3 _ _
          (checkAll_two sigs c c1 c2 _ _ (checkAll_of_check sigs c c1 _ e1) e2) (checkAll_of_check sigs c2 c3 _ e3)) ?_
        rw [freeFs_append, show (⟨f0⟩ :: sharedIns (f0 + 1) jobs.length : List FieldH) = hs f0 (2 * jobs.length + 1)
          from (hs_succ _ _).symm]
        exact checkAll_two sigs _ _ _ _ _ e4 e5
      · refine WFP.mono (quotientMany_wfp sigs h5 hP.quotient _ qslot _ (by omega)
          (by simp only [List.length_map, List.length_range]; omega) fun p hp => ?_) (fun _ _ _ => trivial)
        simp only [List.mem_map, List.mem_range] at hp
        obtain ⟨j, hj, rfl⟩ := hp
        refine ⟨by dsimp only; wf_marks, by dsimp only; wf_marks, by dsimp only; omega, by dsimp only; omega⟩
    · exact WFP.abort _ _

theorem agreeAffine_wf (sigs : Bytes → Option Sig) (c : Ctx) (f0 rho qslot : Nat)
    (jobs : List (List FieldH × List FieldH)) (hfresh : ∀ j, f0 ≤ j → j ∉ c.seenF) (hP : CurveProgs c.progs)
    (hw : jobs.length ≤ maxWidth)
    (hjobs : ∀ jb ∈ jobs, ∀ x ∈ jb.1 ++ jb.2, (c.field? x).isSome = true ∧ x.id < f0) :
    WF sigs c (agreeAffine f0 rho qslot jobs) :=
  (agreeAffine_wfp sigs (St.init c f0 hfresh) hP f0 rho qslot jobs (Nat.le_refl _) hw hjobs).wf

/-- A hinted agreement job's handles are live below `lo`. -/
def JobLive (c : Ctx) (lo : Nat) (jb : HintedJob) : Prop :=
  (∀ x ∈ jb.bits, (c.field? x).isSome = true ∧ x.id < lo) ∧ ((c.field? jb.valid).isSome = true ∧ jb.valid.id < lo) ∧
    ∀ t, jb.table = some t → ∀ x ∈ t, (c.field? x).isSome = true ∧ x.id < lo

theorem agreeHinted_wf (sigs : Bytes → Option Sig) (c : Ctx) (f0 rho qslot : Nat) (jobs : List HintedJob)
    (hfresh : ∀ j, f0 ≤ j → j ∉ c.seenF) (hP : CurveProgs c.progs) (hw : jobs.length ≤ maxWidth)
    (hjobs : ∀ jb ∈ jobs, JobLive c f0 jb) :
    WF sigs c (agreeHinted f0 rho qslot jobs) := by
  suffices hh : WFP sigs (fun _ _ => True) c (agreeHinted f0 rho qslot jobs) from hh.wf
  have h0 := St.init c f0 hfresh
  unfold agreeHinted
  dsimp only
  split
  · next hall =>
    simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hall
    obtain ⟨c1, e1, h1⟩ := st_public1 sigs h0 f0 (ofNat 0) (Nat.le_refl _)
    refine WFP_seq sigs c c1 _ _ e1 ?_
    split
    · exact WFP.done _ _ trivial
    · next hm0 =>
      have hmem : ∀ e ∈ jobs.filterMap (fun j => j.table.map fun t => (j, t)), e.1 ∈ jobs ∧ e.1.table = some e.2 := by
        intro e he
        simp only [List.mem_filterMap, Option.map_eq_some_iff] at he
        obtain ⟨j, hj, t, ht, rfl⟩ := he
        exact ⟨hj, ht⟩
      have hlen : (jobs.filterMap (fun j => j.table.map fun t => (j, t))).length ≤ maxWidth :=
        Nat.le_trans (List.length_filterMap_le _ _) hw
      generalize hL : jobs.filterMap (fun j => j.table.map fun t => (j, t)) = live at hall hmem hlen hm0 ⊢
      obtain ⟨c2, e2, h2⟩ := st_shared sigs h1 (f0 + 1) live.length rho (by omega)
      obtain ⟨c3, e3, h3⟩ := st_program sigs h2 bitSumName live.length
        ((live.zipIdx).flatMap fun e => [e.1.1.valid, ⟨f0 + 1 + 2 * live.length + e.2⟩] ++ (e.1.2.drop 12).take 1008 ++
          e.1.1.bits)
        (f0 + 1 + 3 * live.length) 0 (f0 + 1 + 3 * live.length) (2 * live.length) Label.curveChecks
        ⟨1261, 0, marksPN 0 2⟩ (by decide) hP.bitSum (by omega) hlen
        (by
          rw [Masks.length_flatMap_const _ 1261 _ (fun e he => by
            obtain ⟨l1, l2⟩ := hall e.1 (List.fst_mem_of_mem_zipIdx he)
            simp only [List.length_append, List.length_cons, List.length_nil, List.length_take, List.length_drop, l1, l2]
            omega), List.length_zipIdx])
        rfl (by rw [marksPN_length]; omega) (fun i hi => absurd hi (Nat.not_lt_zero _))
        (fun x hx => by
          simp only [List.mem_flatMap, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
          obtain ⟨e, he, hx⟩ := hx
          have hlt := Masks.zipIdx_snd_lt he
          obtain ⟨hj1, hj2⟩ := hmem e.1 (List.fst_mem_of_mem_zipIdx he)
          obtain ⟨b1, ⟨v1, v2⟩, t1⟩ := hjobs e.1.1 hj1
          rcases hx with ((rfl | rfl) | hx) | hx
          · wf_marks; exact v1
          · dsimp only; wf_marks
          · obtain ⟨a1, a2⟩ := t1 e.1.2 hj2 x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
            wf_marks; exact a1
          · obtain ⟨a1, a2⟩ := b1 x hx
            wf_marks; exact a1) (by omega) [] _ rfl rfl
      obtain ⟨c4, e4, h4⟩ := st_free sigs (2 * live.length) h3 (f0 + 1) (fun i hi => by wf_marks)
      obtain ⟨c5, e5, h5⟩ := st_free sigs live.length h4 (f0 + 1 + 2 * live.length) (fun i hi => by wf_marks)
      refine Masks.WFP_seqs sigs _ _ c1 c5 ?_ ?_
      · refine checkAll_two sigs c1 c3 c5 _ _ (checkAll_two sigs c1 c2 c3 _ _ e2 (checkAll_of_check sigs c2 c3 _ e3)) ?_
        rw [freeFs_append]
        exact checkAll_two sigs _ _ _ _ _ e4 e5
      · refine WFP.bind (quotientMany_wfp sigs h5 (by rw [← h0.progs]; exact hP.quotient) _ qslot _ (by omega)
          (by simp only [List.length_map, List.length_range]; omega) fun p hp => ?_) (fun _ _ _ => WFP.done _ _ trivial)
        simp only [List.mem_map, List.mem_range] at hp
        obtain ⟨j, hj, rfl⟩ := hp
        refine ⟨by dsimp only; wf_marks, by dsimp only; wf_marks, by dsimp only; omega, by dsimp only; omega⟩
  · exact WFP.abort _ _

/-! ## Bit tables -/

theorem mem_hintRow {x : FieldH} {fh m j : Nat} (hx : x ∈ hintRow fh m j) (hj : j < m) :
    fh ≤ x.id ∧ x.id < fh + 252 * m := by
  simp only [hintRow, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain ⟨w, hw, hx⟩ := hx
  rcases hx with rfl | rfl | rfl | rfl <;> (dsimp only; omega)

theorem hintRow_length (fh m j : Nat) : (hintRow fh m j).length = 252 := by
  unfold hintRow
  rw [Masks.length_flatMap_const _ 4 _ (fun _ _ => rfl), List.length_range]

theorem mem_linkSlice {x : FieldH} {fl m j : Nat} (hx : x ∈ ((sharedOut fl (126 * m)).drop (126 * j)).take 126) :
    fl + 2 * (126 * m) ≤ x.id ∧ x.id < fl + 2 * (126 * m) + 126 * m :=
  mem_hs.mp (List.mem_of_mem_drop (List.mem_of_mem_take hx))

theorem linkSlice_length (fl m j : Nat) (hj : j < m) : (((sharedOut fl (126 * m)).drop (126 * j)).take 126).length = 126 := by
  simp only [sharedOut, List.length_take, List.length_drop, hs_length]
  omega

theorem tables_wf (sigs : Bytes → Option Sig) (c : Ctx) (f0 : Nat) (s : TableSlots) (pts : List Lifted)
    (hfresh : ∀ j, f0 ≤ j → j ∉ c.seenF) (hP : CurveProgs c.progs) (hw : pts.length ≤ maxWidth)
    (hpts : ∀ l ∈ pts, (c.field? l.x).isSome = true ∧ (c.field? l.y).isSome = true ∧ l.x.id < f0 ∧ l.y.id < f0) :
    WF sigs c (tables f0 s pts) := by
  suffices hh : WFP sigs (fun _ _ => True) c (tables f0 s pts) from hh.wf
  have h0 := St.init c f0 hfresh
  unfold tables
  dsimp only
  split
  · exact WFP.done _ _ trivial
  · next hn =>
    obtain ⟨c1, e1, h1⟩ := st_input sigs h0 f0 (126 * pts.length) .elements s.hints (Nat.le_refl _)
    obtain ⟨c2, e2, h2⟩ := st_shared sigs h1 (f0 + 252 * pts.length) (126 * pts.length) s.links (by omega)
    obtain ⟨c3, e3, h3⟩ := st_shared sigs h2 (f0 + 252 * pts.length + 378 * pts.length) (252 * pts.length) s.masks
      (by omega)
    obtain ⟨c4, e4, h4⟩ := st_program sigs h3 bitTableName pts.length
      ((pts.zipIdx).flatMap fun e => [e.1.x, e.1.y] ++ hintRow f0 pts.length e.2 ++
        ((sharedOut (f0 + 252 * pts.length) (126 * pts.length)).drop (126 * e.2)).take 126)
      (f0 + 252 * pts.length + 378 * pts.length + 2 * (252 * pts.length)) (252 * pts.length)
      (f0 + 252 * pts.length + 378 * pts.length + 756 * pts.length) (1150 * pts.length) Label.maskedDenominator
      ⟨380, 252, marksPN 126 1024⟩ (by decide) hP.bitTable (by omega) hw
      (by
        rw [Masks.length_flatMap_const _ 380 _ (fun e he => by
          have := Masks.zipIdx_snd_lt he
          simp only [List.length_append, List.length_cons, List.length_nil, hintRow_length,
            linkSlice_length _ _ _ this]), List.length_zipIdx])
      (by show 252 * pts.length = pts.length * 252; omega) (by rw [marksPN_length]; omega)
      (fun i hi => by wf_marks)
      (fun x hx => by
        simp only [List.mem_flatMap, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
        obtain ⟨e, he, hx⟩ := hx
        have hlt := Masks.zipIdx_snd_lt he
        obtain ⟨a1, a2, a3, a4⟩ := hpts e.1 (List.fst_mem_of_mem_zipIdx he)
        rcases hx with ((rfl | rfl) | hx) | hx
        · wf_marks; exact a1
        · wf_marks; exact a2
        · have := mem_hintRow hx hlt; wf_marks
        · have := mem_linkSlice hx; wf_marks) (by omega) _ _ rfl rfl
    refine Masks.WFP_seqs sigs _ _ c c4 (checkAll_two sigs c c3 c4 _ _ (checkAll_two sigs c c2 c3 _ _
      (checkAll_two sigs c c1 c2 _ _ (checkAll_of_check sigs c c1 _ e1) e2) e3)
      (by rw [Masks.checkAll_cons sigs c3 c3 _ _ rfl]; exact checkAll_of_check sigs c3 c4 _ e4)) ?_
    refine Masks.WFP_openFieldThen sigs c4 c4 _ _ _ _ (st_open sigs h4 _ (by decide) _ fun x hx => ?_) (fun z _ => ?_)
    · obtain ⟨j, hj, h1, h2⟩ := mem_flatMap_hs.mp hx
      exact ⟨.pub, by
        rw [updL_flat _ _ pts.length _ _ 1150 (marksPN_length 126 1024) (by omega) j
          (x.id - (f0 + 252 * pts.length + 378 * pts.length + 756 * pts.length + 1150 * j)) _ hj (by omega) (by omega),
          marksPN_getD 126 1024 _ (by omega)], rfl⟩
    · split
      · obtain ⟨c5, e5, h5⟩ := st_free sigs (252 * pts.length) h4 f0 (fun i hi => by wf_marks)
        obtain ⟨c6, e6, h6⟩ := st_free sigs (2 * (126 * pts.length)) h5 (f0 + 252 * pts.length) (fun i hi => by wf_marks)
        obtain ⟨c7, e7, h7⟩ := st_free sigs (126 * pts.length) h6 (f0 + 252 * pts.length + 2 * (126 * pts.length))
          (fun i hi => by wf_marks)
        obtain ⟨c8, e8, h8⟩ := st_free sigs (2 * (252 * pts.length)) h7 (f0 + 252 * pts.length + 378 * pts.length)
          (fun i hi => by wf_marks)
        obtain ⟨c9, e9, h9⟩ := st_freeS sigs (f0 + 252 * pts.length + 378 * pts.length + 756 * pts.length) 1150 126
          (by omega) pts.length h8 (fun i t hi ht => by wf_marks)
        refine Masks.WFP_seqs sigs _ _ c4 c9 ?_ (WFP.done _ _ trivial)
        rw [freeFs_append, freeFs_append, freeFs_append, freeFs_append]
        exact checkAll_two sigs _ _ _ _ _ (checkAll_two sigs _ _ _ _ _ (checkAll_two sigs _ _ _ _ _
          (checkAll_two sigs _ _ _ _ _ e5 e6) e7) e8) e9
      · exact WFP.abort _ _

end TlsMpc.Node.Flows.Curve
