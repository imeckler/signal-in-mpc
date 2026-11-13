import TlsMpc.Node.Flows.CurveWFBase

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

end TlsMpc.Node.Flows.Curve
