import TlsMpc.Node.Flows.Refresh

/-!
# `Refresh.*`: what the scripts release, ORD-2 on the table, the one-source splice

REORGANIZATION_PLAN.md stage S15 (T3, T4-REFRESH, ORD-2). No I/O; no emitter imports this module.

  * T3 (`*_reveals`, `op*_reveals`, `opEstablish_reveals`): every release instruction of every
    refresh script carries the label of `fetchKinds` (`sealedRecord`), `shapeKinds`
    (`bundleShape`), `establishKinds` (`identityChanged`, `deviceStatus`), `scratchKinds`
    (`sealedBlob`), or one of S11's kinds (the `CurveOps` parameter's own `Reveals`, a
    hypothesis). In particular no instruction opens the keys response body or anything computed
    from it other than the shape flags, the first device's `changed` byte and each device's status
    (`refresh_viewD_kinds`: against any adversary).
  * ORD-2 on the table (`*_entries`, `opCommit_entry`, `opDrop_table`): every refresh operation
    but `opCommit` leaves the contact table's entries unchanged on every result; `opDrop` leaves
    the table itself unchanged; `opCommit` changes exactly the contact's entry, and only to the
    content the scratch's seal sealed (`opCommit_entry`), and only when the scratch is complete
    and sealed for that contact.
  * The one-source splice (`slotInput_one_source`): the bytes `bundle-slot` receives are the cut of
    the body with the item spliced by `BundleSlots.splice w` and the `widths` input is
    `widthsOf w` of the SAME `w` (`slot_bits`), so `BundleSlotWhole.bundleSlot_device` applies
    with consistent inputs, and the inconsistent combination of
    `BundleSlotWhole.inconsistent_width_accepts` cannot be formed by the script.
-/

namespace TlsMpc.Node.Flows.Refresh

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open TlsMpc.Node.Flows.TlsBase
open TlsMpc.Signal.BundleResponse (Widths)

/-! ## Instructions without a label -/

/-- No instruction of the list is a release. -/
def Quiet (l : List Instr) : Prop := ∀ i ∈ l, i.label? = none

theorem Quiet.append {l₁ l₂ : List Instr} (h₁ : Quiet l₁) (h₂ : Quiet l₂) : Quiet (l₁ ++ l₂) := by
  intro i hi
  rcases List.mem_append.mp hi with h | h
  · exact h₁ i h
  · exact h₂ i h

theorem Quiet.ite (b : Bool) {l₁ l₂ : List Instr} (h₁ : Quiet l₁) (h₂ : Quiet l₂) :
    Quiet (if b then l₁ else l₂) := by
  cases b <;> assumption

theorem Quiet.nil : Quiet [] := fun _ h => by cases h

theorem quiet_frees (hs : List BoolH) : Quiet (frees hs) := Tls.none_of_frees hs

theorem quiet_slice (o h : Nat) (f : Nat × Nat) : Quiet [sliceOf o h f] := by
  intro i hi
  simp only [List.mem_singleton] at hi
  subst hi
  rfl

theorem Quiet.reveals {α : Type} {ks : List TlsMpc.Node.RevealKind} {l : List Instr} {s : Script α}
    (h : Quiet l) (hs : Reveals ks s) : Reveals ks (seqs l s) :=
  every_seqs hs l (labelIn_of_none h)

theorem quiet_slotInput (n : Nat) (body : BoolH) (total start : Nat) (w : Widths) (first last : Bool) :
    Quiet (slotInput n body total start w first last) := by
  intro i hi
  simp only [slotInput, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem quiet_kemHash (k : Nat) (key : BoolH) (slot : Nat) : Quiet (kemHashInstrs k key slot) := by
  intro i hi
  simp only [kemHashInstrs, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem quiet_kemRow (k : Nat) (key : BoolH) (r : Nat) : Quiet (kemRowInstrs k key r) := by
  intro i hi
  simp only [kemRowInstrs, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem quiet_kemFinish (k : Nat) (key : BoolH) : Quiet (kemFinishInstrs k key) := by
  refine Quiet.append ?_ (quiet_frees _)
  intro i hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl <;> rfl

/-- **The encapsulation releases nothing** (steps 2–7). -/
theorem quiet_kemBlock (k : Nat) (key : BoolH) (slot : Nat) : Quiet (kemBlock k key slot) :=
  (((((quiet_kemHash k key slot).append (quiet_kemRow k key 0)).append (quiet_kemRow k key 1)).append
    (quiet_kemRow k key 2)).append (quiet_kemRow k key 3)).append (quiet_kemFinish k key)

/-! ## T3: the kinds of each script -/

theorem fetch_reveals (n : Nat) (traffic state : BoolH) (seq frame mask : B8) (payloadAt uuidAt keyAt : Nat) :
    Reveals fetchKinds (fetchScript n traffic state seq frame mask payloadAt uuidAt keyAt) := by
  refine every_seqs (every_openThen (LabelIn.of_mem (k := .sealedRecord) (by simp [fetchKinds]) rfl)
    (fun _ => every_seqs ?_ _ (labelIn_of_none (by simp [InstrP.label?])))) _
    (labelIn_of_none (by simp [InstrP.label?]))
  split
  · exact Every.done _
  · exact Every.abort _

theorem take_reveals (n : Nat) (body : Option BoolH) (content : BoolH) (offset count : Nat) :
    Reveals [] (takeScript n body content offset count) := by
  unfold takeScript
  split
  · exact every_seqs (Every.done _) _ (labelIn_of_none (by simp [InstrP.label?]))
  · exact every_seqs (Every.done _) _ (labelIn_of_none (by simp [InstrP.label?]))

theorem shape_reveals (n : Nat) (body : BoolH) (size : Nat) : Reveals shapeKinds (shapeScript n body size) :=
  every_seqs (every_openThen (LabelIn.of_mem (k := .bundleShape) (by simp [shapeKinds]) rfl)
    (fun _ => every_seqs (Every.done _) _ (labelIn_of_none (by simp [InstrP.label?])))) _
    (labelIn_of_none (by simp [InstrP.label?]))

theorem parse_reveals (n : Nat) (body : BoolH) (total start : Nat) (w : Widths) (first last : Bool) :
    Reveals [] (parseScript n body total start w first last) := by
  unfold parseScript
  split
  · refine Quiet.reveals ?_ (Every.done _)
    refine (((((quiet_slotInput _ _ _ _ _ _ _).append ?_).append (Quiet.ite _ (quiet_slice _ _ _) Quiet.nil)).append
      ?_).append (Quiet.ite _ ?_ Quiet.nil)).append (quiet_frees _)
    · intro i hi
      simp only [sliceOf, List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> rfl
    · intro i hi
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> rfl
    · intro i hi
      simp only [List.mem_singleton] at hi
      subst hi
      rfl
  · exact Every.done _

theorem challenge_reveals (n : Nat) (fields : BoolH) (l : Lifted) : Reveals [] (challengeScript n fields l) := by
  refine Quiet.reveals ?_ (Quiet.reveals (quiet_frees _) (Every.done _))
  intro i hi
  simp only [sliceOf, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem verify_reveals (n : Nat) (state fields : BoolH) (l : Lifted) (r : BoolH × BoolH × BoolH × BoolH)
    (first : Bool) : Reveals establishKinds (verifyScript n state fields l r first) := by
  refine Quiet.reveals ?_ (Quiet.reveals (quiet_frees _) ?_)
  · intro i hi
    simp only [sliceOf, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · split
    · exact Quiet.reveals (quiet_slice _ _ _)
        (every_openThen (LabelIn.of_mem (k := .identityChanged) (by simp [establishKinds]) rfl)
          (fun _ => Quiet.reveals (quiet_frees [⟨n + 9⟩]) (Every.done _)))
    · exact Every.done _

theorem session_reveals (n : Nat) (acct : Account) (registration : Nat) (parsed : Parsed) (bound kem : BoolH)
    (ag : List BoolH) (oneTime : Bool) :
    Reveals establishKinds (sessionScript n acct registration parsed bound kem ag oneTime) := by
  refine Quiet.reveals ?_ (every_openThen (LabelIn.of_mem (k := .deviceStatus) (by simp [establishKinds]) rfl)
    (fun _ => Quiet.reveals (quiet_frees [⟨n + 17⟩]) (Every.done _)))
  refine Quiet.append (Quiet.append (Quiet.append ?_ (Quiet.ite _ (quiet_slice _ _ _) Quiet.nil)) ?_) (quiet_frees _)
  · intro i hi
    simp only [sliceOf, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro i hi
    simp only [sliceOf, List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem scratchSeal_reveals (n : Nat) (key : BoolH) (cert : Nat) (ds : List Device) (version : B8) :
    Reveals scratchKinds (scratchSealScript n key cert ds version) := by
  unfold scratchSealScript contentParts
  refine Quiet.reveals ?_ ?_
  · refine (Quiet.append ?_ ?_).append (quiet_frees _)
    · intro i hi
      simp only [List.mem_map] at hi
      obtain ⟨_, _, rfl⟩ := hi
      rfl
    · intro i hi
      simp only [List.mem_singleton] at hi
      subst hi
      rfl
  · exact Every.bind (sealScript_reveals _ _ _ _ _) (fun _ => Every.done _)

/-! ## T3 for the operations -/

/-- **S11's parameter declares its kinds** (a hypothesis: S11 proves it of its scripts). -/
structure CurveOps.Reveals (cv : CurveOps) : Prop where
  lift : ∀ c h, Engine.Reveals cv.kinds (cv.lift c h)
  check : ∀ c x y e p, Engine.Reveals cv.kinds (cv.check c x y e p)
  agree : ∀ c a b o, Engine.Reveals cv.kinds (cv.agree c a b o)

theorem mem_refresh {ks : List TlsMpc.Node.RevealKind} {k : TlsMpc.Node.RevealKind}
    (h : k ∈ [.sealedRecord, .bundleShape, .identityChanged, .deviceStatus, .sealedBlob] ∨ k ∈ ks) :
    k ∈ refreshKinds ks := by
  unfold refreshKinds
  rcases h with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ h

theorem up {α : Type} {ks ks' : List TlsMpc.Node.RevealKind} {s : Script α} (h : Reveals ks s)
    (hk : ∀ k ∈ ks, k ∈ [.sealedRecord, .bundleShape, .identityChanged, .deviceStatus, .sealedBlob]) :
    Reveals (refreshKinds ks') s :=
  h.mono (fun k hk' => mem_refresh (Or.inl (hk k hk')))

theorem refuse_reveals {ks : List TlsMpc.Node.RevealKind} (st : RState) : Reveals ks (refuse st) :=
  Quiet.reveals (quiet_frees _) (Every.done _)

theorem opTake_reveals (t : Contacts.Table) (st : RState) (content : BoolH) (offset count : Nat) :
    Reveals [] (opTake t st content offset count).script := by
  unfold opTake
  dsimp only
  split
  · exact take_reveals _ _ _ _ _
  · exact Every.abort _

theorem opDrop_reveals (t : Contacts.Table) (st : RState) : Reveals [] (opDrop t st).script :=
  Quiet.reveals (quiet_frees _) (Every.done _)

theorem opShape_reveals (t : Contacts.Table) (st : RState) (loaded : Bytes → Bool) :
    Reveals shapeKinds (opShape t st loaded).script := by
  unfold opShape
  split
  · next b size _ =>
    split
    · exact (Reveals.bind (ks' := []) (shape_reveals (t.alloc 3).1 b size) (fun f => Every.done (some f))).mono
        (by simp [shapeKinds])
    · split
      · exact Every.done _
      · exact Every.abort _
  · exact Every.abort _

theorem opFetch_reveals (t : Contacts.Table) (st : RState) (id : Nat) (traffic : BoolH) (seq frame mask : B8)
    (payloadAt uuidAt keyAt : Nat) :
    Reveals fetchKinds (opFetch t st id traffic seq frame mask payloadAt uuidAt keyAt).script := by
  unfold opFetch
  split
  · split
    · split
      · exact fetch_reveals _ _ _ _ _ _ _ _ _
      · exact Every.abort _
    · exact Every.abort _
  · exact Every.abort _

theorem opScratchSeal_reveals (t : Contacts.Table) (st : RState) (id cert : Nat) (version : B8) :
    Reveals scratchKinds (opScratchSeal t st id cert version).script := by
  unfold opScratchSeal
  split
  · split
    · split
      · exact scratchSeal_reveals _ _ _ _ _
      · exact Every.abort _
    · exact Every.abort _
  · exact Every.abort _

theorem opCommit_reveals (t : Contacts.Table) (st : RState) (id : Nat) : Reveals [] (opCommit t st id).script := by
  unfold opCommit
  split
  · split
    · exact Quiet.reveals (quiet_frees _) (Every.done _)
    · exact Every.abort _
  · exact Every.abort _

theorem step0_reveals (cv : CurveOps) (hcv : cv.Reveals) (t : Contacts.Table) (st : RState) (id : Nat)
    (state body : BoolH) (total index count start : Nat) (w : Widths) :
    Reveals (refreshKinds cv.kinds) (step0 cv t st id state body total index count start w).1 := by
  unfold step0
  dsimp only
  refine Every.bind (up (parse_reveals _ _ _ _ _ _ _) (by simp)) (fun p => ?_)
  cases p with
  | none => exact refuse_reveals st
  | some p =>
    try dsimp only
    refine Every.bind ?_ (fun l => ?_)
    · split
      · exact Every.done _
      · exact Every.bind ((hcv.lift _ _).mono (fun k hk => mem_refresh (Or.inr hk))) (fun _ => Every.done _)
    refine Every.bind (up (challenge_reveals _ _ _) (by simp)) (fun ch => ?_)
    refine Every.bind ((hcv.check _ _ _ _ _).mono (fun k hk => mem_refresh (Or.inr hk))) (fun r => ?_)
    refine Every.bind (Quiet.reveals (quiet_frees _) (up (verify_reveals _ _ _ _ _ _) ?_)) (fun _ => Every.done _)
    simp [establishKinds]

theorem opEstablish_reveals (cv : CurveOps) (hcv : cv.Reveals) (acct : Account) (t : Contacts.Table) (st : RState)
    (id registration index count step start : Nat) (w : Widths) (slot : Nat) :
    Reveals (refreshKinds cv.kinds) (opEstablish cv acct t st id registration index count step start w slot).script := by
  unfold opEstablish
  dsimp only
  split
  · split
    · split
      · split
        · split
          · exact step0_reveals cv hcv _ _ _ _ _ _ _ _ _ _
          · exact Every.abort _
        · split
          · split
            · exact Every.bind ((hcv.agree _ _ _ _).mono (fun k hk => mem_refresh (Or.inr hk)))
                (fun ag => by
                  try dsimp only
                  split <;> (try split) <;> first | exact Every.done _ | exact Every.abort _)
            · exact Quiet.reveals ((quiet_slice _ _ _).append (quiet_kemHash _ _ _)) (Every.done _)
            · exact up (Every.bind (session_reveals _ _ _ _ _ _ _ _) (fun _ => Every.done _))
                (by simp [establishKinds])
            · exact Quiet.reveals ((quiet_kemFinish _ _).append (by
                intro i hi
                simp only [List.mem_singleton] at hi
                subst hi
                rfl)) (Every.done _)
            · split
              · exact Quiet.reveals (quiet_kemRow _ _ _) (Every.done _)
              · exact Every.abort _
            · exact Every.abort _
          · exact Every.abort _
        · exact Every.abort _
      · exact Every.abort _
    · exact Every.abort _
  · exact Every.abort _

/-- **T3 for the whole refresh, against any adversary**: every release the adversary receives from
any refresh operation's script carries the label of a refresh kind or of one of S11's kinds. The
keys response body is opened only through `bundleShape` (its punctuation flags), `identityChanged`
(the first device's `changed`) and `deviceStatus` (one status per device). -/
theorem refresh_viewD_kinds (E : Env) (me : Party) (adv : Adversary) (cv : CurveOps) (hcv : cv.Reveals)
    (acct : Account) (t : Contacts.Table) (st : RState) (id registration index count step start : Nat) (w : Widths)
    (slot : Nat) (σ : Store) (I : Ideal) (vD : List Release) :
    ∀ r ∈ (withAdv E me adv (opEstablish cv acct t st id registration index count step start w slot).script σ I vD).viewD,
      ∃ k ∈ refreshKinds cv.kinds, r.label = Label.ofKind k :=
  viewD_kinds E me adv _ _ (opEstablish_reveals cv hcv acct t st id registration index count step start w slot) σ I vD

/-! ## ORD-2 on the table: only `opCommit` changes a contact's entry -/

theorem opTake_entries (t : Contacts.Table) (st : RState) (content : BoolH) (offset count : Nat) (r : BoolH) :
    ((opTake t st content offset count).commit r).1.entries = t.entries := by
  unfold opTake
  dsimp only
  split <;> rfl

/-- **A dropped scratch leaves the table unchanged** (entries and counter). -/
theorem opDrop_table (t : Contacts.Table) (st : RState) (r : Unit) : ((opDrop t st).commit r) = (t, {}) := rfl

theorem opShape_entries (t : Contacts.Table) (st : RState) (loaded : Bytes → Bool) (r : Option (List Bool)) :
    ((opShape t st loaded).commit r).1.entries = t.entries := by
  unfold opShape
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

theorem opFetch_entries (t : Contacts.Table) (st : RState) (id : Nat) (traffic : BoolH) (seq frame mask : B8)
    (payloadAt uuidAt keyAt : Nat) (r : B8 × BoolH) :
    ((opFetch t st id traffic seq frame mask payloadAt uuidAt keyAt).commit r).1.entries = t.entries := by
  unfold opFetch
  split
  · split
    · split <;> rfl
    · rfl
  · rfl

theorem opScratchSeal_entries (t : Contacts.Table) (st : RState) (id cert : Nat) (version : B8) (r : BoolH × B8) :
    ((opScratchSeal t st id cert version).commit r).1.entries = t.entries := by
  unfold opScratchSeal
  split
  · split
    · split <;> rfl
    · rfl
  · rfl

theorem opEstablish_entries (cv : CurveOps) (acct : Account) (t : Contacts.Table) (st : RState)
    (id registration index count step start : Nat) (w : Widths) (slot : Nat) (r : Status × RState) :
    ((opEstablish cv acct t st id registration index count step start w slot).commit r).1.entries = t.entries := by
  unfold opEstablish
  dsimp only
  split
  · split
    · split
      · split
        · split
          · rfl
          · rfl
        · split
          · split <;> (try split) <;> rfl
          · rfl
        · rfl
      · rfl
    · rfl
  · rfl

/-- **`opCommit` is the commit of the scratch, and nothing else**: when it does not abort it
changes exactly entry `id`, to the entry whose state is the content the scratch's seal SEALED (and
the kinds and size sealed with it); it requires the scratch to be complete (`ready`), for this
contact, and sealed. -/
theorem opCommit_entry (t : Contacts.Table) (st : RState) (id : Nat) (r : Unit)
    (h : ((opCommit t st id).commit r).1.entries ≠ t.entries) :
    ∃ e content size kinds, t.find? id = some e ∧ st.contact = some id ∧ st.sealed = some (content, size, kinds) ∧
      st.ready = true ∧
      ((opCommit t st id).commit r).1 = t.put id (committed e content size kinds st.changed) := by
  unfold opCommit at h ⊢
  split at h
  · next e c content size kinds he hc hs =>
    split at h
    · next hok =>
      obtain ⟨hr, rfl⟩ := hok
      exact ⟨e, content, size, kinds, he, hc, hs, hr, by rw [if_pos ⟨hr, rfl⟩]⟩
    · exact absurd rfl h
  · exact absurd rfl h

end TlsMpc.Node.Flows.Refresh
