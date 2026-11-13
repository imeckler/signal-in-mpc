import TlsMpc.Node.Flows.Registry

/-!
# Op 44 (TEST): `Contacts.admitTest`, a contact's record from the export into the contact table (J23)

TEST PATH ONLY, as the legacy operation it replaces: a local-server export's contact record enters
the engines (`Session/Start.lean` `fromExport`: a contact of the export that has no stored state and
is not on the database nodes yet), and the session then gives it a key (op 36) and seals it (op 38).
Nothing changes in who may call it: the flow function `Flow.Contacts.admitTest` keeps its callers
(the export scaffolding of `Start.fromExport` and `Serve.loadJob`), its TEST marking, and its
`Secret.OwnInput.contactAdmit` row; selecting `contacts` only replaces the legacy operation by this
script (`Flows/Select.lean`).

Replaces `service_kernels.h` `admit_contact` (lines 246-249) and the dispatch of `tls_worker_v3.cpp`
op 44: `need(!closed && admitted && account.certificate.size() && record.size()==CONTACT &&
!conversations.count(id))`, then `c.record = entered(record)` (party A's private input of the 319
bytes, `input_private(ALICE, …)`; B enters nothing) and `conversations[id] = c` (no key yet).

  `admitScript n slot`: boolInput n (owner A, 8 · 319 bits, not once, not revealable, from A's store
    slot `slot`; B's payload is empty). Returns n.
  `opAdmit t id slot`: refused (abort, as the C++'s `need`) when the table already has an entry
    `id`; otherwise `admitScript` on the table's next id, and the commit enters `id` with the record
    as its state (`size` 319, one established device, kind 0) and no key. The C++'s other
    preconditions are the IO side's (`Select.lean` `contactsAdmitTest`: the account is admitted, the
    record is 319 bytes; a record of another length also fails `fill`, so the batch is never sent).

PROVED (in the same terms as ops 36-40 and 52, `ContactsTable.lean`):
  WF and the table invariant: `admitScript_wfp` (`AdmitPost`: the returned handle and its marks, the
    handles below the counter untouched, the counter past the block), `opAdmit_inv` (from `Table.Inv c t`
    the step is well formed and every leaf commits a table satisfying the invariant in the context it
    left), `opAdmit_wf`;
  `Wire.Bounded`: `opAdmit_bounded`;
  T3: `opAdmit_disclosure` (nothing is released, to either party, against any adversary),
    `opAdmit_reveals` (`admitKinds = []`), `opAdmit_viewD_kinds`;
  the honest run: `admit_honest` (two honest parties, A's slot holding the record's bits: both return
    handle n, which holds exactly the record's bits; no other handle changes) and `opAdmit_honest` (on
    the table: the committed entry's state handle holds the record).
-/

namespace TlsMpc.Node.Flows.Contacts

open TlsMpc.Node.Engine

/-- A contact's record (`service_kernels.h` CONTACT): 319 bytes. -/
def recordBytes : Nat := 319

theorem recordBytes_kinds : kindsOk [0] recordBytes := by decide

/-- **Op 44's engine part.** `slot`: party A's store slot holding the record's bits (B's is unused). -/
def admitScript (n slot : Nat) : Script BoolH :=
  seqs [.boolInput ⟨n⟩ .a (8 * recordBytes) false false slot] (.done ⟨n⟩)

theorem admitScript_eq (n slot : Nat) :
    admitScript n slot = seq (.boolInput ⟨n⟩ .a (8 * recordBytes) false false slot) (.done ⟨n⟩) := rfl

/-- **Op 44 on the contact table** (TEST). -/
def opAdmit (t : Table) (id slot : Nat) : Step BoolH :=
  match t.find? id with
  | none =>
    { script := admitScript (t.alloc 1).1 slot
      commit := fun h => (t.alloc 1).2.put id { state := some h, size := recordBytes, kinds := [0] } }
  | some _ => { script := .abort "contact admission", commit := fun _ => t }

/-! ## T3 -/

theorem admitScript_silent (n slot : Nat) : Silent (admitScript n slot) :=
  Silent.seqs (Silent.done _) _ (by simp [InstrP.label?])

theorem opAdmit_silent (t : Table) (id slot : Nat) : Silent (opAdmit t id slot).script := by
  unfold opAdmit
  split
  · exact admitScript_silent _ _
  · exact Silent.abort _

section Disclosure

variable (E : Env) (me : Party) (adv : Adversary) (σ : Store) (I : Ideal) (vD : List Release)

/-- **T3 for op 44.** Nothing is released, to either party, against any adversary. -/
theorem opAdmit_disclosure (t : Table) (id slot : Nat) :
    (withAdv E me adv (opAdmit t id slot).script σ I vD).viewD = [] ∧
      (withAdv E me adv (opAdmit t id slot).script σ I vD).viewH = [] :=
  silent_view E me adv _ (opAdmit_silent t id slot) σ I vD

/-- Op 44 declares no kind. -/
def admitKinds : List TlsMpc.Node.RevealKind := []

theorem opAdmit_reveals (t : Table) (id slot : Nat) : Reveals admitKinds (opAdmit t id slot).script :=
  (opAdmit_silent t id slot).reveals _

/-- **T3 for op 44 in the reveal list's vocabulary**: no kind (the view is empty). -/
theorem opAdmit_viewD_kinds (t : Table) (id slot : Nat) :
    ∀ r ∈ (withAdv E me adv (opAdmit t id slot).script σ I vD).viewD, ∃ k ∈ admitKinds, r.label = Label.ofKind k :=
  viewD_kinds E me adv _ _ (opAdmit_reveals t id slot) σ I vD

end Disclosure

/-! ## Well-formedness and the table invariant -/

/-- What `admitScript n` leaves: it returns handle `n`, which holds 8 · 319 private bits (not once);
the handles below `n` are as before; no id from `n + 1` on was defined. -/
def AdmitPost (c : Ctx) (n : Nat) (c' : Ctx) (h : BoolH) : Prop :=
  h = ⟨n⟩ ∧ c'.bool? ⟨n⟩ = some ⟨List.replicate (8 * recordBytes) .never, false⟩ ∧
    (∀ g : BoolH, g.id < n → c'.bool? g = c.bool? g) ∧ Fresh c' (n + 1)

theorem admitScript_wfp (sigs : Bytes → Option Sig) (c : Ctx) (n slot : Nat) (hf : Fresh c n) :
    WFP sigs (AdmitPost c n) c (admitScript n slot) := by
  rw [admitScript_eq]
  refine WFP_seq sigs c _ _ _ (TlsBase.check_boolInput sigs hf .a (8 * recordBytes) false false (by decide)) ?_
  refine WFP.done _ _ ⟨rfl, ?_, fun g hg => ?_, hf.push n (Nat.le_refl n) _⟩
  · rw [bool?_push_self]
    rfl
  · have e0 : g.id ≠ n := by omega
    simp only [bool?_push, e0, if_false]

/-- **Op 44 preserves the invariant** (and is well formed). -/
theorem opAdmit_inv (sigs : Bytes → Option Sig) (c : Ctx) (t : Table) (id slot : Nat) (hI : t.Inv c) :
    WFP sigs (fun c' h => ((opAdmit t id slot).commit h).Inv c') c (opAdmit t id slot).script := by
  unfold opAdmit
  cases hfind : t.find? id with
  | some e => exact WFP.abort _ _
  | none =>
    dsimp only
    refine (admitScript_wfp sigs c (t.alloc 1).1 slot hI.fresh).mono (fun c2 h hp => ?_)
    obtain ⟨rfl, hk2, hlow, hf2⟩ := hp
    have hold : ∀ p ∈ t.entries, p.1 ≠ id → ∀ g ∈ p.2.handles, c2.bool? g = c.bool? g :=
      fun p hp _ g hg => hlow g (hI.below p hp g hg)
    have hH : ({ state := some ⟨(t.alloc 1).1⟩, size := recordBytes, kinds := [0] } : Entry).handles =
        [⟨(t.alloc 1).1⟩] := by
      simp [Entry.handles]
    refine Table.Inv.put hI rfl (by simp) hf2 hold ?_ ?_ ?_ ?_ ?_ ?_
    · intro h hh p hp _ g hg
      rw [hH, List.mem_singleton] at hh
      subst hh
      have := hI.below p hp g hg
      simp only [Table.alloc_fst]
      omega
    · intro h hh
      rw [hH, List.mem_singleton] at hh
      subst hh
      simp
    · rw [hH]
      simp
    · intro h hh
      rw [hH, List.mem_singleton] at hh
      subst hh
      rw [hk2]
      rfl
    · intro k hk
      simp at hk
    · intro s hs
      simp only [Option.some.injEq] at hs
      subst hs
      exact ⟨hk2, recordBytes_kinds⟩

theorem opAdmit_wf (sigs : Bytes → Option Sig) (c : Ctx) (t : Table) (id slot : Nat) (hI : t.Inv c) :
    WF sigs c (opAdmit t id slot).script :=
  (opAdmit_inv sigs c t id slot hI).wf

/-- **Op 44 sends only `Wire.Bounded` instructions** (the counter below 2^64 − 1). -/
theorem opAdmit_bounded (t : Table) (id slot : Nat) (ht : t.next + 1 < B64) :
    Every Instr.Bounded (opAdmit t id slot).script := by
  have hB := Registry.big_lt_B64
  unfold opAdmit
  split
  · refine every_seqs (Every.done _) _ ?_
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    simp [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank, recordBytes]
    omega
  · exact Every.abort _

/-! ## Two honest parties -/

section Honest

variable (E : Env) (σA σB : Store)

/-- **The honest run of op 44's engine part.** Party A's slot holds the 319-byte record's bits (B's
slot is not read): both parties return handle `n`, which holds the record's bits; every other
handle is as before. -/
theorem admit_honest (I : Ideal) (n slotA slotB : Nat) (record : B8) (hr : record.length = recordBytes)
    (hσA : σA.bits slotA = bitsOf record) :
    (jointRun E (admitScript n slotA) (admitScript n slotB) σA σB I).result = some (⟨n⟩, ⟨n⟩) ∧
    (jointRun E (admitScript n slotA) (admitScript n slotB) σA σB I).ideal.bools n = some (bitsOf record) ∧
    ∀ j, j ≠ n → (jointRun E (admitScript n slotA) (admitScript n slotB) σA σB I).ideal.bools j = I.bools j := by
  have hfA : fill E.hash .a σA (.boolInput ⟨n⟩ .a (8 * recordBytes) false false slotA) =
      some (.boolInput ⟨n⟩ .a (8 * recordBytes) false false (bitsOf record)) := by
    simp [fill, hσA, hr]
  have hfB : fill E.hash .b σB (.boolInput ⟨n⟩ .a (8 * recordBytes) false false slotB) =
      some (.boolInput ⟨n⟩ .a (8 * recordBytes) false false []) := by
    simp [fill]
  have hst : idealStep E .a (.boolInput ⟨n⟩ .a (8 * recordBytes) false false (bitsOf record))
      (Wire.part (.boolInput ⟨n⟩ .a (8 * recordBytes) false false [])) I =
      some (I.setBool ⟨n⟩ (bitsOf record), none, none) := by
    simp [idealStep, hr]
  obtain ⟨r1, d1⟩ := jointRun_seq E (.boolInput ⟨n⟩ .a (8 * recordBytes) false false slotA)
    (.boolInput ⟨n⟩ .a (8 * recordBytes) false false slotB) (.done (⟨n⟩ : BoolH)) (.done (⟨n⟩ : BoolH))
    σA σB I _ _ _ rfl hfA hfB hst
  rw [admitScript_eq, admitScript_eq, r1, d1]
  refine ⟨rfl, ?_, fun j hj => ?_⟩
  · simp [jointRun, Ideal.setBool]
  · simp [jointRun, Ideal.setBool, hj]

/-- **The honest run of op 44 on the table**: a contact not in the table is entered with its record
as its state (the state handle holds the record's bits), no key, one device of kind 0. -/
theorem opAdmit_honest (I : Ideal) (t : Table) (id slotA slotB : Nat) (record : B8)
    (hr : record.length = recordBytes) (hσA : σA.bits slotA = bitsOf record) (hnew : t.find? id = none) :
    (jointRun E (opAdmit t id slotA).script (opAdmit t id slotB).script σA σB I).result = some (⟨t.next⟩, ⟨t.next⟩) ∧
    ((opAdmit t id slotA).commit ⟨t.next⟩).find? id =
      some { state := some ⟨t.next⟩, size := recordBytes, kinds := [0] } ∧
    (jointRun E (opAdmit t id slotA).script (opAdmit t id slotB).script σA σB I).ideal.bools t.next =
      some (bitsOf record) := by
  obtain ⟨h1, h2, -⟩ := admit_honest E σA σB I t.next slotA slotB record hr hσA
  simp only [opAdmit, hnew, Table.alloc_fst]
  refine ⟨h1, ?_, h2⟩
  simp [Table.put, Table.find?]

end Honest

end TlsMpc.Node.Flows.Contacts
