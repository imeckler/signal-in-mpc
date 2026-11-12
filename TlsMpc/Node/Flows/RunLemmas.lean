import TlsMpc.Node.Flows.ContactsBase

/-!
# Generic run lemmas for the S10 flows: local blocks, field openings, plain exchanges

Stage S10. Extends `Flows/ContactsBase.lean` (whose `plain` covers the Boolean plumbing and `run`)
to the field engine's local instructions, and adds the combinators the conversion scripts use. No
I/O; no emitter imports this module.

  * `isLocal`: no private input, no release, an ideal effect independent of the parties and of the
    adversary: the Boolean `plain` instructions and `fieldPublic`, `fieldAdd`, `fieldSub`,
    `fieldScale`, `fieldDivide`, `fieldMul`, `fieldCheck`, `freeField`. `runLocal`: a block's
    ideal effect.
  * `viewD_locals`, `jointRun_locals`: a local block releases nothing, against any adversary, and
    moves the ideal state by `runLocal`; for two honest parties likewise.
  * `openFieldThen` (an `openField` and its continuation): `viewD_openFieldThen`,
    `jointRun_openFieldThen`.
  * `sayThen` (an exchange of public bytes written in the script): `viewD_sayThen` (the adversary
    sees exactly those bytes, before it answers), `jointRun_sayThen`.
  * `Silent` for local blocks and `Every` for blocks.
-/

namespace TlsMpc.Node.Flows.Run

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open TlsMpc.FieldDag (F)

/-! ## Local instructions -/

def isLocal : Instr → Bool
  | .boolPublic .. => true
  | .run .. => true
  | .concat .. => true
  | .slice .. => true
  | .pick .. => true
  | .freeBool .. => true
  | .fieldPublic .. => true
  | .fieldAdd .. => true
  | .fieldSub .. => true
  | .fieldScale .. => true
  | .fieldDivide .. => true
  | .fieldMul .. => true
  | .fieldCheck => true
  | .freeField .. => true
  | _ => false

theorem fill_local (hash : Bytes → Bytes) (me : Party) (σ : Store) (i : Instr) (h : isLocal i = true) :
    fill hash me σ i = some (blankWire i) := by
  cases i <;> simp_all [isLocal, fill, blankWire]

theorem early_local (i : Instr) (h : isLocal i = true) : (blankWire i).early = none := by
  cases i <;> simp_all [isLocal, blankWire, InstrP.map, Wire.early]

theorem label_local (i : Instr) (h : isLocal i = true) : i.label? = none := by
  cases i <;> simp_all [isLocal, InstrP.label?]

/-- The ideal effect of a local instruction (`none`: the functionality aborts). -/
def localStep (E : Env) (i : Instr) (I : Ideal) : Option Ideal :=
  match idealStep E .a (blankWire i) {} I with
  | some (I', _, _) => some I'
  | none => none

theorem idealStep_local (E : Env) (me : Party) (p : PeerPart) (I : Ideal) (i : Instr) (h : isLocal i = true) :
    idealStep E me (blankWire i) p I = (localStep E i I).map fun I' => (I', none, none) := by
  cases i with
  | boolPublic out bits => simp [idealStep, localStep, blankWire, InstrP.map]
  | run out name copies input =>
    simp only [idealStep, localStep, blankWire, InstrP.map]
    cases hc : E.circuits name <;> cases hv : I.bools input.id <;> simp
    split <;> simp
  | concat out parts =>
    simp only [idealStep, localStep, blankWire, InstrP.map]
    cases hm : parts.mapM (fun h => I.bools h.id) <;> simp
  | slice out hh lo hi =>
    simp only [idealStep, localStep, blankWire, InstrP.map]
    cases hv : I.bools hh.id <;> simp
    split <;> simp
  | pick out hh idx =>
    simp only [idealStep, localStep, blankWire, InstrP.map]
    cases hv : I.bools hh.id <;> simp
    split <;> simp
  | freeBool hh => simp [idealStep, localStep, blankWire, InstrP.map]
  | fieldPublic out v => simp [idealStep, localStep, blankWire, InstrP.map]
  | fieldAdd out a b =>
    simp only [idealStep, localStep, blankWire, InstrP.map]
    cases I.fields a.id <;> cases I.fields b.id <;> simp
  | fieldSub out a b =>
    simp only [idealStep, localStep, blankWire, InstrP.map]
    cases I.fields a.id <;> cases I.fields b.id <;> simp
  | fieldScale out a k =>
    simp only [idealStep, localStep, blankWire, InstrP.map]
    cases I.fields a.id <;> simp
  | fieldDivide out a k =>
    simp only [idealStep, localStep, blankWire, InstrP.map]
    cases I.fields a.id <;> simp
    split <;> simp
  | fieldMul outs pairs =>
    simp only [idealStep, localStep, blankWire, InstrP.map]
    split <;> (try split) <;> simp_all
  | fieldCheck => simp [idealStep, localStep, blankWire, InstrP.map]
  | freeField hh => simp [idealStep, localStep, blankWire, InstrP.map]
  | _ => simp [isLocal] at h

/-- A block of local instructions, ideally. -/
def runLocal (E : Env) : List Instr → Ideal → Option Ideal
  | [], I => some I
  | i :: is, I =>
    match localStep E i I with
    | some I' => runLocal E is I'
    | none => none

theorem runLocal_append (E : Env) (is js : List Instr) (I : Ideal) :
    runLocal E (is ++ js) I = (runLocal E is I).bind (runLocal E js) := by
  induction is generalizing I with
  | nil => rfl
  | cons i is ih =>
    simp only [List.cons_append, runLocal]
    cases localStep E i I with
    | none => rfl
    | some I' => exact ih I'

/-! ## Against an adversary -/

section Adv

variable (E : Env) (me : Party) (adv : Adversary)

/-- **A local block releases nothing.** If the rest of the run, from the ideal state the block
produces, releases at most `L` to the adversary, so does the whole run. -/
theorem viewD_locals {α : Type} (s : Script α) (σ : Store) (L : List Release) :
    ∀ (is : List Instr), (∀ i ∈ is, isLocal i = true) → ∀ (I : Ideal) (vD : List Release),
    (∀ I', runLocal E is I = some I' → (withAdv E me adv s σ I' vD).viewD <+: L) →
    (withAdv E me adv (seqs is s) σ I vD).viewD <+: L
  | [], _, I, vD, h => h I rfl
  | i :: is, hp, I, vD, h => by
    have hi := hp i (by simp)
    show (withAdv E me adv (seq i (seqs is s)) σ I vD).viewD <+: L
    simp only [seq, withAdv, fill_local _ _ _ i hi, early_local i hi, Option.toList_none, List.append_nil]
    split
    · exact List.nil_prefix
    · rw [idealStep_local E me _ I i hi]
      cases hs : localStep E i I with
      | none => exact List.nil_prefix
      | some I' =>
        simp only [Option.map_some, absorb_none, Option.toList_none, List.nil_append, List.append_nil]
        exact viewD_locals s σ L is (fun j hj => hp j (by simp [hj])) I' vD
          (fun I'' h'' => h I'' (by simp [runLocal, hs, h'']))

/-- The result of a run through a local block is a result of the rest, from the block's state. -/
theorem result_locals {α : Type} (s : Script α) (σ : Store) :
    ∀ (is : List Instr), (∀ i ∈ is, isLocal i = true) → ∀ (I : Ideal) (vD : List Release) (x : α),
    (withAdv E me adv (seqs is s) σ I vD).result = some x →
    ∃ I', runLocal E is I = some I' ∧ (withAdv E me adv s σ I' vD).result = some x
  | [], _, I, vD, x, h => ⟨I, rfl, h⟩
  | i :: is, hp, I, vD, x, h => by
    have hi := hp i (by simp)
    change (withAdv E me adv (seq i (seqs is s)) σ I vD).result = some x at h
    simp only [seq, withAdv, fill_local _ _ _ i hi, early_local i hi, Option.toList_none,
      List.append_nil] at h ⊢
    revert h
    split
    · simp
    · rw [idealStep_local E me _ I i hi]
      cases hs : localStep E i I with
      | none => simp
      | some I' =>
        simp only [Option.map_some, absorb_none, Option.toList_none, List.nil_append, List.append_nil]
        intro h
        obtain ⟨I'', h1, h2⟩ := result_locals s σ is (fun j hj => hp j (by simp [hj])) I' vD x h
        exact ⟨I'', by simp [runLocal, hs, h1], h2⟩

end Adv

/-! ## Two honest parties -/

theorem jointRun_locals (E : Env) {α β : Type} (sA : Script α) (sB : Script β) (σA σB : Store) :
    ∀ (is : List Instr), (∀ i ∈ is, isLocal i = true) → ∀ (I I' : Ideal), runLocal E is I = some I' →
    (jointRun E (seqs is sA) (seqs is sB) σA σB I).result = (jointRun E sA sB σA σB I').result ∧
    (jointRun E (seqs is sA) (seqs is sB) σA σB I).ideal = (jointRun E sA sB σA σB I').ideal
  | [], _, I, I', h => by
    simp only [runLocal, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  | i :: is, hp, I, I', h => by
    have hi := hp i (by simp)
    simp only [runLocal] at h
    cases hs : localStep E i I with
    | none => rw [hs] at h; cases h
    | some I1 =>
      rw [hs] at h
      have ih := jointRun_locals E sA sB σA σB is (fun j hj => hp j (by simp [hj])) I1 I' h
      show (jointRun E (seq i (seqs is sA)) (seq i (seqs is sB)) σA σB I).result = _ ∧
        (jointRun E (seq i (seqs is sA)) (seq i (seqs is sB)) σA σB I).ideal = _
      simp only [seq, jointRun, if_true, fill_local _ _ _ i hi, idealStep_local E .a _ I i hi, hs,
        Option.map_some, absorb_none]
      exact ih

/-! ## Silence and `Every` for blocks -/

theorem silent_locals {α : Type} {s : Script α} (hs : Silent s) (is : List Instr)
    (h : ∀ i ∈ is, isLocal i = true) : Silent (seqs is s) :=
  Silent.seqs hs is (fun i hi => label_local i (h i hi))

/-! ## Field openings -/

/-- Open the field handles `hs` to both parties with label `l`, then continue with the values. -/
def openFieldThen {α : Type} (hs : List FieldH) (l : Label) (k : List F → Script α) : Script α :=
  .step (.openField hs l) fun
    | .elems v => k v
    | _ => .abort "reply shape"

theorem every_openFieldThen {α : Type} {P : Instr → Prop} {hs : List FieldH} {l : Label} {k : List F → Script α}
    (hi : P (.openField hs l)) (hk : ∀ v, Every P (k v)) : Every P (openFieldThen hs l k) :=
  Every.step _ _ hi (fun r => by cases r <;> first | exact hk _ | exact Every.abort _)

theorem viewD_openFieldThen (E : Env) (me : Party) (adv : Adversary) {α : Type} (hs : List FieldH) (l : Label)
    (k : List F → Script α) (σ : Store) (I : Ideal) (vD : List Release) (v : List F) (L : List Release)
    (hv : hs.mapM (fun h => I.fields h.id) = some v)
    (hk : (withAdv E me adv (k v) σ I (vD ++ [⟨l, .elems v⟩])).viewD <+: L) :
    (withAdv E me adv (openFieldThen hs l k) σ I vD).viewD <+: ⟨l, .elems v⟩ :: L := by
  simp only [openFieldThen, withAdv, fill, InstrP.map, Wire.early, Option.toList_none, List.append_nil]
  split
  · exact List.nil_prefix
  · simp only [idealStep, hv, absorb, Option.toList_some, List.cons_append, List.nil_append]
    exact List.cons_prefix_cons.mpr ⟨rfl, hk⟩

theorem jointRun_openFieldThen (E : Env) {α β : Type} (hs : List FieldH) (l : Label) (kA : List F → Script α)
    (kB : List F → Script β) (σA σB : Store) (I : Ideal) (v : List F)
    (hv : hs.mapM (fun h => I.fields h.id) = some v) :
    (jointRun E (openFieldThen hs l kA) (openFieldThen hs l kB) σA σB I).result = (jointRun E (kA v) (kB v) σA σB I).result ∧
    (jointRun E (openFieldThen hs l kA) (openFieldThen hs l kB) σA σB I).ideal = (jointRun E (kA v) (kB v) σA σB I).ideal := by
  simp [openFieldThen, jointRun, fill, InstrP.map, idealStep, hv, absorb]

/-! ## Exchanges of public bytes -/

/-- Send the public bytes `b` (length `len`), receive the peer's `len` bytes, continue with them. -/
def sayThen {α : Type} (len : Nat) (l : Label) (b : Bytes) (k : Bytes → Script α) : Script α :=
  .step (.exchange len l (.plain b)) fun
    | .exchanged _ r => k r
    | _ => .abort "reply shape"

theorem every_sayThen {α : Type} {P : Instr → Prop} {len : Nat} {l : Label} {b : Bytes} {k : Bytes → Script α}
    (hi : P (.exchange len l (.plain b))) (hk : ∀ r, Every P (k r)) : Every P (sayThen len l b k) :=
  Every.step _ _ hi (fun r => by cases r <;> first | exact hk _ | exact Every.abort _)

/-- **A plain exchange releases its bytes to the adversary** (before the adversary answers), and
nothing else; the honest party continues with the adversary's answer. -/
theorem viewD_sayThen (E : Env) (me : Party) (adv : Adversary) {α : Type} (len : Nat) (l : Label) (b : Bytes)
    (k : Bytes → Script α) (σ : Store) (I : Ideal) (vD : List Release) (L : List Release) (hb : b.length = len)
    (hk : ∀ r, (withAdv E me adv (k r) σ I (vD ++ [⟨l, .bytes b⟩])).viewD <+: L) :
    (withAdv E me adv (sayThen len l b k) σ I vD).viewD <+: ⟨l, .bytes b⟩ :: L := by
  simp only [sayThen, withAdv, fill, Payload.eval, hb, if_true, Wire.early, Option.toList_some]
  split
  · simp
  · split
    · simp
    · next I' toH toD hst =>
      simp only [idealStep] at hst
      split at hst
      · simp only [Option.some.injEq, Prod.mk.injEq] at hst
        obtain ⟨rfl, rfl, rfl⟩ := hst
        simp only [absorb, Payload.eval, Option.toList_some, List.cons_append, List.nil_append]
        exact List.cons_prefix_cons.mpr ⟨rfl, hk _⟩
      · cases hst

theorem jointRun_sayThen (E : Env) {α β : Type} (len : Nat) (l : Label) (bA bB : Bytes)
    (kA : Bytes → Script α) (kB : Bytes → Script β) (σA σB : Store) (I : Ideal)
    (hA : bA.length = len) (hB : bB.length = len) :
    (jointRun E (sayThen len l bA kA) (sayThen len l bB kB) σA σB I).result = (jointRun E (kA bB) (kB bA) σA σB I).result ∧
    (jointRun E (sayThen len l bA kA) (sayThen len l bB kB) σA σB I).ideal = (jointRun E (kA bB) (kB bA) σA σB I).ideal := by
  simp [sayThen, jointRun, fill, InstrP.map, InstrP.skel, Payload.eval, hA, hB, idealStep, Wire.part, absorb]

end TlsMpc.Node.Flows.Run
