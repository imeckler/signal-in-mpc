import TlsMpc.Node.Engine.Model
import TlsMpc.Node.Engine.Labels

/-!
# Scripts and the reveal list: what kinds a script may release under

REORGANIZATION_PLAN.md 4.3 (the reveal list) and 5.4 (the open rule), stage S9 reconciled with
stage S6. The link between the ideal model (Engine/Model.lean) and the reveal list (`RevealKind`,
TlsMpc/Node/Types.lean; per kind its flow and bound in TlsMpc/Node/Reveal.lean).

  * `Every P s`: every instruction on every branch of script `s` satisfies `P`.
  * `Reveals ks s`: every release instruction of `s` (an opening or an exchange) carries the label
    `Label.ofKind k` of a kind `k ∈ ks`: the kinds the script DECLARES. A script flow states its
    list (e.g. `Contacts.sealKinds = [.sealedBlob]`) and proves `Reveals` structurally (no
    hypothesis on the engines, the stores or the adversary).
  * `viewD_kinds`, `viewH_kinds` (**the open rule in the reveal list's vocabulary**): in ANY run of
    such a script against ANY adversary, every release in the adversary's view (resp. the honest
    party's) is labelled `ofKind k` for a declared `k`. From the open rule `view_labels_D` /
    `view_labels_H` and T12's `trace_eq_skeletons`.
  * `kinds_of_prefix`: the same conclusion from a T3 theorem's form (the view is a prefix of a
    fixed list of releases), for flows whose T3 names the releases.
  * Combinators: `Every.bind`, `Every.mono`; `Reveals.nil` (a silent script reveals nothing),
    `Reveals.mono` (more kinds), `Reveals.append`.
  * `fill_bounded`, `nextBatch_bounded`: the Lean sender emits only `Wire.Bounded` instructions
    (every number below 2^64, so `decodeBatch_encodeBatch` applies) for every script whose
    instructions are `Instr.Bounded` (their skeletons, with empty payloads, are bounded): the
    filled payloads have the lengths the skeleton declares.

No I/O; no emitter imports this module.
-/

namespace TlsMpc.Node.Engine

open TlsMpc.Node (RevealKind)

/-! ## Every instruction on every branch -/

/-- Every instruction on every branch of the script satisfies `P`. -/
inductive Every (P : Instr → Prop) {α : Type} : Script α → Prop
  | done (a : α) : Every P (.done a)
  | abort (r : String) : Every P (.abort r)
  | step (i : Instr) (k : Reply → Script α) : P i → (∀ r, Every P (k r)) → Every P (.step i k)

namespace Every

variable {P Q : Instr → Prop} {α β : Type}

theorem mono {s : Script α} (h : Every P s) (hq : ∀ i, P i → Q i) : Every Q s := by
  induction h with
  | done a => exact .done a
  | abort r => exact .abort r
  | step i k hi _ ih => exact .step i k (hq i hi) ih

theorem bind {s : Script α} {f : α → Script β} (h : Every P s) (hf : ∀ a, Every P (f a)) :
    Every P (s.bind f) := by
  induction h with
  | done a => exact hf a
  | abort r => exact .abort r
  | step i k hi _ ih => exact .step i _ hi ih

/-- An instruction whose reply the continuation matches (`seq`-style: `unit`, otherwise abort). -/
theorem step_unit {i : Instr} {s : Script α} (hi : P i) (hs : Every P s) :
    Every P (.step i fun r => match r with
      | .unit => s
      | _ => .abort "reply shape") :=
  .step i _ hi (fun r => by cases r <;> first | exact hs | exact .abort _)

theorem exchange {len : Nat} {l : Label} {p : Payload} (hi : P (.exchange len l p)) :
    Every P (Script.exchange len l p) :=
  .step _ _ hi (fun r => by cases r <;> first | exact .done _ | exact .abort _)

theorem ensure (c : Bool) (reason : String) : Every P (Script.ensure c reason) := by
  unfold Script.ensure
  split
  · exact .done _
  · exact .abort _

/-- The skeletons a script reaches satisfy `P` (up to the skeleton). -/
theorem skeletons {s : Script α} (h : Every P s) :
    ∀ (rs : List Reply), ∀ sk ∈ s.skeletons rs, ∃ i, P i ∧ i.skel = sk := by
  induction h with
  | done a => intro rs sk hsk; simp [Script.skeletons] at hsk
  | abort r => intro rs sk hsk; simp [Script.skeletons] at hsk
  | step i k hi _ ih =>
    intro rs sk hsk
    cases rs with
    | nil =>
      simp only [Script.skeletons, List.mem_cons, List.not_mem_nil, or_false] at hsk
      exact ⟨i, hi, hsk.symm⟩
    | cons r rs =>
      simp only [Script.skeletons, List.mem_cons] at hsk
      rcases hsk with rfl | hsk
      · exact ⟨i, hi, rfl⟩
      · exact ih r rs sk hsk

end Every

/-! ## The kinds a script releases under -/

/-- The instruction is not a release, or its label is that of one of the kinds `ks`. -/
def LabelIn (ks : List RevealKind) (i : Instr) : Prop :=
  ∀ l, i.label? = some l → ∃ k ∈ ks, l = Label.ofKind k

/-- **The kinds a script declares**: every release instruction on every branch carries the label
of one of the kinds `ks`. -/
abbrev Reveals (ks : List RevealKind) {α : Type} (s : Script α) : Prop := Every (LabelIn ks) s

theorem LabelIn.of_none {ks : List RevealKind} {i : Instr} (h : i.label? = none) : LabelIn ks i := by
  intro l hl
  rw [h] at hl
  cases hl

theorem LabelIn.of_mem {ks : List RevealKind} {k : RevealKind} (hk : k ∈ ks) {i : Instr}
    (h : i.label? = some (Label.ofKind k)) : LabelIn ks i := by
  intro l hl
  rw [h] at hl
  exact ⟨k, hk, (Option.some.inj hl).symm⟩

theorem LabelIn.mono {ks ks' : List RevealKind} (h : ∀ k ∈ ks, k ∈ ks') {i : Instr} (hi : LabelIn ks i) :
    LabelIn ks' i := by
  intro l hl
  obtain ⟨k, hk, e⟩ := hi l hl
  exact ⟨k, h k hk, e⟩

namespace Reveals

variable {α β : Type}

theorem mono {ks ks' : List RevealKind} {s : Script α} (h : Reveals ks s) (hk : ∀ k ∈ ks, k ∈ ks') :
    Reveals ks' s :=
  Every.mono h (fun _ hi => hi.mono hk)

/-- A script without release instructions reveals under no kind. -/
theorem nil_of_none {s : Script α} (h : Every (fun i => i.label? = none) s) : Reveals [] s :=
  Every.mono h (fun _ hi => LabelIn.of_none hi)

theorem of_nil {ks : List RevealKind} {s : Script α} (h : Reveals [] s) : Reveals ks s :=
  h.mono (fun _ hk => by cases hk)

/-- Sequencing: the kinds of both halves. -/
theorem bind {ks ks' : List RevealKind} {s : Script α} {f : α → Script β} (h : Reveals ks s)
    (hf : ∀ a, Reveals ks' (f a)) : Reveals (ks ++ ks') (s.bind f) :=
  Every.bind (h.mono (fun _ hk => List.mem_append_left _ hk))
    (fun a => (hf a).mono (fun _ hk => List.mem_append_right _ hk))

end Reveals

/-! ## The open rule in the reveal list's vocabulary -/

section Views

variable (E : Env) (me : Party) (adv : Adversary)

/-- Every release instruction the run reached carries a declared kind's label. -/
theorem trace_labels {α : Type} (ks : List RevealKind) (s : Script α) (hs : Reveals ks s)
    (σ : Store) (I : Ideal) (vD : List Release) :
    ∀ l ∈ (withAdv E me adv s σ I vD).trace.filterMap InstrP.label?, ∃ k ∈ ks, l = Label.ofKind k := by
  intro l hl
  rw [trace_eq_skeletons, List.mem_filterMap] at hl
  obtain ⟨sk, hsk, hl⟩ := hl
  obtain ⟨i, hi, rfl⟩ := Every.skeletons hs _ sk hsk
  rw [InstrP.label?_skel] at hl
  exact hi l hl

/-- **The adversary's view in the reveal list's vocabulary.** In any run of a script that declares
the kinds `ks`, against any adversary, from any store and engine state, every release the
adversary received is labelled `Label.ofKind k` for a declared kind `k`. -/
theorem viewD_kinds {α : Type} (ks : List RevealKind) (s : Script α) (hs : Reveals ks s)
    (σ : Store) (I : Ideal) (vD : List Release) :
    ∀ r ∈ (withAdv E me adv s σ I vD).viewD, ∃ k ∈ ks, r.label = Label.ofKind k := by
  intro r hr
  exact trace_labels E me adv ks s hs σ I vD r.label
    ((view_labels_D E me adv s σ I vD).subset (List.mem_map_of_mem hr))

/-- **The honest party's view in the reveal list's vocabulary** (the same, for what it received). -/
theorem viewH_kinds {α : Type} (ks : List RevealKind) (s : Script α) (hs : Reveals ks s)
    (σ : Store) (I : Ideal) (vD : List Release) :
    ∀ r ∈ (withAdv E me adv s σ I vD).viewH, ∃ k ∈ ks, r.label = Label.ofKind k := by
  intro r hr
  exact trace_labels E me adv ks s hs σ I vD r.label
    ((view_labels_H E me adv s σ I vD).subset (List.mem_map_of_mem hr))

/-- A silent script (no release on any branch) leaves both views empty of kinds: the case `ks = []`. -/
theorem viewD_nil {α : Type} (s : Script α) (hs : Reveals [] s) (σ : Store) (I : Ideal) (vD : List Release) :
    (withAdv E me adv s σ I vD).viewD = [] := by
  cases h : (withAdv E me adv s σ I vD).viewD with
  | nil => rfl
  | cons r rest =>
    obtain ⟨k, hk, -⟩ := viewD_kinds E me adv [] s hs σ I vD r (by rw [h]; exact List.mem_cons_self ..)
    cases hk

end Views

/-- **From a T3 theorem's form.** If the view is a prefix of releases each labelled with a kind of
`ks`, every release of the view is. -/
theorem kinds_of_prefix (ks : List RevealKind) (v L : List Release) (h : v <+: L)
    (hL : ∀ r ∈ L, ∃ k ∈ ks, r.label = Label.ofKind k) : ∀ r ∈ v, ∃ k ∈ ks, r.label = Label.ofKind k :=
  fun r hr => hL r (h.subset hr)

/-! ## The Lean sender emits only bounded wire instructions -/

/-- A script instruction whose public part fits the pipe: its skeleton with empty payloads is
`Wire.Bounded` (every handle id, width, count, index, label code and public length below 2^64). -/
def Instr.Bounded (i : Instr) : Prop := i.skel.blank.Bounded

/-- **Filling keeps the bound**: the payloads `fill` puts in have the lengths the skeleton
declares (a width, the number of output handles, an exchange length), all below 2^64. -/
theorem fill_bounded (hash : Bytes → Bytes) (me : Party) (σ : Store) (i : Instr) (w : Wire)
    (h : fill hash me σ i = some w) (hb : i.Bounded) : w.Bounded := by
  have h0 : (0 : Nat) < B64 := by decide
  cases i <;> simp only [fill] at h <;> (repeat' split at h) <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp_all [Instr.Bounded, Wire.Bounded, InstrP.skel, InstrP.map, InstrP.blank] <;> exact hb.2.2.2

/-- **The wires of a batch the Lean sender builds are bounded** when the script's instructions are
(on every branch): so the batch encoding round-trips (`decodeBatch_encodeBatch`, given its length
below 2^64), and the peer decodes exactly what was sent. -/
theorem nextBatch_bounded {α : Type} (hash : Bytes → Bytes) (me : Party) (σ : Store) (s : Script α)
    (hs : Every Instr.Bounded s) : ∀ w ∈ (nextBatch hash me σ s).wires, w.Bounded := by
  induction hs with
  | done a => simp [nextBatch]
  | abort r => simp [nextBatch]
  | step i k hi _ ih =>
    intro w hw
    rcases hf : fill hash me σ i with _ | w'
    · simp [nextBatch, hf] at hw
    · have hb' := fill_bounded hash me σ i w' hf hi
      by_cases he : i.endsBatch = true
      · simp only [nextBatch, hf, he, if_true, List.mem_cons, List.not_mem_nil, or_false] at hw
        subst hw
        exact hb'
      · have he' : i.endsBatch = false := by simpa using he
        have ih' := ih .unit
        rcases hnb : nextBatch hash me σ (k .unit) with ⟨ws, rest⟩
        rw [hnb] at ih'
        cases rest with
        | aborted r => simp [nextBatch, hf, he', hnb] at hw
        | finished a =>
          simp only [nextBatch, hf, he', hnb, Bool.false_eq_true, if_false, List.mem_cons] at hw
          rcases hw with rfl | hw
          · exact hb'
          · exact ih' w hw
        | waiting i' k' =>
          simp only [nextBatch, hf, he', hnb, Bool.false_eq_true, if_false, List.mem_cons] at hw
          rcases hw with rfl | hw
          · exact hb'
          · exact ih' w hw

end TlsMpc.Node.Engine
