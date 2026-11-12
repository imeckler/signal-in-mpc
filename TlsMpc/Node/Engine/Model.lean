import TlsMpc.Node.Engine

/-!
# The ideal two-party model of the engine instruction set

REORGANIZATION_PLAN.md section 5.3 (stage S9, Lean side). The semantics the theorems of
sections 7 and 8 quantify over. No I/O; no emitter imports this module.

WHAT "IDEAL" ASSUMES. The two engines (emp-ag2pc with its patches and triple stock, and the
MP-SPDZ-based field engine), their C ABI, and the Rust shell's execution of an agreed batch are
the trusted base (NEEDS_REVIEW 1). This file assumes exactly that they behave as the functionality
`idealStep` below: every value behind a handle is the value the instruction defines from its
operands (a circuit computes its Lean definition `Circuit.eval`; field operations are those of F,
the integers mod 2^255 - 19), inputs are the inputs given, an opening delivers the true value to
the party or parties it names and nothing else reaches anyone, the MAC check passes (a failing
check is an abort, which the model does not need to distinguish), and a deviating party can do
nothing but choose its own inputs and exchange payloads, abort, or disagree (which aborts).
Nothing here is proved about the engines; their correctness and privacy are not claimed.
Commitments use a hash function `Env.hash` (SHA-256 in the node); no property of it is assumed
here. Theorems that need one say so in a hypothesis.

THE MODEL.
  A party's private input is its `Store` (Engine.lean): private bits, elements and bytes,
  including the randomness drawn before the script runs (rule 5).
  `idealStep` is one agreed instruction: from this party's filled wire instruction and the other
  party's contribution (`PeerPart`: its input bits / elements, its exchange payload) it updates
  the ideal store of handle values and says what is released to each party.
  `withAdv` runs an honest party's script against an adversary: any function from the
  adversary's view so far (and the agreed skeleton) to its contribution or an abort. The
  adversary sees the honest party's exchange payload before choosing its own (rushing: the
  control link lets a party read before it writes). Its inputs are arbitrary and independent per
  instruction, so the values it gives the two engines may be inconsistent.
  `jointRun` runs two honest parties' scripts in lockstep and aborts as soon as their skeletons
  differ.

PERMISSIVENESS (stated so that no theorem claims more than the model gives). The model does not
enforce the open marks, `once`, or handle freshness; the shell does (Engine.lean `check`). Where
the shell refuses, the model may go on. Every real run is therefore a prefix of a model run that
ends in an abort; the theorems here are about accepted results or are prefix-closed, so they
transfer to real runs.

PROVED HERE (standard axioms only):
  trace_eq_skeletons, T12_skeleton_determinism: the instructions an honest party's run reaches
  (everything the peer and the network see besides released values) are the script's skeletons
  along the replies it received, whatever the private inputs, the adversary and the engine state.
  view_labels_H, view_labels_D (the open rule, 5.4): each party's view is a list of labelled
  releases, in order, at most one per release instruction of the trace, each carrying that
  instruction's label; nothing else is released.
  honest_replay: the honest party's result and final store are a function of its own script,
  its own store, its view and the number of completed steps; so everything the other party and
  the engines influence reaches it through released values.
-/

namespace TlsMpc.Node.Engine

open TlsMpc.FieldDag (F modulus)

/-- One released value with the label of the instruction that released it. -/
structure Release where
  label : Label
  datum : Datum
  deriving DecidableEq, Repr

/-- A circuit as the model sees it: its signature and its ideal function on one copy. -/
structure Circuit where
  inWidth : Nat
  outMarks : List Mark
  eval : Bits → Bits

structure Env where
  circuits : Bytes → Option Circuit
  hash : Bytes → Bytes

/-- The signatures `check` uses, from the model's circuits. -/
def Env.sigs (E : Env) : Bytes → Option Sig :=
  fun n => (E.circuits n).map fun c => ⟨c.inWidth, c.outMarks⟩

/-- The values behind the handles (the ideal functionality's state). -/
structure Ideal where
  bools : Nat → Option Bits := fun _ => none
  fields : Nat → Option F := fun _ => none

namespace Ideal
def setBool (I : Ideal) (h : BoolH) (v : Bits) : Ideal :=
  { I with bools := fun j => if j = h.id then some v else I.bools j }
def setField (I : Ideal) (h : FieldH) (v : F) : Ideal :=
  { I with fields := fun j => if j = h.id then some v else I.fields j }
def setFields (I : Ideal) : List FieldH → List F → Ideal
  | h :: hs, v :: vs => (I.setField h v).setFields hs vs
  | _, _ => I
def dropBool (I : Ideal) (h : BoolH) : Ideal :=
  { I with bools := fun j => if j = h.id then none else I.bools j }
def dropField (I : Ideal) (h : FieldH) : Ideal :=
  { I with fields := fun j => if j = h.id then none else I.fields j }
end Ideal

/-- What the other party contributes to an agreed instruction. -/
structure PeerPart where
  bits : Bits := []
  elems : List F := []
  bytes : Bytes := []

/-- An honest party's contribution, from its filled wire instruction. -/
def Wire.part : Wire → PeerPart
  | .boolInput _ _ _ _ _ v => { bits := v }
  | .boolInputBoth _ _ _ _ _ v => { bits := v }
  | .fieldInput _ _ _ _ v => { elems := v }
  | .exchange _ _ p => { bytes := p }
  | _ => {}

/-- What a party releases before it sees the other's contribution: its exchange payload. -/
def Wire.early : Wire → Option Release
  | .exchange _ l p => some ⟨l, .bytes p⟩
  | _ => none

/-- `copies` side-by-side copies of a circuit (LeanCircuit::parallel). -/
def runCopies (c : Circuit) (copies : Nat) (v : Bits) : Bits :=
  ((List.range copies).map fun j => c.eval ((v.drop (j * c.inWidth)).take c.inWidth)).flatten

def coinsOk : FieldIn → List F → Bool
  | .coins, v => v.all (·.val < B64)
  | .elements, _ => true

/-- One agreed instruction, computed ideally, from party `me`'s point of view: `w` is `me`'s
filled instruction and `peer` the other party's contribution. Returns the new ideal state, the
release to `me` and the release to the other party; `none` is an abort. -/
def idealStep (E : Env) (me : Party) (w : Wire) (peer : PeerPart) (I : Ideal) :
    Option (Ideal × Option Release × Option Release) :=
  match w with
  | .boolInput out owner width _ _ mine =>
    let v := if owner = me then mine else peer.bits
    if v.length = width then some (I.setBool out v, none, none) else none
  | .boolInputBoth outA outB width _ _ mine =>
    let va := if me = .a then mine else peer.bits
    let vb := if me = .a then peer.bits else mine
    if va.length = width ∧ vb.length = width then some ((I.setBool outA va).setBool outB vb, none, none)
    else none
  | .boolPublic out v => some (I.setBool out v, none, none)
  | .run out name copies input =>
    match E.circuits name, I.bools input.id with
    | some c, some v =>
      if v.length = copies * c.inWidth then some (I.setBool out (runCopies c copies v), none, none) else none
    | _, _ => none
  | .concat out parts =>
    match parts.mapM (fun h => I.bools h.id) with
    | some vs => some (I.setBool out vs.flatten, none, none)
    | none => none
  | .slice out h lo hi =>
    match I.bools h.id with
    | some v => if lo ≤ hi ∧ hi ≤ v.length then some (I.setBool out ((v.drop lo).take (hi - lo)), none, none) else none
    | none => none
  | .pick out h idx =>
    match I.bools h.id with
    | some v => if idx.all (· < v.length) then some (I.setBool out (idx.map (v.getD · false)), none, none) else none
    | none => none
  | .openBool h l =>
    match I.bools h.id with
    | some v => some (I, some ⟨l, .bits v⟩, some ⟨l, .bits v⟩)
    | none => none
  | .openBoolTo h r l _ =>
    match I.bools h.id with
    | some v => if r = me then some (I, some ⟨l, .bits v⟩, none) else some (I, none, some ⟨l, .bits v⟩)
    | none => none
  | .freeBool h => some (I.dropBool h, none, none)
  | .fieldInput outsA outsB k _ mine =>
    let va := if me = .a then mine else peer.elems
    let vb := if me = .a then peer.elems else mine
    if va.length = outsA.length ∧ vb.length = outsB.length ∧ coinsOk k va = true ∧ coinsOk k vb = true then
      some ((I.setFields outsA va).setFields outsB vb, none, none)
    else none
  | .fieldPublic out v => some (I.setField out v, none, none)
  | .fieldAdd out a b =>
    match I.fields a.id, I.fields b.id with
    | some x, some y => some (I.setField out (x + y), none, none)
    | _, _ => none
  | .fieldSub out a b =>
    match I.fields a.id, I.fields b.id with
    | some x, some y => some (I.setField out (x - y), none, none)
    | _, _ => none
  | .fieldScale out a k =>
    match I.fields a.id with
    | some x => some (I.setField out (x * TlsMpc.FieldDag.ofNat k), none, none)
    | none => none
  | .fieldDivide out a k =>
    match I.fields a.id with
    | some x => if k = 0 then none else some (I.setField out (x * TlsMpc.FieldDag.inverse k), none, none)
    | none => none
  | .fieldMul outs pairs =>
    match pairs.mapM (fun p => match I.fields p.1.id, I.fields p.2.id with
        | some x, some y => some (x * y)
        | _, _ => none) with
    | some vs => if outs.length = pairs.length then some (I.setFields outs vs, none, none) else none
    | none => none
  | .fieldCheck => some (I, none, none)
  | .openField hs l =>
    match hs.mapM (fun h => I.fields h.id) with
    | some vs => some (I, some ⟨l, .elems vs⟩, some ⟨l, .elems vs⟩)
    | none => none
  | .freeField h => some (I.dropField h, none, none)
  | .exchange len l mine =>
    if peer.bytes.length = len then some (I, some ⟨l, .bytes peer.bytes⟩, some ⟨l, .bytes mine⟩) else none

/-- How a party's script and store take in what was released to it. -/
def absorb (hash : Bytes → Bytes) (me : Party) (i : Instr) (σ : Store) (toMe : Option Release) :
    Reply × Store :=
  match i, toMe with
  | .openBool .., some ⟨_, .bits v⟩ => (.bits v, σ)
  | .openField .., some ⟨_, .elems v⟩ => (.elems v, σ)
  | .openBoolTo _ _ _ dst, some ⟨_, .bits v⟩ => (.unit, σ.setBits dst v)
  | .exchange _ _ p, some ⟨_, .bytes v⟩ => (.exchanged (p.eval hash me σ) v, σ)
  | _, _ => (.unit, σ)

/-- An adversary controlling the other party: from its view so far (the honest party's exchange
payload of this step included) and the agreed skeleton, its contribution, or `none` to abort. -/
structure Adversary where
  act : List Release → Skel → Option PeerPart

/-- A run of an honest party against an adversary. `viewH` / `viewD`: what was released to the
honest party / to the adversary during the run, in order; `trace`: the instructions the honest
party's script reached; `replies`: what its continuations received. -/
structure Outcome (α : Type) where
  result : Option α
  store : Store
  ideal : Ideal
  viewH : List Release
  viewD : List Release
  trace : List Skel
  replies : List Reply

/-- Honest party `me` runs `s` with store `σ`; the adversary's view before the run is `vD`. -/
def withAdv (E : Env) (me : Party) (adv : Adversary) {α : Type} :
    Script α → Store → Ideal → List Release → Outcome α
  | .done a, σ, I, _ => ⟨some a, σ, I, [], [], [], []⟩
  | .abort _, σ, I, _ => ⟨none, σ, I, [], [], [], []⟩
  | .step i k, σ, I, vD =>
    match fill E.hash me σ i with
    | none => ⟨none, σ, I, [], [], [i.skel], []⟩
    | some w =>
      match adv.act (vD ++ w.early.toList) i.skel with
      | none => ⟨none, σ, I, [], w.early.toList, [i.skel], []⟩
      | some part =>
        match idealStep E me w part I with
        | none => ⟨none, σ, I, [], w.early.toList, [i.skel], []⟩
        | some (I', toH, toD) =>
          let rs := absorb E.hash me i σ toH
          let o := withAdv E me adv (k rs.1) rs.2 I' (vD ++ toD.toList)
          ⟨o.result, o.store, o.ideal, toH.toList ++ o.viewH, toD.toList ++ o.viewD, i.skel :: o.trace,
            rs.1 :: o.replies⟩

/-- A run of two honest parties. -/
structure Outcome2 (α β : Type) where
  result : Option (α × β)
  storeA : Store
  storeB : Store
  ideal : Ideal
  viewA : List Release
  viewB : List Release
  trace : List Skel

/-- Two honest parties in lockstep: A runs `sA` with `σA`, B runs `sB` with `σB`. -/
def jointRun (E : Env) {α β : Type} : Script α → Script β → Store → Store → Ideal → Outcome2 α β
  | .done a, .done b, σA, σB, I => ⟨some (a, b), σA, σB, I, [], [], []⟩
  | .step iA kA, .step iB kB, σA, σB, I =>
    if iA.skel = iB.skel then
      match fill E.hash .a σA iA, fill E.hash .b σB iB with
      | some wA, some wB =>
        match idealStep E .a wA wB.part I with
        | some (I', toA, toB) =>
          let rA := absorb E.hash .a iA σA toA
          let rB := absorb E.hash .b iB σB toB
          let o := jointRun E (kA rA.1) (kB rB.1) rA.2 rB.2 I'
          ⟨o.result, o.storeA, o.storeB, o.ideal, toA.toList ++ o.viewA, toB.toList ++ o.viewB,
            iA.skel :: o.trace⟩
        | none => ⟨none, σA, σB, I, [], [], [iA.skel]⟩
      | _, _ => ⟨none, σA, σB, I, [], [], [iA.skel]⟩
    else ⟨none, σA, σB, I, [], [], []⟩
  | _, _, σA, σB, I => ⟨none, σA, σB, I, [], [], []⟩

/-! ## T12: skeleton determinism -/

/-- The instructions a run reaches are the script's skeletons along the replies it received. -/
theorem trace_eq_skeletons (E : Env) (me : Party) (adv : Adversary) {α : Type} (s : Script α)
    (σ : Store) (I : Ideal) (vD : List Release) :
    (withAdv E me adv s σ I vD).trace = s.skeletons (withAdv E me adv s σ I vD).replies := by
  induction s generalizing σ I vD with
  | done a => rfl
  | abort r => rfl
  | step i k ih =>
    simp only [withAdv]
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · simp only [Script.skeletons, ih]

/-- **T12 (skeleton determinism).** For any script (a public value: Engine.lean decision D1), two
runs in which the honest party received the same replies reached the same instructions, whatever
its private inputs and randomness, the adversary, and the engines' state. A script builder
`f : P → Script α` gets this for each public argument `p`, by construction. -/
theorem T12_skeleton_determinism {α : Type} (s : Script α)
    (E₁ E₂ : Env) (me₁ me₂ : Party) (adv₁ adv₂ : Adversary) (σ₁ σ₂ : Store) (I₁ I₂ : Ideal)
    (v₁ v₂ : List Release)
    (h : (withAdv E₁ me₁ adv₁ s σ₁ I₁ v₁).replies = (withAdv E₂ me₂ adv₂ s σ₂ I₂ v₂).replies) :
    (withAdv E₁ me₁ adv₁ s σ₁ I₁ v₁).trace = (withAdv E₂ me₂ adv₂ s σ₂ I₂ v₂).trace := by
  rw [trace_eq_skeletons, trace_eq_skeletons, h]

/-! ## The open rule: views are labelled releases, nothing else -/

theorem idealStep_labels (E : Env) (me : Party) (w : Wire) (p : PeerPart) (I I' : Ideal)
    (toH toD : Option Release) (h : idealStep E me w p I = some (I', toH, toD)) :
    (∀ r, toH = some r → w.label? = some r.label) ∧ (∀ r, toD = some r → w.label? = some r.label) := by
  cases w <;> simp only [idealStep] at h <;>
    (repeat' first
      | (split at h)
      | (simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h)) <;>
    (try obtain ⟨_, rfl, rfl⟩ := h) <;>
    simp [InstrP.label?]

theorem idealStep_toH (E : Env) (me : Party) (w : Wire) (p : PeerPart) (I I' : Ideal)
    (toH toD : Option Release) (h : idealStep E me w p I = some (I', toH, toD)) :
    toH.isSome = w.releasesTo me := by
  cases w <;> simp only [idealStep] at h <;>
    (repeat' first
      | (split at h)
      | (simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h)) <;>
    (try obtain ⟨_, rfl, rfl⟩ := h) <;>
    simp_all [InstrP.releasesTo]

theorem early_label (w : Wire) (r : Release) (h : w.early = some r) : w.label? = some r.label := by
  cases w <;> simp only [Wire.early, reduceCtorEq, Option.some.injEq] at h
  subst h
  rfl

theorem sublist_step (tr : List Skel) (s : Skel) (o : Option Release) (v : List Release)
    (hs : ∀ r, o = some r → s.label? = some r.label)
    (hv : List.Sublist (v.map (·.label)) (tr.filterMap InstrP.label?)) :
    List.Sublist ((o.toList ++ v).map (·.label)) ((s :: tr).filterMap InstrP.label?) := by
  cases o with
  | none =>
    simp only [Option.toList_none, List.nil_append, List.filterMap_cons]
    split
    · exact hv
    · exact hv.cons _
  | some r =>
    simp only [Option.toList_some, List.cons_append, List.nil_append, List.map_cons, List.filterMap_cons,
      hs r rfl]
    exact hv.cons_cons _

/-- **The open rule (honest party's view).** The labels of what was released to the honest
party are, in order, a sublist of the labels of the release instructions it reached: every
released value comes from an opening or an exchange of the trace and carries its label. -/
theorem view_labels_H (E : Env) (me : Party) (adv : Adversary) {α : Type} (s : Script α)
    (σ : Store) (I : Ideal) (vD : List Release) :
    List.Sublist ((withAdv E me adv s σ I vD).viewH.map (·.label))
      ((withAdv E me adv s σ I vD).trace.filterMap InstrP.label?) := by
  induction s generalizing σ I vD with
  | done a => simp [withAdv]
  | abort r => simp [withAdv]
  | step i k ih =>
    simp only [withAdv]
    split
    · simp
    · next w hw =>
      split
      · simp
      · split
        · simp
        · next I' toH toD hst =>
          refine sublist_step _ _ _ _ (fun r hr => ?_) (ih _ _ _ _)
          rw [← fill_skel E.hash me σ i w hw, InstrP.label?_skel]
          exact (idealStep_labels E me w _ I I' toH toD hst).1 r hr

/-- **The open rule (adversary's view).** The same for what was released to the adversary. -/
theorem view_labels_D (E : Env) (me : Party) (adv : Adversary) {α : Type} (s : Script α)
    (σ : Store) (I : Ideal) (vD : List Release) :
    List.Sublist ((withAdv E me adv s σ I vD).viewD.map (·.label))
      ((withAdv E me adv s σ I vD).trace.filterMap InstrP.label?) := by
  induction s generalizing σ I vD with
  | done a => simp [withAdv]
  | abort r => simp [withAdv]
  | step i k ih =>
    simp only [withAdv]
    split
    · simp
    · next w hw =>
      have hl : ∀ r : Release, w.label? = some r.label → i.skel.label? = some r.label := by
        intro r h
        rw [← fill_skel E.hash me σ i w hw, InstrP.label?_skel]
        exact h
      have he := sublist_step [] i.skel w.early [] (fun r hr => hl r (early_label w r hr)) (by simp)
      simp only [List.append_nil] at he
      split
      · exact he
      · split
        · exact he
        · next I' toH toD hst =>
          exact sublist_step _ _ _ _ (fun r hr => hl r ((idealStep_labels E me w _ I I' toH toD hst).2 r hr))
            (ih _ _ _ _)

/-! ## The honest party learns only its view -/

/-- Re-run party `me`'s script alone, taking released values from `view` (for the instructions
that release to `me`) and stopping after `n` completed steps. -/
def replay (hash : Bytes → Bytes) (me : Party) {α : Type} :
    Script α → Store → List Release → Nat → Option α × Store
  | .done a, σ, _, _ => (some a, σ)
  | .abort _, σ, _, _ => (none, σ)
  | .step _ _, σ, _, 0 => (none, σ)
  | .step i k, σ, view, n + 1 =>
    if i.releasesTo me then
      match view with
      | r :: rest =>
        let rs := absorb hash me i σ (some r)
        replay hash me (k rs.1) rs.2 rest n
      | [] => (none, σ)
    else
      let rs := absorb hash me i σ none
      replay hash me (k rs.1) rs.2 view n

theorem replay_step_rel (hash : Bytes → Bytes) (me : Party) {α : Type} (i : Instr) (k : Reply → Script α)
    (σ : Store) (r : Release) (rest : List Release) (n : Nat) (h : i.releasesTo me = true) :
    replay hash me (.step i k) σ (r :: rest) (n + 1) =
      replay hash me (k (absorb hash me i σ (some r)).1) (absorb hash me i σ (some r)).2 rest n := by
  show (if i.releasesTo me then _ else _) = _
  rw [if_pos h]

theorem replay_step_norel (hash : Bytes → Bytes) (me : Party) {α : Type} (i : Instr) (k : Reply → Script α)
    (σ : Store) (view : List Release) (n : Nat) (h : i.releasesTo me = false) :
    replay hash me (.step i k) σ view (n + 1) =
      replay hash me (k (absorb hash me i σ none).1) (absorb hash me i σ none).2 view n := by
  cases view with
  | nil =>
    show (if i.releasesTo me then _ else _) = _
    rw [if_neg (by simp [h])]
  | cons r rest =>
    show (if i.releasesTo me then _ else _) = _
    rw [if_neg (by simp [h])]

/-- **The honest party's computation is a function of its own script, its own store and its
view.** Its result and final store are what `replay` computes from those (and the number of
steps that completed). Nothing of the other party or of the engines reaches it except the
released values. -/
theorem honest_replay (E : Env) (me : Party) (adv : Adversary) {α : Type} (s : Script α)
    (σ : Store) (I : Ideal) (vD : List Release) :
    replay E.hash me s σ (withAdv E me adv s σ I vD).viewH (withAdv E me adv s σ I vD).replies.length =
      ((withAdv E me adv s σ I vD).result, (withAdv E me adv s σ I vD).store) := by
  induction s generalizing σ I vD with
  | done a => rfl
  | abort r => rfl
  | step i k ih =>
    simp only [withAdv]
    split
    · rfl
    · next w hw =>
      split
      · rfl
      · split
        · rfl
        · next I' toH toD hst =>
          have hrel : i.releasesTo me = w.releasesTo me := by
            rw [← InstrP.releasesTo_skel, ← fill_skel E.hash me σ i w hw, InstrP.releasesTo_skel]
          have ht := idealStep_toH E me w _ I I' toH toD hst
          simp only [List.length_cons]
          cases toH with
          | none =>
            have : i.releasesTo me = false := by rw [hrel, ← ht]; rfl
            simp only [Option.toList_none, List.nil_append]
            rw [replay_step_norel _ _ _ _ _ _ _ this]
            exact ih _ _ _ _
          | some r =>
            have : i.releasesTo me = true := by rw [hrel, ← ht]; rfl
            simp only [Option.toList_some, List.cons_append, List.nil_append]
            rw [replay_step_rel _ _ _ _ _ _ _ _ this]
            exact ih _ _ _ _

end TlsMpc.Node.Engine
