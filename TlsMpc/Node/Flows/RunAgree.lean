import TlsMpc.Node.Flows.RunLemmas
import TlsMpc.Node.Flows.Challenge

/-!
# Two runs of one script that the other party cannot tell apart (plan 7.0, in the model)

Stage S10. The tool behind the hiding theorems that are about a whole script (`Masks.generate_hides`).
Plan 7.0 states hiding as re-randomisation: for the honest party's randomness ρ and σ ρ, every value
released is the same. In the model of `Engine/Model.lean` an adversary is a function of its view so
far (and the agreed skeleton), so two runs of the same script against the same adversary stay in
lockstep exactly as long as every release is equal: the adversary then makes the same contributions
in both, the honest party receives the same replies, and its script takes the same branch.

`Agree Q o o'` says this of two finished runs: equal views of BOTH parties (so the honest party's
public behaviour, a function of its replies, is the same too), equal traces (the instructions
reached, aborts included), equal replies, equal results, and `Q` of the two final states when the
runs returned. It is proved step by step:

  * `Agree.step`: one instruction, for the contribution the adversary actually makes;
  * `Agree.bind`: composition (the second halves start from the same adversary view);
  * `Agree.locals`, `Agree.openFieldThen`, `Agree.openThen`, `Agree.program`,
    `Agree.boolInputBoth`, `Agree.fieldInput`: the combinators of the S10 scripts. An opening
    needs the SAME opened value in both runs; an input lets the two stores differ;
  * `agree_joint`: `Random.joint` reads only the nonce and the value of the byte store, so two
    stores that agree there give the same run (and it leaves the engines' states as they were).

No I/O; no emitter imports this module.
-/

namespace TlsMpc.Node.Flows.Run

open TlsMpc.Node.Engine
open TlsMpc.Node.Flows.Contacts
open TlsMpc.FieldDag (F)

/-- Two runs with the same views, trace, replies and result; `Q` relates the final stores and
engine states when they returned. -/
structure Agree {α : Type} (Q : α → Store → Ideal → Store → Ideal → Prop) (o o' : Outcome α) : Prop where
  viewD : o.viewD = o'.viewD
  viewH : o.viewH = o'.viewH
  trace : o.trace = o'.trace
  replies : o.replies = o'.replies
  result : o.result = o'.result
  post : ∀ a, o.result = some a → Q a o.store o.ideal o'.store o'.ideal

section

variable (E : Env) (me : Party) (adv : Adversary)

theorem Agree.done {α : Type} {Q : α → Store → Ideal → Store → Ideal → Prop} (a : α) (σ σ' : Store)
    (I I' : Ideal) (vD : List Release) (h : Q a σ I σ' I') :
    Agree Q (withAdv E me adv (.done a) σ I vD) (withAdv E me adv (.done a) σ' I' vD) :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun x hx => by
    simp only [withAdv, Option.some.injEq] at hx
    subst hx
    exact h⟩

theorem Agree.abort {α : Type} {Q : α → Store → Ideal → Store → Ideal → Prop} (r : String) (σ σ' : Store)
    (I I' : Ideal) (vD : List Release) :
    Agree Q (withAdv E me adv (.abort r : Script α) σ I vD) (withAdv E me adv (.abort r) σ' I' vD) :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun x hx => by simp [withAdv] at hx⟩

theorem Agree.mono {α : Type} {Q Q' : α → Store → Ideal → Store → Ideal → Prop} {o o' : Outcome α}
    (h : Agree Q o o') (hq : ∀ a s i s' i', Q a s i s' i' → Q' a s i s' i') : Agree Q' o o' :=
  ⟨h.viewD, h.viewH, h.trace, h.replies, h.result, fun a ha => hq _ _ _ _ _ (h.post a ha)⟩

/-- **Composition.** If the runs of `s` agree, and the runs of `f a` agree from the states `s`
left (for the result `a` the first run returned, when it did), the runs of `s.bind f` agree. -/
theorem Agree.bind {α β : Type} {Q : α → Store → Ideal → Store → Ideal → Prop}
    {R : β → Store → Ideal → Store → Ideal → Prop} (s : Script α) (f : α → Script β) (σ σ' : Store)
    (I I' : Ideal) (vD : List Release)
    (h : Agree Q (withAdv E me adv s σ I vD) (withAdv E me adv s σ' I' vD))
    (hf : ∀ a, (withAdv E me adv s σ I vD).result = some a →
      Q a (withAdv E me adv s σ I vD).store (withAdv E me adv s σ I vD).ideal
        (withAdv E me adv s σ' I' vD).store (withAdv E me adv s σ' I' vD).ideal →
      Agree R
        (withAdv E me adv (f a) (withAdv E me adv s σ I vD).store (withAdv E me adv s σ I vD).ideal
          (vD ++ (withAdv E me adv s σ I vD).viewD))
        (withAdv E me adv (f a) (withAdv E me adv s σ' I' vD).store (withAdv E me adv s σ' I' vD).ideal
          (vD ++ (withAdv E me adv s σ I vD).viewD))) :
    Agree R (withAdv E me adv (s.bind f) σ I vD) (withAdv E me adv (s.bind f) σ' I' vD) := by
  have hres := h.result
  have hvd := h.viewD
  rw [withAdv_bind, withAdv_bind, ← hres, ← hvd]
  cases hr : (withAdv E me adv s σ I vD).result with
  | none =>
    exact ⟨h.viewD, h.viewH, h.trace, h.replies, rfl, fun a ha => by simp [Outcome.stop] at ha⟩
  | some a =>
    have h2 := hf a hr (h.post a hr)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · show _ ++ _ = _ ++ _
      rw [h2.viewD, hvd]
    · show _ ++ _ = _ ++ _
      rw [h2.viewH, h.viewH]
    · show _ ++ _ = _ ++ _
      rw [h2.trace, h.trace]
    · show _ ++ _ = _ ++ _
      rw [h2.replies, h.replies]
    · exact h2.result
    · exact h2.post

/-- **One instruction.** Both stores fill it, with the same early release; for the contribution
the adversary makes, the functionality aborts in both runs or releases the same to both parties
in both runs, the honest party's reply is the same, and the continuations agree. -/
theorem Agree.step {α : Type} {Q : α → Store → Ideal → Store → Ideal → Prop} (i : Instr)
    (k : Reply → Script α) (σ σ' : Store) (I I' : Ideal) (vD : List Release) (w w' : Wire)
    (hw : fill E.hash me σ i = some w) (hw' : fill E.hash me σ' i = some w') (he : w'.early = w.early)
    (h : ∀ part, adv.act (vD ++ w.early.toList) i.skel = some part →
      (idealStep E me w part I = none ∧ idealStep E me w' part I' = none) ∨
      ∃ I1 I1' toH toD, idealStep E me w part I = some (I1, toH, toD) ∧
        idealStep E me w' part I' = some (I1', toH, toD) ∧
        (absorb E.hash me i σ' toH).1 = (absorb E.hash me i σ toH).1 ∧
        Agree Q
          (withAdv E me adv (k (absorb E.hash me i σ toH).1) (absorb E.hash me i σ toH).2 I1 (vD ++ toD.toList))
          (withAdv E me adv (k (absorb E.hash me i σ toH).1) (absorb E.hash me i σ' toH).2 I1' (vD ++ toD.toList))) :
    Agree Q (withAdv E me adv (.step i k) σ I vD) (withAdv E me adv (.step i k) σ' I' vD) := by
  simp only [withAdv, hw, hw', he]
  cases ha : adv.act (vD ++ w.early.toList) i.skel with
  | none => exact ⟨rfl, rfl, rfl, rfl, rfl, fun a ha => by simp at ha⟩
  | some part =>
    rcases h part ha with ⟨h1, h2⟩ | ⟨I1, I1', toH, toD, h1, h2, h3, h4⟩
    · simp only [h1, h2]
      exact ⟨rfl, rfl, rfl, rfl, rfl, fun a ha => by simp at ha⟩
    · simp only [h1, h2, h3]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · show _ ++ _ = _ ++ _
        rw [h4.viewD]
      · show _ ++ _ = _ ++ _
        rw [h4.viewH]
      · show _ :: _ = _ :: _
        rw [h4.trace]
      · show _ :: _ = _ :: _
        rw [h4.replies]
      · exact h4.result
      · exact h4.post

/-- **A local block**: when it succeeds in both engine states, the runs agree if the rest does. -/
theorem Agree.locals {α : Type} {Q : α → Store → Ideal → Store → Ideal → Prop} (s : Script α) (σ σ' : Store) :
    ∀ (is : List Instr), (∀ i ∈ is, isLocal i = true) → ∀ (I I' I1 I1' : Ideal) (vD : List Release),
      runLocal E is I = some I1 → runLocal E is I' = some I1' →
      Agree Q (withAdv E me adv s σ I1 vD) (withAdv E me adv s σ' I1' vD) →
      Agree Q (withAdv E me adv (seqs is s) σ I vD) (withAdv E me adv (seqs is s) σ' I' vD)
  | [], _, I, I', I1, I1', vD, h1, h2, hk => by
    simp only [runLocal, Option.some.injEq] at h1 h2
    subst h1
    subst h2
    exact hk
  | i :: is, hp, I, I', I1, I1', vD, h1, h2, hk => by
    have hi := hp i (by simp)
    simp only [runLocal] at h1 h2
    cases hs : localStep E i I with
    | none => rw [hs] at h1; cases h1
    | some J =>
      cases hs' : localStep E i I' with
      | none => rw [hs'] at h2; cases h2
      | some J' =>
        rw [hs] at h1
        rw [hs'] at h2
        have ih := Agree.locals s σ σ' is (fun j hj => hp j (by simp [hj])) J J' I1 I1' vD h1 h2 hk
        show Agree Q (withAdv E me adv (seq i (seqs is s)) σ I vD) (withAdv E me adv (seq i (seqs is s)) σ' I' vD)
        refine Agree.step E me adv i _ σ σ' I I' vD (blankWire i) (blankWire i) (fill_local _ _ _ i hi)
          (fill_local _ _ _ i hi) rfl (fun part _ => Or.inr ⟨J, J', none, none, ?_, ?_, ?_, ?_⟩)
        · rw [idealStep_local E me _ I i hi, hs]
          rfl
        · rw [idealStep_local E me _ I' i hi, hs']
          rfl
        · rw [absorb_none, absorb_none]
        · rw [absorb_none, absorb_none, Option.toList_none, List.append_nil]
          exact ih

/-- **A field opening**: the same opened values in both runs. -/
theorem Agree.openFieldThen {α : Type} {Q : α → Store → Ideal → Store → Ideal → Prop} (hs : List FieldH)
    (l : Label) (k : List F → Script α) (σ σ' : Store) (I I' : Ideal) (vD : List Release) (v : List F)
    (hv : hs.mapM (fun h => I.fields h.id) = some v) (hv' : hs.mapM (fun h => I'.fields h.id) = some v)
    (hk : Agree Q (withAdv E me adv (k v) σ I (vD ++ [⟨l, .elems v⟩]))
      (withAdv E me adv (k v) σ' I' (vD ++ [⟨l, .elems v⟩]))) :
    Agree Q (withAdv E me adv (openFieldThen hs l k) σ I vD) (withAdv E me adv (openFieldThen hs l k) σ' I' vD) := by
  unfold TlsMpc.Node.Flows.Run.openFieldThen
  refine Agree.step E me adv _ _ σ σ' I I' vD (.openField hs l) (.openField hs l) rfl rfl rfl
    (fun part _ => Or.inr ⟨I, I', some ⟨l, .elems v⟩, some ⟨l, .elems v⟩, ?_, ?_, rfl, hk⟩)
  · simp only [idealStep, hv]
  · simp only [idealStep, hv']

/-- **A Boolean opening**: the same opened bits in both runs. -/
theorem Agree.openThen {α : Type} {Q : α → Store → Ideal → Store → Ideal → Prop} (h0 : BoolH)
    (l : Label) (k : Bits → Script α) (σ σ' : Store) (I I' : Ideal) (vD : List Release) (v : Bits)
    (hv : I.bools h0.id = some v) (hv' : I'.bools h0.id = some v)
    (hk : Agree Q (withAdv E me adv (k v) σ I (vD ++ [⟨l, .bits v⟩]))
      (withAdv E me adv (k v) σ' I' (vD ++ [⟨l, .bits v⟩]))) :
    Agree Q (withAdv E me adv (openThen h0 l k) σ I vD) (withAdv E me adv (openThen h0 l k) σ' I' vD) := by
  unfold TlsMpc.Node.Flows.Contacts.openThen
  refine Agree.step E me adv _ _ σ σ' I I' vD (.openBool h0 l) (.openBool h0 l) rfl rfl rfl
    (fun part _ => Or.inr ⟨I, I', some ⟨l, .bits v⟩, some ⟨l, .bits v⟩, ?_, ?_, rfl, hk⟩)
  · simp only [idealStep, hv]
  · simp only [idealStep, hv']

/-- **A program step**: it succeeds in both runs with the same openings (its outputs may differ). -/
theorem Agree.program {α : Type} {Q : α → Store → Ideal → Store → Ideal → Prop} (name : Bytes) (copies : Nat)
    (ins masks outs : List FieldH) (l : Label) (s : Script α) (σ σ' : Store) (I I' : Ideal) (vD : List Release)
    (p : TlsMpc.FieldDag.V3.Program) (vi vm vo vi' vm' vo' opened : List F)
    (hp : E.programs name = some p)
    (hi : ins.mapM (fun h => I.fields h.id) = some vi) (hm : masks.mapM (fun h => I.fields h.id) = some vm)
    (hr : runProgram p copies vi vm = some (vo, opened)) (hl : vo.length = outs.length)
    (hi' : ins.mapM (fun h => I'.fields h.id) = some vi') (hm' : masks.mapM (fun h => I'.fields h.id) = some vm')
    (hr' : runProgram p copies vi' vm' = some (vo', opened)) (hl' : vo'.length = outs.length)
    (hk : Agree Q (withAdv E me adv s σ (I.setFields outs vo) (vD ++ [⟨l, .elems opened⟩]))
      (withAdv E me adv s σ' (I'.setFields outs vo') (vD ++ [⟨l, .elems opened⟩]))) :
    Agree Q (withAdv E me adv (seq (.program name copies ins masks outs l) s) σ I vD)
      (withAdv E me adv (seq (.program name copies ins masks outs l) s) σ' I' vD) := by
  unfold seq
  refine Agree.step E me adv _ _ σ σ' I I' vD (.program name copies ins masks outs l)
    (.program name copies ins masks outs l) rfl rfl rfl
    (fun part _ => Or.inr ⟨I.setFields outs vo, I'.setFields outs vo', some ⟨l, .elems opened⟩,
      some ⟨l, .elems opened⟩, ?_, ?_, rfl, hk⟩)
  · simp only [idealStep, hp, hi, hm, hr, hl, if_true]
  · simp only [idealStep, hp, hi', hm', hr', hl', if_true]

/-- The engines' state after both parties' Boolean inputs (`mine`: the honest party's). -/
def bothBools (me : Party) (I : Ideal) (oa ob : BoolH) (mine peer : Bits) : Ideal :=
  (I.setBool oa (if me = .a then mine else peer)).setBool ob (if me = .a then peer else mine)

/-- The engines' state after both parties' field inputs. -/
def bothFields (me : Party) (I : Ideal) (oa ob : List FieldH) (mine peer : List F) : Ideal :=
  (I.setFields oa (if me = .a then mine else peer)).setFields ob (if me = .a then peer else mine)

/-- **Both parties' Boolean inputs**: the two stores may hold different bits (of the right width);
the runs agree if the rest does for every contribution of the adversary. -/
theorem Agree.boolInputBoth {α : Type} {Q : α → Store → Ideal → Store → Ideal → Prop} (oa ob : BoolH) (w : Nat)
    (once rev : Bool) (slot : Nat) (s : Script α) (σ σ' : Store) (I I' : Ideal) (vD : List Release)
    (hl : (σ.bits slot).length = w) (hl' : (σ'.bits slot).length = w)
    (hk : ∀ pb : Bits, pb.length = w →
      Agree Q (withAdv E me adv s σ (bothBools me I oa ob (σ.bits slot) pb) vD)
        (withAdv E me adv s σ' (bothBools me I' oa ob (σ'.bits slot) pb) vD)) :
    Agree Q (withAdv E me adv (seq (.boolInputBoth oa ob w once rev slot) s) σ I vD)
      (withAdv E me adv (seq (.boolInputBoth oa ob w once rev slot) s) σ' I' vD) := by
  unfold seq
  refine Agree.step E me adv _ _ σ σ' I I' vD (.boolInputBoth oa ob w once rev (σ.bits slot))
    (.boolInputBoth oa ob w once rev (σ'.bits slot)) (by simp [fill, hl]) (by simp [fill, hl']) rfl
    (fun part _ => ?_)
  by_cases hp : part.bits.length = w
  · refine Or.inr ⟨bothBools me I oa ob (σ.bits slot) part.bits, bothBools me I' oa ob (σ'.bits slot) part.bits,
      none, none, ?_, ?_, rfl, ?_⟩
    · cases me <;> simp [idealStep, bothBools, hl, hp]
    · cases me <;> simp [idealStep, bothBools, hl', hp]
    · have := hk part.bits hp
      simpa [absorb] using this
  · refine Or.inl ⟨?_, ?_⟩
    · cases me <;> simp [idealStep, hp]
    · cases me <;> simp [idealStep, hp]

/-- **Both parties' field inputs**: the two stores may hold different elements (as many as the
outputs, coins when coins are asked); the runs agree if the rest does for every contribution of
the adversary. -/
theorem Agree.fieldInput {α : Type} {Q : α → Store → Ideal → Store → Ideal → Prop} (oa ob : List FieldH)
    (kd : FieldIn) (rev : Bool) (slot : Nat) (s : Script α) (σ σ' : Store) (I I' : Ideal) (vD : List Release)
    (hab : oa.length = ob.length)
    (hl : (σ.elems slot).length = oa.length) (hc : coinsOk kd (σ.elems slot) = true)
    (hl' : (σ'.elems slot).length = oa.length) (hc' : coinsOk kd (σ'.elems slot) = true)
    (hk : ∀ pe : List F, pe.length = oa.length → coinsOk kd pe = true →
      Agree Q (withAdv E me adv s σ (bothFields me I oa ob (σ.elems slot) pe) vD)
        (withAdv E me adv s σ' (bothFields me I' oa ob (σ'.elems slot) pe) vD)) :
    Agree Q (withAdv E me adv (seq (.fieldInput oa ob kd rev slot) s) σ I vD)
      (withAdv E me adv (seq (.fieldInput oa ob kd rev slot) s) σ' I' vD) := by
  unfold seq
  refine Agree.step E me adv _ _ σ σ' I I' vD (.fieldInput oa ob kd rev (σ.elems slot))
    (.fieldInput oa ob kd rev (σ'.elems slot)) (by simp [fill, hl, hc]) (by simp [fill, hl', hc']) rfl
    (fun part _ => ?_)
  by_cases hp : part.elems.length = oa.length ∧ coinsOk kd part.elems = true
  · refine Or.inr ⟨bothFields me I oa ob (σ.elems slot) part.elems, bothFields me I' oa ob (σ'.elems slot) part.elems,
      none, none, ?_, ?_, rfl, ?_⟩
    · cases me <;> simp [idealStep, bothFields, hl, hc, hp.1, hp.2, ← hab]
    · cases me <;> simp [idealStep, bothFields, hl', hc', hp.1, hp.2, ← hab]
    · have := hk part.elems hp.1 hp.2
      simpa [absorb] using this
  · refine Or.inl ⟨?_, ?_⟩
    · cases me <;> simp only [idealStep, reduceCtorEq, if_true, if_false, ← hab] <;> rw [if_neg] <;>
        intro hh <;> exact hp ⟨by first | exact hh.2.1 | exact hh.1, by first | exact hh.2.2.2 | exact hh.2.2.1⟩
    · cases me <;> simp only [idealStep, reduceCtorEq, if_true, if_false, ← hab] <;> rw [if_neg] <;>
        intro hh <;> exact hp ⟨by first | exact hh.2.1 | exact hh.1, by first | exact hh.2.2.2 | exact hh.2.2.1⟩

end

/-! ## `Random.joint` and `Random.challenge` read only two byte slots -/

section Joint

open TlsMpc.Node.Flows.Random

variable (E : Env) (me : Party) (adv : Adversary)

/-- The run of `joint` from another store with the same nonce and value, and any engine state, is
the same run (only the store and the engine state it carries along differ). -/
theorem withAdv_joint_frame (hh : ∀ m, (E.hash m).length = 32) (σ σ' : Store) (I I' : Ideal)
    (vD : List Release) (nonce value : Nat)
    (hn : (σ.bytes nonce).length = 32) (hv : (σ.bytes value).length = 32)
    (hbn : σ'.bytes nonce = σ.bytes nonce) (hbv : σ'.bytes value = σ.bytes value) :
    withAdv E me adv (joint E.hash me nonce value) σ' I' vD =
      { withAdv E me adv (joint E.hash me nonce value) σ I vD with store := σ', ideal := I' } := by
  have e1' : e1 E me σ' nonce value = e1 E me σ nonce value := by simp [e1, ourCommit, hbn, hbv]
  have e2' : e2 σ' nonce value = e2 σ nonce value := by simp [e2, hbn, hbv]
  have oc : ourCommit E me σ' nonce value = ourCommit E me σ nonce value := by simp [ourCommit, hbn, hbv]
  rw [withAdv_joint E me adv σ' I' vD nonce value hh (by rw [hbn]; exact hn) (by rw [hbv]; exact hv),
    withAdv_joint E me adv σ I vD nonce value hh hn hv, e1', e2', oc, hbn, hbv]
  cases h1 : adv.act (vD ++ [e1 E me σ nonce value]) skel1 with
  | none => rfl
  | some p1 =>
    by_cases hl1 : p1.bytes.length = 32
    · simp only [if_pos hl1]
      cases h2 : adv.act (vD ++ [e1 E me σ nonce value, e2 σ nonce value]) skel2 with
      | none => rfl
      | some p2 =>
        by_cases hl2 : p2.bytes.length = 64
        · simp only [if_pos hl2]
        · simp only [if_neg hl2]
    · simp only [if_neg hl1]

/-- **`joint` from two stores with the same nonce and value**: the runs agree and leave both
stores and both engine states as they were. -/
theorem agree_joint (hh : ∀ m, (E.hash m).length = 32) (σ σ' : Store) (I I' : Ideal)
    (vD : List Release) (nonce value : Nat)
    (hn : (σ.bytes nonce).length = 32) (hv : (σ.bytes value).length = 32)
    (hbn : σ'.bytes nonce = σ.bytes nonce) (hbv : σ'.bytes value = σ.bytes value) :
    Agree (fun _ s i s' i' => s = σ ∧ i = I ∧ s' = σ' ∧ i' = I')
      (withAdv E me adv (joint E.hash me nonce value) σ I vD)
      (withAdv E me adv (joint E.hash me nonce value) σ' I' vD) := by
  rw [withAdv_joint_frame E me adv hh σ σ' I I' vD nonce value hn hv hbn hbv]
  obtain ⟨h1, h2⟩ := joint_ideal E me adv σ I vD nonce value hh hn hv
  exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => ⟨h2, h1, rfl, rfl⟩⟩

/-- The same for `challenge` (the permutation is computed from the seed alone). -/
theorem agree_challenge (hh : ∀ m, (E.hash m).length = 32) (σ σ' : Store) (I I' : Ideal)
    (vD : List Release) (nonce value : Nat) (domain : Bytes) (n : Nat)
    (hn : (σ.bytes nonce).length = 32) (hv : (σ.bytes value).length = 32)
    (hbn : σ'.bytes nonce = σ.bytes nonce) (hbv : σ'.bytes value = σ.bytes value) :
    Agree (fun _ s i s' i' => s = σ ∧ i = I ∧ s' = σ' ∧ i' = I')
      (withAdv E me adv (challenge E.hash me nonce value domain n) σ I vD)
      (withAdv E me adv (challenge E.hash me nonce value domain n) σ' I' vD) := by
  unfold challenge
  refine Agree.bind E me adv _ _ σ σ' I I' vD (agree_joint E me adv hh σ σ' I I' vD nonce value hn hv hbn hbv)
    (fun seed _ hq => ?_)
  obtain ⟨h1, h2, h3, h4⟩ := hq
  rw [h1, h2, h3, h4]
  unfold finish
  split
  · exact Agree.done E me adv _ _ _ _ _ _ ⟨rfl, rfl, rfl, rfl⟩
  · exact Agree.abort E me adv _ _ _ _ _ _

/-- An accepted challenge is a permutation of `[0, n)` (P-CHAL (b)), in any run. -/
theorem challenge_result_spec (σ : Store) (I : Ideal) (vD : List Release) (nonce value : Nat)
    (domain : Bytes) (n : Nat) (π : List Nat)
    (h : (withAdv E me adv (challenge E.hash me nonce value domain n) σ I vD).result = some π) :
    π.length = n ∧ π.Nodup ∧ ∀ x ∈ π, x < n := by
  obtain ⟨seed, -, hp⟩ := challenge_result E me adv σ I vD nonce value domain n π h
  exact permOf_spec E.hash domain seed n π hp

end Joint

end TlsMpc.Node.Flows.Run
