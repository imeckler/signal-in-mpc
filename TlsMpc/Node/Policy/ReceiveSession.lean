import TlsMpc.Node.Policy.ReceiveLoop
import TlsMpc.Node.Policy.RecordLoop

/-!
# T1 about the record loop the session runs (PROOF_GAPS.md C1, C2)

`ReceiveLoop.t1_model` (formerly `t1_all`) is about `ReceiveProofs.recordLoop` / `streamRun`, a
pure transcription of the session's record loop. Since 2026-11-12 the session's `record`
(`Session/Common.lean`) IS `RecordLoop.run` (`Policy/RecordLoop.lean`) at the session's operations
(`Common.recordOps`). This file proves T1 about `RecordLoop.run` itself, at any operations of the
pure monad `RevealM` (failures keep the list of revealed stream positions) that satisfy the
assumption on the engines (`Faithful`), and over a whole connection: record after record with the
session's steps between records (`sessionRun`), every one that keeps the policy's view.

* `loop_sub`: every position `RecordLoop.loop` reveals is one `recordLoop` reveals, and when it
  returns a state `recordLoop` returns the same state. The three differences of C1 are handled
  here: the bytes come from the `reveal` parameter (hypothesis `Faithful.reveal`); completed
  envelopes go to the `envelope` parameter before the list is cleared (`Faithful.envelope`: it may
  fail, which ends the loop early, but does not reveal; the state the loop continues from is
  `{ s with envelopes := [] }` as in `recordLoop`); the loop has fuel `length + 1`, which never runs
  out under `Faithful` (`loop_good`'s bound; running out would only stop it, revealing nothing).
* `replies_state`, `view_replies` (C2): `PublicReceive.replies` returns the state with only
  `control` changed, so it keeps the view; with `view_requests`, `view_expect` and the fetch fields
  (`view_fetch`), every step the session applies to a connection's parser state between two of its
  records keeps the view (`KeepsView`, closed under composition: `keepsView_bind`).
* `t1_session` (from any state that simulates the reference) and **`t1_all`** (from the upgraded
  start): every stream position the session's record loop reveals, over every stream, every cut
  into records, with any view-keeping steps between records, is allowed by
  `ReceiveSpec.classifyFrames`, or is its first `error` (the one-byte allowance).

**The assumption on `revealRange` (`Faithful`).** For the record `r` at stream position `base`, the
engines' length probe returns `r.length`, and `reveal offset count` returns `r.length` and exactly
the bytes `(r.drop offset).take count` (as the parsers' bytes), revealing to the nodes those stream
positions and no others; the other operations reveal nothing (they may fail). For the script TLS
backend (S12, branch `s12-tls`, not merged) this is a theorem (`reveal_value`, `range_value`); for
the legacy operation 43 (`Flows/TlsLegacy.lean`, today's) it stays an assumption on the engines (A1).

Standard axioms only. No emitter or executable imports this module.
-/

open TlsMpc TlsMpc.Signal

namespace ReceiveLoop

open PublicReceive ReceiveProofs ReceiveStream ReceiveSimByte ReceiveSim

/-! ### The pure monad: results, and the stream positions revealed so far -/

/-- A computation that may fail and records the stream positions revealed (failures keep them). -/
def RevealM (α : Type) : Type := List Nat → Except String α × List Nat

namespace RevealM

instance : Monad RevealM where
  pure a := fun acc => (.ok a, acc)
  bind x f := fun acc =>
    match x acc with
    | (.ok a, acc') => f a acc'
    | (.error e, acc') => (.error e, acc')

instance : MonadExceptOf String RevealM where
  throw e := fun acc => (.error e, acc)
  tryCatch x h := fun acc =>
    match x acc with
    | (.error e, acc') => h e acc'
    | r => r

variable {α β : Type}

theorem pure_run (a : α) (acc : List Nat) : (pure a : RevealM α) acc = (.ok a, acc) := rfl
theorem throw_run (e : String) (acc : List Nat) : (throw e : RevealM α) acc = (.error e, acc) := rfl
theorem bind_run (x : RevealM α) (f : α → RevealM β) (acc : List Nat) :
    (x >>= f) acc = (match x acc with
      | (.ok a, acc') => f a acc'
      | (.error e, acc') => (.error e, acc')) := rfl
theorem lift_run (x : Except String α) (acc : List Nat) : (RecordLoop.lift x : RevealM α) acc = (x, acc) := by
  cases x <;> rfl

end RevealM

open RevealM

/-- The positions of `n` bytes revealed from `offset` of the record at stream position `base`. -/
def positions (base offset n : Nat) : List Nat := (List.range n).map (base + offset + ·)

/-- **The assumption on the engines** for the record `r` at stream position `base` (header). -/
structure Faithful (r : List Byte) (base : Nat) {β : Type} (o : RecordLoop.Ops RevealM β) : Prop where
  length : ∀ acc, o.length acc = (.ok r.length, acc)
  reveal : ∀ offset count acc, ∃ bs : List β,
    o.reveal offset count acc = (.ok (r.length, bs), acc ++ positions base offset bs.length) ∧
    bs.map o.byte = (r.drop offset).take count
  passed : ∀ offset count capture collect acc, (o.passed offset count capture collect acc).2 = acc
  revealed : ∀ offset bs acc, (o.revealed offset bs acc).2 = acc
  envelope : ∀ kind size acc, (o.envelope kind size acc).2 = acc

/-! ### The loop against `recordLoop` -/

theorem recordLoop_mono : ∀ (fuel : Nat) (s : State) (r : List Byte) (off base : Nat) (acc : List Nat),
    ∀ q ∈ acc, q ∈ (recordLoop fuel s r off base acc).1
  | 0, _, _, _, _, _, _, hq => hq
  | fuel + 1, s, r, off, base, acc, q, hq => by
    unfold recordLoop
    dsimp only
    repeat' split
    all_goals first
      | exact hq
      | exact List.mem_append_left _ hq
      | exact recordLoop_mono fuel _ r _ base _ q hq
      | exact recordLoop_mono fuel _ r _ base _ q (List.mem_append_left _ hq)

theorem stepRun_window : ∀ (l : List Byte) (s : State) (c : Bool) (s' : State) (c' : Bool),
    RecordLoop.stepRun s c l = .ok (s', c') → stepWindow s l = .ok s'
  | [], s, c, s', c', h => by
    simp only [RecordLoop.stepRun, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | b :: rest, s, c, s', c', h => by
    unfold RecordLoop.stepRun at h
    unfold stepWindow
    cases hs : step s b with
    | error e => rw [hs] at h; cases h
    | ok p =>
      obtain ⟨next, done⟩ := p
      rw [hs] at h
      simp only at h
      show (if rest.isEmpty then pure next else if mayReveal next && decide (rest.length ≤ budget next) then
        stepWindow next rest else throw "revealed range went past what may be revealed") = Except.ok s'
      cases rest with
      | nil =>
        simp only [List.length_nil, beq_self_eq_true, Bool.true_or, if_true] at h
        simp only [RecordLoop.stepRun, Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1]; rfl
      | cons b' rest' =>
        simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, List.length_cons]
        have hz : (rest'.length + 1 == 0) = false := by simp
        simp only [List.length_cons, hz, Bool.false_or] at h
        split at h
        · next hc =>
          rw [if_pos hc]
          exact stepRun_window (b' :: rest') next _ s' c' h
        · cases h

theorem envelopes_acc {β : Type} {o : RecordLoop.Ops RevealM β}
    (he : ∀ kind size acc, (o.envelope kind size acc).2 = acc) :
    ∀ (l : List (Nat × Nat)) (acc : List Nat), (RecordLoop.envelopes o l acc).2 = acc
  | [], _ => rfl
  | (kind, size) :: rest, acc => by
    show ((o.envelope kind size >>= fun _ => RecordLoop.envelopes o rest) acc).2 = acc
    rw [bind_run]
    have h1 := he kind size acc
    revert h1
    rcases o.envelope kind size acc with ⟨res, acc1⟩
    intro h1
    simp only at h1
    subst h1
    cases res with
    | ok _ => exact envelopes_acc he rest _
    | error _ => rfl

/-- A computation's run, split into its result and the positions, when the positions are
unchanged. -/
theorem run_same {α : Type} {x : RevealM α} {acc : List Nat} (h : (x acc).2 = acc) :
    x acc = ((x acc).1, acc) :=
  Prod.ext rfl h

/-- Close a case of `loop_sub` that stops (the loop failed): its positions are the model's so far. -/
macro "sub_close" : tactic => `(tactic| (try dsimp only) <;> (try split) <;> first
  | exact ⟨fun q hq => hq, fun _ _ h => by cases h⟩
  | exact ⟨fun q hq => recordLoop_mono _ _ _ _ _ _ q hq, fun _ _ h => by cases h⟩
  | exact ⟨fun q hq => List.mem_append_left _ hq, fun _ _ h => by cases h⟩)

set_option maxHeartbeats 1000000 in
/-- **The loop the session runs against the model** (C1). Under `Faithful`, every position
`RecordLoop.loop` reveals is one `recordLoop` reveals (with the same fuel), and when it returns a
state, `recordLoop` returns the same state. -/
theorem loop_sub {β : Type} {o : RecordLoop.Ops RevealM β} {r : List Byte} {base : Nat} (hO : Faithful r base o) :
    ∀ (fuel : Nat) (s : State) (cpl : Bool) (off : Nat) (acc : List Nat),
      (∀ q ∈ (RecordLoop.loop o fuel s cpl off r.length acc).2, q ∈ (recordLoop fuel s r off base acc).1) ∧
      (∀ s' c', (RecordLoop.loop o fuel s cpl off r.length acc).1 = .ok (s', c') →
        (recordLoop fuel s r off base acc).2 = .ok s')
  | 0, s, cpl, off, acc => ⟨fun q hq => hq, fun s' c' h => by cases h⟩
  | fuel + 1, s, cpl, off, acc => by
    unfold RecordLoop.loop recordLoop
    by_cases hlt : off < r.length
    · rw [if_pos hlt, if_pos hlt]
      by_cases hsk : s.skip > 0
      · rw [if_pos hsk, if_pos hsk]
        -- passed over
        dsimp only
        simp only [bind_run]
        rw [run_same (hO.passed off _ _ _ acc)]
        generalize (o.passed off (min s.skip (r.length - off)) s.capture s.collect acc).1 = res1
        cases res1 with
        | error e => sub_close
        | ok u =>
          dsimp only
          rw [lift_run]
          cases hp : passRun (min s.skip (r.length - off) - min (min s.skip (r.length - off)) (passRoom s))
              (passBulk (min (min s.skip (r.length - off)) (passRoom s)) s) with
          | error e => dsimp only; sub_close
          | ok p =>
            obtain ⟨s1, d⟩ := p
            dsimp only
            rw [run_same (envelopes_acc hO.envelope s1.envelopes acc)]
            generalize (RecordLoop.envelopes o s1.envelopes acc).1 = res2
            cases res2 with
            | error e => sub_close
            | ok u' => exact loop_sub hO fuel _ _ _ acc
      · rw [if_neg hsk, if_neg hsk]
        by_cases hmr : mayReveal s = true
        · have hlen : ∀ bs : List β, bs.map o.byte = (r.drop off).take (budget s) →
              bs.length = ((r.drop off).take (budget s)).length := fun bs h => by rw [← h, List.length_map]
          have hemp : ∀ bs : List β, bs.map o.byte = (r.drop off).take (budget s) →
              bs.isEmpty = ((r.drop off).take (budget s)).isEmpty := fun bs h => by rw [← h]; cases bs <;> rfl
          obtain ⟨bs, hrev, hbs⟩ := hO.reveal off (budget s) acc
          simp only [hmr, Bool.not_true, Bool.false_eq_true, if_false, bind_run, pure_run, hrev]
          rw [if_pos hlt]
          have hpos : positions base off bs.length =
              (List.range ((r.drop off).take (budget s)).length).map (base + off + ·) := by
            rw [positions, hlen bs hbs]
          rw [hpos]
          by_cases he : ((r.drop off).take (budget s)).isEmpty = true
          · have he' : bs.isEmpty = true := by rw [hemp bs hbs]; exact he
            simp only [he, he', if_true, bind_run, throw_run]
            sub_close
          · have he' : bs.isEmpty = false := by rw [hemp bs hbs]; simpa using he
            have he0 : ((r.drop off).take (budget s)).isEmpty = false := by simpa using he
            simp only [he0, he', Bool.false_eq_true, if_false, bind_run, pure_run]
            rw [run_same (hO.revealed off bs _)]
            generalize (o.revealed off bs (acc ++ (List.range ((r.drop off).take (budget s)).length).map (base + off + ·))).1
              = res3
            cases res3 with
            | error e => sub_close
            | ok u =>
              dsimp only
              rw [lift_run, hbs]
              cases hw : RecordLoop.stepRun s cpl ((r.drop off).take (budget s)) with
              | error e =>
                dsimp only
                split
                · sub_close
                · sub_close
              | ok p =>
                obtain ⟨s2, c2⟩ := p
                rw [stepRun_window _ _ _ _ _ hw]
                dsimp only
                rw [run_same (envelopes_acc hO.envelope s2.envelopes _)]
                generalize (RecordLoop.envelopes o s2.envelopes
                    (acc ++ (List.range ((r.drop off).take (budget s)).length).map (base + off + ·))).1 = res4
                cases res4 with
                | error e => sub_close
                | ok u' =>
                  dsimp only
                  rw [hlen bs hbs]
                  exact loop_sub hO fuel _ _ _ _
        · have hmr' : mayReveal s = false := by simpa using hmr
          simp only [hmr', Bool.not_false, if_true, bind_run, throw_run]
          sub_close
    · rw [if_neg hlt, if_neg hlt]
      exact ⟨fun q hq => hq, fun s' c' h => by cases h; rfl⟩

set_option maxHeartbeats 1000000 in
/-- **The fuel never runs out** (C1: the loop that ran before had none). Under `Faithful`, from
`offset`, any fuel above the bytes left gives the same run as any larger fuel: the loop the session
runs (`RecordLoop.run`: fuel `length + 1`) behaves as the unbounded `while` loop did. Every step
before the end advances `offset` by at least one. -/
theorem loop_fuel {β : Type} {o : RecordLoop.Ops RevealM β} {r : List Byte} {base : Nat} (hO : Faithful r base o) :
    ∀ (fuel k : Nat) (s : State) (cpl : Bool) (off : Nat) (acc : List Nat), r.length - off < fuel →
      RecordLoop.loop o (fuel + k) s cpl off r.length acc = RecordLoop.loop o fuel s cpl off r.length acc
  | 0, _, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, k, s, cpl, off, acc, h => by
    rw [show fuel + 1 + k = (fuel + k) + 1 by omega]
    unfold RecordLoop.loop
    by_cases hlt : off < r.length
    · rw [if_pos hlt, if_pos hlt]
      by_cases hsk : s.skip > 0
      · rw [if_pos hsk, if_pos hsk]
        have hc : 1 ≤ min s.skip (r.length - off) := Nat.le_min.mpr ⟨hsk, by omega⟩
        dsimp only
        simp only [bind_run]
        generalize o.passed off (min s.skip (r.length - off)) s.capture s.collect acc = p1
        rcases p1 with ⟨res1, acc1⟩
        cases res1 with
        | error e => rfl
        | ok u =>
          dsimp only
          rw [lift_run]
          cases passRun (min s.skip (r.length - off) - min (min s.skip (r.length - off)) (passRoom s))
              (passBulk (min (min s.skip (r.length - off)) (passRoom s)) s) with
          | error e => rfl
          | ok p =>
            obtain ⟨s1, d⟩ := p
            dsimp only
            generalize RecordLoop.envelopes o s1.envelopes acc1 = p2
            rcases p2 with ⟨res2, acc2⟩
            cases res2 with
            | error e => rfl
            | ok u' =>
              dsimp only
              exact loop_fuel hO fuel k _ _ _ _ (by omega)
      · rw [if_neg hsk, if_neg hsk]
        by_cases hmr : mayReveal s = true
        · obtain ⟨bs, hrev, hbs⟩ := hO.reveal off (budget s) acc
          simp only [hmr, Bool.not_true, Bool.false_eq_true, if_false, bind_run, pure_run, hrev]
          rw [if_pos hlt, if_pos hlt]
          cases hb : bs.isEmpty
          · have hl : 1 ≤ bs.length := by
              cases bs with
              | nil => cases hb
              | cons _ _ => simp
            simp only [Bool.false_eq_true, if_false, bind_run, pure_run]
            generalize o.revealed off bs (acc ++ positions base off bs.length) = p3
            rcases p3 with ⟨res3, acc3⟩
            cases res3 with
            | error e => rfl
            | ok u =>
              dsimp only
              rw [lift_run]
              cases RecordLoop.stepRun s cpl (List.map o.byte bs) with
              | error e => rfl
              | ok p =>
                obtain ⟨s2, c2⟩ := p
                dsimp only
                generalize RecordLoop.envelopes o s2.envelopes acc3 = p4
                rcases p4 with ⟨res4, acc4⟩
                cases res4 with
                | error e => rfl
                | ok u' =>
                  dsimp only
                  exact loop_fuel hO fuel k _ _ (off + bs.length) _ (by omega)
          · simp only [if_true, bind_run, throw_run]
        · have hmr' : mayReveal s = false := by simpa using hmr
          simp only [hmr', Bool.not_false, if_true, bind_run, throw_run]
    · rw [if_neg hlt, if_neg hlt]

/-- **The record loop the session runs is the unbounded loop**: `RecordLoop.run` gives `loop` the
record's length plus one steps, and any more give the same run. -/
theorem run_fuel {β : Type} {o : RecordLoop.Ops RevealM β} {r : List Byte} {base : Nat} (hO : Faithful r base o)
    (s : State) (acc : List Nat) (k : Nat) :
    RecordLoop.loop o (r.length + 1 + k) s false 0 r.length acc = RecordLoop.run o s acc := by
  rw [loop_fuel hO (r.length + 1) k s false 0 acc (by omega)]
  show _ = (o.length >>= fun length => RecordLoop.loop o (length + 1) s false 0 length) acc
  rw [bind_run, hO.length]

/-! ### Between records (C2): every step the session takes keeps the view -/

theorem bind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- `replies` changes only the control queue (and returns the frames). -/
theorem replies_state {s s' : State} {masks : List (List Byte)} {frames : List (Nat × List Byte)}
    (h : replies s masks = .ok (s', frames)) :
    s' = { s with control := s.control.take 127 ++ List.replicate 509 0 } := by
  unfold replies at h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := bind_ok h
    split at h
    · obtain ⟨_, -, h⟩ := bind_ok h
      obtain ⟨_, -, h⟩ := bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      exact h.1.symm
    · obtain ⟨_, h1, -⟩ := bind_ok h
      cases h1
  · obtain ⟨_, h1, -⟩ := bind_ok h
    cases h1

/-- **`replies` keeps the policy's view** (C2; the lemma that timed out, by `replies_state`). -/
theorem view_replies {s s' : State} {masks : List (List Byte)} {frames : List (Nat × List Byte)}
    (h : replies s masks = .ok (s', frames)) : view s' = view s := by
  rw [replies_state h]; rfl

/-- The prekey fetch's fields (`Send.refreshContact`, `refreshSoft`) are not in the view. -/
theorem view_fetch (s : State) (f : Option Nat) (b : Option Nat) (c : Bool) :
    view { s with fetch := f } = view s ∧ view { s with fetch := f, bundle := b } = view s ∧
      view { s with fetch := f, collect := c } = view s := ⟨rfl, rfl, rfl⟩

/-- A step between records keeps the view. -/
def Keeps (f : State → Except String State) : Prop := ∀ s s', f s = .ok s' → view s' = view s

theorem keeps_pure (f : State → State) (h : ∀ s, view (f s) = view s) : Keeps (fun s => .ok (f s)) :=
  fun s s' e => by cases e; exact h s

theorem keepsView_bind {f g : State → Except String State} (hf : Keeps f) (hg : Keeps g) :
    Keeps (fun s => f s >>= g) := by
  intro s s' h
  obtain ⟨t, ht, hg'⟩ := bind_ok h
  rw [hg t s' hg', hf s t ht]

/-- The session's step after a record (`awaitReply`, `awaitSoft`, `drainOne`, `Send.loop`,
`Receive`): the control replies (masks: any), then `requests := []`. -/
theorem keeps_afterRecord (masks : List (List Byte)) :
    Keeps (fun s => (replies s masks).map (fun p => { p.1 with requests := [] })) := by
  intro s s' h
  dsimp only at h
  cases hr : replies s masks with
  | error e => rw [hr] at h; cases h
  | ok p =>
    obtain ⟨t, fr⟩ := p
    rw [hr] at h
    simp only [Except.map, Except.ok.injEq] at h
    subst h
    show view { t with requests := [] } = view s
    rw [← view_requests t, view_replies hr]

/-- `expect` (a keepalive, a send, a resend, a prekey fetch) keeps the view. -/
theorem keeps_expect (id : Nat) : Keeps (fun s => .ok (expect s id)) :=
  keeps_pure _ (fun s => (view_expect s id).symm)

/-! ### Whole connections -/

/-- **One connection's records as the session reads them**: each through the deployed record loop
`RecordLoop.run`, at that record's operations `O base r` (`base`: its stream position), and between
the `i`-th record and the next the session's step `g i`. Returns every revealed position, and the
final state or the first error. -/
def sessionGo {β : Type} (O : Nat → List Byte → RecordLoop.Ops RevealM β) (g : Nat → State → Except String State) :
    State → List (List Byte) → Nat → Nat → List Nat → List Nat × Except String State
  | s, [], _, _, acc => (acc, .ok s)
  | s, r :: rs, i, base, acc =>
    match RecordLoop.run (O base r) s acc with
    | (.error e, acc') => (acc', .error e)
    | (.ok (s', _), acc') =>
      match g i s' with
      | .error e => (acc', .error e)
      | .ok s'' => sessionGo O g s'' rs (i + 1) (base + r.length) acc'

def sessionRun {β : Type} (O : Nat → List Byte → RecordLoop.Ops RevealM β) (g : Nat → State → Except String State)
    (s : State) (records : List (List Byte)) : List Nat × Except String State :=
  sessionGo O g s records 0 0 []

theorem run_eq {β : Type} {o : RecordLoop.Ops RevealM β} {r : List Byte} {base : Nat} (hO : Faithful r base o)
    (s : State) (acc : List Nat) :
    RecordLoop.run o s acc = RecordLoop.loop o (r.length + 1) s false 0 r.length acc := by
  show (o.length >>= fun length => RecordLoop.loop o (length + 1) s false 0 length) acc = _
  rw [bind_run, hO.length]

theorem sessionGo_good {ob : Bool} {C : List ReceiveSpec.Class} {β : Type}
    {O : Nat → List Byte → RecordLoop.Ops RevealM β} {g : Nat → State → Except String State}
    (hO : ∀ base r, Faithful r base (O base r)) (hg : ∀ i, Keeps (g i)) :
    ∀ (records : List (List Byte)) (s : State) (i base : Nat) (acc : List Nat) (st : Stream.St × Bool),
      Sim ob s st records.flatten.length → G ob C base st records.flatten → (∀ q ∈ acc, Good C q) →
      ∀ q ∈ (sessionGo O g s records i base acc).1, Good C q
  | [], _, _, _, _, _, _, _, hacc, q, hq => hacc q hq
  | r :: rs, s, i, base, acc, st, hs, hg0, hacc, q, hq => by
    rw [List.flatten_cons] at hs hg0
    have hL := loop_good (r.length + 1) s r 0 base acc st rs.flatten (by omega) (by omega)
      (by rw [List.drop_zero]; exact hs) (by rw [List.drop_zero, Nat.add_zero]; exact hg0) hacc
    have hS := loop_sub (hO base r) (r.length + 1) s false 0 acc
    unfold sessionGo at hq
    rw [run_eq (hO base r)] at hq
    revert hq hS
    rcases RecordLoop.loop (O base r) (r.length + 1) s false 0 r.length acc with ⟨res, acc1⟩
    intro hS hq
    cases res with
    | error e => exact hL.1 q (hS.1 q hq)
    | ok p =>
      obtain ⟨s1, c1⟩ := p
      have hsub : ∀ q ∈ acc1, Good C q := fun q h => hL.1 q (hS.1 q h)
      obtain ⟨st', hs', hg'⟩ := hL.2 s1 (hS.2 s1 c1 rfl)
      simp only at hq
      split at hq
      · exact hsub q hq
      · next s2 h2 =>
        exact sessionGo_good hO hg rs s2 (i + 1) (base + r.length) acc1 st'
          (sim_congr (hg i s1 s2 h2).symm hs') hg' hsub q hq

/-- **T1 for the record loop the session runs, from any state that simulates the reference's
initial state**, over every stream and every cut into records, with any steps between records that
keep the view, and the engines as assumed (`Faithful`). -/
theorem t1_session (ob : Bool) (s : State) (records : List (List Byte))
    (hs : Sim ob s Stream.init records.flatten.length) {β : Type}
    (O : Nat → List Byte → RecordLoop.Ops RevealM β) (hO : ∀ base r, Faithful r base (O base r))
    (g : Nat → State → Except String State) (hg : ∀ i, Keeps (g i)) :
    ∀ q ∈ (sessionRun O g s records).1,
      ReceiveSpec.allowedIn (ReceiveSpec.classifyFrames ob records.flatten) q = true ∨
        ReceiveSpec.firstError (ReceiveSpec.classifyFrames ob records.flatten) = some q := by
  intro q hq
  have hC : ReceiveSpec.classifyFrames ob records.flatten = Stream.runF ob Stream.init records.flatten := by
    rw [Stream.classifyFrames_stream]; rfl
  have hg0 : G ob (ReceiveSpec.classifyFrames ob records.flatten) 0 Stream.init records.flatten :=
    ⟨[], by rw [hC]; rfl, rfl, by simp⟩
  exact sessionGo_good hO hg records s 0 0 [] Stream.init hs hg0 (by simp) q hq

/-- **T1 for every stream, about the function the session calls** (`RecordLoop.run`, the policy
core of `Session/Common.lean`'s `record`), from the upgraded starting state (any `accept`, any
`lenient`, either `openBody`): over every stream of frames cut into records in any way, with any
steps of the session between records that keep the view (`replies` then `requests := []`:
`keeps_afterRecord`; `expect`: `keeps_expect`; the fetch fields: `view_fetch`; compositions:
`keepsView_bind`), every stream position the loop has the engines reveal is public in
`ReceiveSpec.classifyFrames openBody records.flatten`, or is that list's first `error`. Assumption:
the engines' operations are `Faithful` (header). -/
theorem t1_all (openBody : Bool) (accept : List Byte) (lenient : Bool) (records : List (List Byte))
    {β : Type} (O : Nat → List Byte → RecordLoop.Ops RevealM β) (hO : ∀ base r, Faithful r base (O base r))
    (g : Nat → State → Except String State) (hg : ∀ i, Keeps (g i)) :
    ∀ q ∈ (sessionRun O g { PublicReceive.start accept with upgraded := true, lenient := lenient, openBody } records).1,
      ReceiveSpec.allowedIn (ReceiveSpec.classifyFrames openBody records.flatten) q = true ∨
        ReceiveSpec.firstError (ReceiveSpec.classifyFrames openBody records.flatten) = some q :=
  t1_session openBody _ records (start_sim openBody accept lenient _) O hO g hg

end ReceiveLoop
