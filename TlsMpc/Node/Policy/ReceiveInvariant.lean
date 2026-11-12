import TlsMpc.Node.Policy.ReceiveEnvelope
import TlsMpc.KernelSpecs.ParseWebSocketFrame

/-!
# T1's per-byte glue: what `step`, `stepSkipped` and `passBulk` keep (proof track P1)

New file; it changes no definition. No emitter or executable imports it. Standard axioms only.

`PublicReceive.step` is `frameByte` (upgrade, frame parser, control queue) followed by `payloadByte`
(the message: kind, response parser, response / request / envelope fields, overrun check, message
end). This file proves what those two and `stepSkipped` keep, byte by byte (`passBulk` is a run of
`stepSkipped`: `passRun_bulk`).

## The request path: delivered envelopes, end to end (every byte string)

* **Where the walk starts** (`payloadByte_request_envelope`): at the byte that completes the body's
  length of a server request whose path is `/api/v1/message`, `scan` asks to pass over `n > 0` bytes
  and the controller starts walking the envelope: `EnvAt s' [] 0 0 n` (with the request's revealed
  bytes ending at the body's length: `scan_skip_missing`, so `budget_env`: one byte per run).
* **Each byte of the walk is `envWalk`'s**: revealed (`env_reveal`, from `payloadByte_env` and
  `envelopeAdvance_ok`), passed over (`env_pass`, from `stepSkipped_inner`), or not the envelope's
  at all (a continuation frame's header, a control frame between fragments: `payloadByte_nodata`,
  with `frameByte_keeps`).
* **Any run of the controller's moves over the body** (`EnvRun`) reveals a prefix of what `envWalk`
  reveals (`envRun_walk`), hence only bytes the reference calls public (`envRun_safe`, with
  `envelope_payload_unrevealed`); composed: `request_envelope_safe`.

## A server request's own fields (invariant (iii)/(v) for requests)

`payloadByte_request_more`, `payloadByte_request_skip`, `payloadByte_request_malformed`: on a
request byte with no envelope being walked, the request's revealed bytes grow by the byte, and
`skip` becomes non-zero exactly when `scan` asks to pass over a body (`skip := n`, the body's
length, `n > 0`); a delivered message's body is walked instead (`payloadByte_request_envelope`).

## A response's own fields (invariant (iii)/(v) for responses)

`payloadByte_reply_more`, `payloadByte_reply_skip`: on a response byte (third payload byte on, the
message not ending there), whatever the response parser's feed does first (`forIn_keeps`), the
response's revealed bytes grow by the byte, and `skip` becomes non-zero exactly when `replyScan` asks
to pass over the body (`skip := n`).

## The frame side (invariant (i))

`frameByte_frame`: once upgraded, `frameByte` keeps the frame state equal to `stateBytes` of the
reference parser's state (`TlsWebSocketFrame.step`, via `runByte_active`), and hands `payloadByte`
that step's event.

## Not here (what T1 for every stream still needs)

* a streaming form of `ReceiveSpec.classifyFrames` (it is a recursive function of the whole stream)
  and its agreement with the reference, and the frame layer's simulation of it: message assembly
  across fragments, control frames, the reject lemmas against the reference's `error` bytes;
* the request scanner against `ReceiveSpec.request` for every field order (`request_body_unrevealed`
  covers the server's order), and `fieldMissing`'s runs against the reference's `text` bytes;
* the loop: `recordLoop`'s runs (`budget`) against the classes above, with the one-byte allowance.
-/

open TlsMpc TlsMpc.Signal

namespace ReceiveProofs

open PublicReceive

/-! ### `Except` -/

theorem throw_ok_iff {α : Type} (e : String) (a : α) : ((throw e : Except String α) = .ok a) ↔ False :=
  ⟨fun h => (by cases h), False.elim⟩

theorem throw_bind_ex {α β : Type} (e : String) (f : α → Except String β) :
    ((throw e : Except String α) >>= f) = throw e := rfl

theorem bind_ok_iff {α β : Type} (x : Except String α) (f : α → Except String β) (b : β) :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact ⟨fun h => (by cases h), fun ⟨a, h, _⟩ => (by cases h)⟩
  | ok a => exact ⟨fun h => ⟨a, rfl, h⟩, fun ⟨a', h, h'⟩ => by cases h; exact h'⟩

theorem ite_ok {α : Type} {c : Prop} [Decidable c] {x y : Except String α} {v : α}
    (h : (if c then x else y) = .ok v) : x = .ok v ∨ y = .ok v := by
  by_cases hc : c
  · rw [if_pos hc] at h; exact Or.inl h
  · rw [if_neg hc] at h; exact Or.inr h

theorem two_beq_one : ((2 : Nat) == 1) = false := rfl
theorem two_beq_zero : ((2 : Nat) == 0) = false := rfl
theorem l81_82 : (([8, 1] : List Byte) == [8, 2]) = false := by decide
theorem l81_81 : (([8, 1] : List Byte) == [8, 1]) = true := by decide

/-! ### `envelopeScan` never asks to pass over an empty payload -/

/-- No `.pass 0` answer in a loop state. -/
def NoPass0 (r : EnvState) : Prop := ∀ c f a b, r.fst = some (.pass c f, a, b) → c ≠ 0

theorem envField_cases (bytes : List Byte) (p key count after c : Nat) (r : EnvState) :
    (∃ r', envField bytes p key count after c r = .yield r' ∧ r'.fst = none) ∨
    (∃ r', envField bytes p key count after c r = .done r' ∧ NoPass0 r') := by
  unfold envField
  by_cases h0 : (count == 0) = true
  · exact Or.inl ⟨_, by rw [if_pos h0], rfl⟩
  rw [if_neg h0]
  by_cases h1 : r.snd.snd.snd.snd < p
  · exact Or.inl ⟨_, by rw [if_pos h1], rfl⟩
  rw [if_neg h1]
  by_cases h2 : (after == bytes.length) = true
  · refine Or.inr ⟨_, by rw [if_pos h2], ?_⟩
    intro c' f a b h
    simp only [Option.some.injEq, Prod.mk.injEq, EnvelopeNeed.pass.injEq] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    simp only [beq_iff_eq] at h0; exact h0
  · refine Or.inr ⟨_, by rw [if_neg h2], ?_⟩
    intro c' f a b h
    simp at h

theorem envCount_cases (bytes : List Byte) (p key count after : Nat) (r : EnvState) :
    (∃ r', envCount bytes p key count after r = .yield r' ∧ r'.fst = none) ∨
    (∃ r', envCount bytes p key count after r = .done r' ∧ NoPass0 r') := by
  unfold envCount
  split
  · split
    · exact Or.inr ⟨_, rfl, fun c f a b h => by simp at h⟩
    · exact envField_cases bytes p key count after count r
  · exact envField_cases bytes p key count after r.snd.fst r

theorem envUnfinished_noPass0 (bytes : List Byte) (at_ : Nat) (r : EnvState) :
    ∃ r', envUnfinished bytes at_ r = .done r' ∧ NoPass0 r' := by
  refine ⟨_, rfl, fun c f a b h => ?_⟩
  simp only at h
  split at h <;> simp at h

theorem envBody_cases (bytes : List Byte) (p : Nat) (r : EnvState) :
    (∃ r', envBody bytes p r = .yield r' ∧ r'.fst = none) ∨
    (∃ r', envBody bytes p r = .done r' ∧ NoPass0 r') := by
  unfold envBody
  split
  · exact Or.inr ⟨_, rfl, fun c f a b h => by simp at h⟩
  split
  · split
    · split
      · split
        · exact Or.inl ⟨_, rfl, rfl⟩
        · exact Or.inl ⟨_, rfl, rfl⟩
      · exact Or.inr (envUnfinished_noPass0 _ _ _)
    · split
      · split
        · split
          · exact envCount_cases _ _ _ _ _ _
          · exact Or.inr (envUnfinished_noPass0 _ _ _)
        · exact envCount_cases _ _ _ _ _ _
      · exact Or.inr ⟨_, rfl, fun c f a b h => by simp at h⟩
  · exact Or.inr (envUnfinished_noPass0 _ _ _)

theorem loopG_noPass0 (bytes : List Byte) (p : Nat) : ∀ (n : Nat) (r : EnvState), r.fst = none →
    NoPass0 (loopG (envBody bytes p) n r)
  | 0, r, h => fun c f a b e => by simp [loopG, h] at e
  | n + 1, r, h => by
    rcases envBody_cases bytes p r with ⟨r', e, h'⟩ | ⟨r', e, h'⟩
    · rw [loopG_yield n e]; exact loopG_noPass0 bytes p n r' h'
    · rw [loopG_done n e]; exact h'

/-- **`envelopeScan` never asks to pass over an empty payload.** -/
theorem envelopeScan_pass_pos {bytes : List Byte} {p n : Nat} {c : Bool}
    (h : (envelopeScan bytes p).1 = .pass n c) : n ≠ 0 := by
  rw [envelopeScan_eq] at h
  have hn := loopG_noPass0 bytes p (bytes.length + 1) ⟨none, 0, 0, 0, 0⟩ rfl
  unfold envResult at h
  generalize loopG (envBody bytes p) (bytes.length + 1) ⟨none, 0, 0, 0, 0⟩ = r at h hn
  obtain ⟨fst, snd⟩ := r
  cases fst with
  | none => simp at h
  | some a =>
    obtain ⟨need, a1, a2⟩ := a
    simp only at h
    subst h
    exact hn n c a1 a2 rfl

/-! ### `envelopeAdvance` -/

/-- What a successful `envelopeAdvance` does: on `.more`, the walk goes on (or, at the body's end,
stops: `inner := none`), `skip` unchanged; on `.pass n`, `skip := n`, with `0 < n ≤ rem`. The
message is unchanged. -/
theorem envelopeAdvance_ok {s s2 : State} {H : List Byte} {p rem : Nat}
    (h : envelopeAdvance s H p rem = .ok s2) :
    (s2.message = s.message ∧ s2.request = s.request) ∧
    ((∃ b, (envelopeScan H p).1 = .more b ∧ s2.skip = s.skip ∧
       (rem = 0 → s2.inner = none) ∧ (rem ≠ 0 → s2.inner = some (H, p, rem))) ∨
     (∃ n c, (envelopeScan H p).1 = .pass n c ∧ 0 < n ∧ n ≤ rem ∧ s2.skip = n ∧ s2.inner = some (H, p, rem))) := by
  unfold envelopeAdvance at h
  generalize hq : envelopeScan H p = q at h
  obtain ⟨need, kind, content⟩ := q
  cases need with
  | malformed => cases h
  | more b =>
    simp only [bind, Except.bind, pure, Except.pure] at h
    by_cases hr : (rem == 0) = true
    · rw [if_pos hr] at h
      cases b
      · cases h
      · simp only [Bool.not_true, if_false, Bool.false_eq_true] at h
        cases h
        refine ⟨⟨rfl, rfl⟩, Or.inl ⟨true, rfl, rfl, fun _ => rfl, fun e => ?_⟩⟩
        simp only [beq_iff_eq] at hr; exact absurd hr e
    · rw [if_neg hr] at h
      cases h
      refine ⟨⟨rfl, rfl⟩, Or.inl ⟨b, rfl, rfl, fun e => ?_, fun _ => rfl⟩⟩
      simp only [beq_iff_eq] at hr; exact absurd e hr
  | pass n c =>
    by_cases hle : n ≤ rem
    · simp only [hle, ↓reduceIte, pure_bind] at h
      cases h
      have hp : (envelopeScan H p).1 = .pass n c := by rw [hq]
      exact ⟨⟨rfl, rfl⟩, Or.inr ⟨n, c, rfl, Nat.pos_of_ne_zero (envelopeScan_pass_pos hp), hle, rfl, rfl⟩⟩
    · simp only [hle, ↓reduceIte, throw_bind_ex, throw_ok_iff] at h

/-! ### Passing over an envelope byte: `stepSkipped` -/

/-- **What `stepSkipped` does to a delivered envelope being walked.** `skip` goes down by one; if it
reaches 0 (the payload's last byte), the walk goes on from the payload's end (`envelopeAdvance` with
one more payload passed), else only the body bytes left go down by one; and the message is not ended
inside the envelope. -/
theorem stepSkipped_inner {s s' : State} {h : List Byte} {p r : Nat} (hi : s.inner = some (h, p, r))
    (hok : stepSkipped s = .ok s') :
    0 < s.skip ∧ s.message = [8, 1] ∧ 0 < r ∧ ∃ t s2, t.skip = s.skip - 1 ∧ t.message = s.message ∧
      t.request = s.request ∧
      (s.skip - 1 = 0 → envelopeAdvance t h (p + 1) (r - 1) = .ok s2) ∧
      (s.skip - 1 ≠ 0 → s2 = { t with inner := some (h, p, r - 1) }) ∧
      s'.inner = s2.inner ∧ s'.skip = s2.skip ∧
      ((s'.message = s2.message ∧ s'.request = s2.request) ∨ s2.inner = none) := by
  unfold stepSkipped at hok
  generalize TlsMpc.TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0]) = F at hok
  by_cases g1 : (s.upgraded && decide (s.skip > 0) && s.message == [8, 1]) = true
  case neg =>
    simp only [g1, Bool.false_eq_true, ↓reduceIte, throw_bind_ex, throw_ok_iff] at hok
  have g1' := g1
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at g1'
  obtain ⟨⟨-, hpos⟩, hmsg⟩ := g1'
  by_cases g2 : (PublicReceive.get F 0 == on && PublicReceive.get F 1 == on) = true
  case neg =>
    simp only [g1, g2, Bool.false_eq_true, ↓reduceIte, pure_bind, throw_bind_ex, throw_ok_iff] at hok
  simp only [g1, g2, ↓reduceIte, pure_bind, hi] at hok
  by_cases hr : 0 < r
  case neg =>
    simp only [hr, ↓reduceIte, throw_bind_ex, throw_ok_iff] at hok
  refine ⟨hpos, hmsg, hr, ?_⟩
  simp only [hr, ↓reduceIte, pure_bind] at hok
  by_cases hk : s.skip - 1 = 0
  · simp only [hk, beq_self_eq_true, ↓reduceIte] at hok
    rw [bind_ok_iff] at hok
    obtain ⟨s2, hadv, hrest⟩ := hok
    refine ⟨_, s2, ?_, ?_, ?_, fun _ => hadv, fun e => absurd hk e, ?_⟩
    · exact hk.symm
    · rfl
    · rfl
    by_cases g5 : (PublicReceive.get F 5 == on) = true
    · simp only [g5, ↓reduceIte] at hrest
      by_cases g6 : (s2.skip == 0 && s2.inner.isNone) = true
      · simp only [g6, ↓reduceIte, pure_bind] at hrest
        cases hrest
        simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at g6
        exact ⟨rfl, rfl, Or.inr g6.2⟩
      · simp only [g6, Bool.false_eq_true, ↓reduceIte, throw_bind_ex, throw_ok_iff] at hrest
    · simp only [g5, Bool.false_eq_true, ↓reduceIte] at hrest
      cases hrest
      exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · have hk' : (s.skip - 1 == 0) = false := by simp only [beq_eq_false_iff_ne]; exact hk
    simp only [hk', Bool.false_eq_true, ↓reduceIte] at hok
    refine ⟨{ s with frame := F.drop 8, control := TlsMpc.TlsWebSocketControl.run fast (s.control ++ [PublicReceive.get F 2, PublicReceive.get F 6, PublicReceive.get F 7, 0]), skip := s.skip - 1 }, _, rfl, rfl, rfl, fun e => absurd e hk, fun _ => rfl, ?_⟩
    by_cases g5 : (PublicReceive.get F 5 == on) = true
    · simp only [g5, hk', Option.isNone_some, Bool.and_false, Bool.false_eq_true, ↓reduceIte, throw_bind_ex,
        throw_ok_iff] at hok
    · simp only [g5, Bool.false_eq_true, ↓reduceIte] at hok
      cases hok
      exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-! ### Revealing an envelope byte: `payloadByte` -/

/-- **What `payloadByte` does with a revealed byte of a delivered envelope** (a data byte, the
message a server request, an envelope being walked): the walk goes on with `envelopeAdvance` on the
revealed bytes and the byte, one body byte fewer; the message is not ended inside the envelope. -/
theorem payloadByte_env {s s' : State} {b : Byte} {done : Bool} {flags : List Byte} {c : Bool}
    {h : List Byte} {p r : Nat} (hm : s.message = [8, 1]) (hi : s.inner = some (h, p, r))
    (hok : payloadByte s b true done false flags = .ok (s', c)) :
    0 < r ∧ ∃ t s2, t.message = s.message ∧ t.skip = s.skip ∧ t.request = s.request ∧
      envelopeAdvance t (h ++ [b]) p (r - 1) = .ok s2 ∧
      s'.inner = s2.inner ∧ s'.skip = s2.skip ∧
      ((s'.message = s2.message ∧ s'.request = s2.request) ∨ s2.inner = none) := by
  unfold payloadByte at hok
  simp only [hm, hi, l81_82, l81_81, two_beq_one, List.length_cons, List.length_nil, Bool.true_and,
    Bool.false_and, Bool.and_false, Bool.false_eq_true, Bool.not_true, Bool.or_true, Bool.true_or,
    decide_true, decide_false, Nat.lt_irrefl, Nat.reduceAdd, Nat.reduceLT, List.forIn_nil, pure_bind,
    ite_self, beq_self_eq_true, ge_iff_le, Nat.le_refl, Bool.or_false, ↓reduceIte] at hok
  by_cases hr : 0 < r
  case neg =>
    simp only [hr, ↓reduceIte, throw_bind_ex, throw_ok_iff] at hok
  simp only [hr, ↓reduceIte, pure_bind] at hok
  refine ⟨hr, ?_⟩
  rw [bind_ok_iff] at hok
  obtain ⟨s2, hadv, hrest⟩ := hok
  refine ⟨_, s2, ?_, ?_, ?_, hadv, ?_⟩
  · exact hm.symm
  · rfl
  · rfl
  by_cases g1 : (PublicReceive.get s2.frame 4 == on && PublicReceive.get s2.frame 8 == on &&
      decide ((PublicReceive.get s2.frame 7).toNat < 8) &&
      decide (pendingField s2 > (PublicReceive.get s2.frame 10).toNat * 256 + (PublicReceive.get s2.frame 11).toNat)) = true
  · simp only [g1, ↓reduceIte, throw_bind_ex, throw_ok_iff] at hrest
  simp only [g1, Bool.false_eq_true, ↓reduceIte, pure_bind] at hrest
  cases done
  · simp only [Bool.false_eq_true, ↓reduceIte] at hrest
    cases hrest
    exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · simp only [↓reduceIte] at hrest
    by_cases g2 : (s2.skip == 0 && s2.inner.isNone) = true
    · have g2' := g2
      simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at g2'
      simp only [g2, ↓reduceIte, pure_bind] at hrest
      by_cases g3 : (pendingField s2 == 0) = true
      · simp only [g3, ↓reduceIte, pure_bind] at hrest
        cases hrest
        exact ⟨rfl, rfl, Or.inr g2'.2⟩
      · simp only [g3, Bool.false_eq_true, ↓reduceIte, throw_bind_ex, throw_ok_iff] at hrest
    · simp only [g2, Bool.false_eq_true, ↓reduceIte, throw_bind_ex, throw_ok_iff] at hrest

/-- What every round of the response parser's loop keeps, the loop keeps. -/
theorem forIn_keeps {α : Type} (P : State → Prop)
    (f : α → MProd Bool State → Except String (ForInStep (MProd Bool State)))
    (hf : ∀ x r r', P r.snd → f x r = .ok r' →
      P (match r' with | .done a => a | .yield a => a).snd) :
    ∀ (L : List α) (init r : MProd Bool State), P init.snd → forIn L init f = .ok r → P r.snd
  | [], init, r, h0, h => by
    simp only [List.forIn_nil] at h; cases h; exact h0
  | x :: L, init, r, h0, h => by
    rw [List.forIn_cons, bind_ok_iff] at h
    obtain ⟨st, hst, hrest⟩ := h
    have hx := hf x init st h0 hst
    cases st with
    | done a => cases hrest; exact hx
    | yield a => exact forIn_keeps P f hf L a r hx hrest

/-- A byte that is not a message payload byte (`data = false`: a frame header byte, a control frame's
payload byte) changes nothing of a delivered envelope's walk: the message, the walk and `skip` are
kept (or the step fails). -/
theorem payloadByte_nodata {s s' : State} {b : Byte} {done : Bool} {flags : List Byte} {c : Bool}
    {h : List Byte} {p r : Nat} (hi : s.inner = some (h, p, r))
    (hok : payloadByte s b false done false flags = .ok (s', c)) :
    s'.message = s.message ∧ s'.inner = s.inner ∧ s'.skip = s.skip ∧ s'.request = s.request := by
  unfold payloadByte at hok
  simp only [hi, Bool.false_and, Bool.and_false, Bool.false_eq_true, Bool.not_false, ↓reduceIte, pure_bind,
    Option.isNone_some] at hok
  by_cases k1 : (decide (s.message.length < 2) || s.message == [8, 2] || s.message == [8, 1]) = true
  case neg =>
    simp only [k1, Bool.false_eq_true, ↓reduceIte, throw_bind_ex, throw_ok_iff] at hok
  simp only [k1, ↓reduceIte] at hok
  rcases ite_ok hok with hok | hok <;> rcases ite_ok hok with hok | hok
  all_goals first
    | (rw [bind_ok_iff] at hok
       obtain ⟨r1, hfor, hrest⟩ := hok
       have hP := forIn_keeps (fun t => t.message = s.message ∧ t.inner = some (h, p, r) ∧ t.skip = s.skip ∧
           t.request = s.request) _
         (by
           intro x r0 r' hP0 e
           repeat' (rcases ite_ok e with e | e)
           all_goals first
             | (simp only [throw_bind_ex, throw_ok_iff] at e)
             | (cases e; exact hP0))
         _ _ _ ⟨rfl, rfl, rfl, rfl⟩ hfor
       simp only [hP.2.1, Option.isNone_some, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hrest
       rcases ite_ok hrest with hrest | hrest
       · simp only [throw_bind_ex, throw_ok_iff] at hrest
       · rcases ite_ok hrest with hrest | hrest
         · simp only [throw_bind_ex, throw_ok_iff] at hrest
         · cases hrest; exact ⟨hP.1, hP.2.1.trans hi.symm, hP.2.2.1, hP.2.2.2⟩)
    | (rcases ite_ok hok with hok | hok
       · simp only [throw_bind_ex, throw_ok_iff] at hok
       · rcases ite_ok hok with hok | hok
         · simp only [throw_bind_ex, throw_ok_iff] at hok
         · cases hok; exact ⟨rfl, hi.symm, rfl, rfl⟩)

/-! ### `frameByte` keeps the message side -/

/-- `frameByte`'s upgrade part, as a value. -/
def upgradePart (s : State) (byte : Byte) : Except String (Byte × State) :=
  if s.upgraded then pure (on, s) else do
    let out := TlsWebSocketUpgrade.runByte PublicReceive.fast (s.upgrade ++ s.accept ++ [on, byte])
    unless get out 0 == on do throw "WebSocket upgrade response rejected"
    let expected : Byte := if s.terminator % 2 == 0 then 13 else 10
    let terminator := if byte == expected then s.terminator + 1 else if byte == 13 then 1 else 0
    unless (get out 1 == on) == (terminator == 4) do throw "upgrade response headers ended unexpectedly"
    pure (get out 2, { s with upgrade := out.drop 3, upgraded := get out 1 == on, terminator })

/-- `frameByte`'s upgrade part, with its continuation. -/
def frameUpgrade {β : Type} (s : State) (byte : Byte) (k : Byte → State → Except String β) : Except String β := do
  let (activity, s) ← if s.upgraded then pure (on, s) else do
    let out := TlsWebSocketUpgrade.runByte PublicReceive.fast (s.upgrade ++ s.accept ++ [on, byte])
    unless get out 0 == on do throw "WebSocket upgrade response rejected"
    let expected : Byte := if s.terminator % 2 == 0 then 13 else 10
    let terminator := if byte == expected then s.terminator + 1 else if byte == 13 then 1 else 0
    unless (get out 1 == on) == (terminator == 4) do throw "upgrade response headers ended unexpectedly"
    pure (get out 2, { s with upgrade := out.drop 3, upgraded := get out 1 == on, terminator })
  k activity s

/-- `frameByte` after its upgrade part. -/
def frameRest (s : State) (byte activity : Byte) : Except String (State × List Byte) := do
  unless s.skip == 0 do throw "a request body byte was revealed"
  let s := if s.pending && s.message.isEmpty && get s.frame 0 == on then { s with rollback := s.response } else s
  let frame := TlsWebSocketFrame.runByte PublicReceive.fast capacity (s.frame ++ [activity, byte])
  unless get frame 0 == on do throw "WebSocket frame rejected"
  let control := TlsWebSocketControl.run PublicReceive.fast (s.control ++ [get frame 2, get frame 6, get frame 7, byte])
  return ({ s with frame := frame.drop 8, control }, frame.take 8)

theorem frameByte_split (s : State) (byte : Byte) :
    frameByte s byte = frameUpgrade s byte (fun a s1 => frameRest s1 byte a) := rfl

theorem frameUpgrade_eq {β : Type} (s : State) (byte : Byte) (k : Byte → State → Except String β) :
    frameUpgrade s byte k = upgradePart s byte >>= fun p => k p.1 p.2 := by
  unfold frameUpgrade upgradePart
  cases s.upgraded
  · simp only [Bool.false_eq_true, ↓reduceIte]
    generalize TlsWebSocketUpgrade.runByte PublicReceive.fast (s.upgrade ++ s.accept ++ [on, byte]) = out
    by_cases h1 : (get out 0 == on) = true
    · simp only [h1, ↓reduceIte]
      repeat' split
      all_goals rfl
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]; rfl
  · rfl

theorem upgradePart_ok {s s1 : State} {byte a : Byte} (h : upgradePart s byte = .ok (a, s1)) :
    ∃ u ud t, s1 = { s with upgrade := u, upgraded := ud, terminator := t } := by
  unfold upgradePart at h
  by_cases hu : s.upgraded = true
  · simp only [hu, ↓reduceIte] at h
    cases h
    exact ⟨s.upgrade, s.upgraded, s.terminator, rfl⟩
  simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
  generalize TlsWebSocketUpgrade.runByte PublicReceive.fast (s.upgrade ++ s.accept ++ [on, byte]) = out at h
  by_cases g0 : (get out 0 == on) = true
  case neg => simp only [g0, Bool.false_eq_true, ↓reduceIte, throw_bind_ex, throw_ok_iff] at h
  simp only [g0, ↓reduceIte, pure_bind] at h
  rcases ite_ok h with h | h
  · cases h
    exact ⟨_, _, _, rfl⟩
  · simp only [throw_bind_ex, throw_ok_iff] at h

theorem frameUpgrade_ok {β : Type} {s : State} {byte : Byte} {k : Byte → State → Except String β} {v : β}
    (h : frameUpgrade s byte k = .ok v) :
    ∃ a u ud t, k a { s with upgrade := u, upgraded := ud, terminator := t } = .ok v := by
  rw [frameUpgrade_eq, bind_ok_iff] at h
  obtain ⟨⟨a, s1⟩, h1, h2⟩ := h
  obtain ⟨u, ud, t, rfl⟩ := upgradePart_ok h1
  exact ⟨a, u, ud, t, h2⟩

theorem frameRest_ok {s s2 : State} {byte a : Byte} {ev : List Byte} (h : frameRest s byte a = .ok (s2, ev)) :
    s.skip = 0 ∧ s2.skip = s.skip ∧ s2.message = s.message ∧ s2.inner = s.inner ∧ s2.request = s.request ∧
      s2.bodySkipped = s.bodySkipped ∧ s2.reply = s.reply ∧ s2.replySkipped = s.replySkipped ∧
      s2.openBody = s.openBody := by
  unfold frameRest at h
  by_cases g1 : (s.skip == 0) = true
  case neg => simp only [g1, Bool.false_eq_true, ↓reduceIte, throw_bind_ex, throw_ok_iff] at h
  simp only [g1, ↓reduceIte, pure_bind] at h
  have h0 : s.skip = 0 := by simpa using g1
  by_cases g2 : (s.pending && s.message.isEmpty && PublicReceive.get s.frame 0 == on) = true
  · simp only [g2, ↓reduceIte] at h
    generalize TlsWebSocketFrame.runByte PublicReceive.fast capacity (s.frame ++ [a, byte]) = F at h
    by_cases g3 : (PublicReceive.get F 0 == on) = true
    case neg => simp only [g3, Bool.false_eq_true, ↓reduceIte, throw_bind_ex, throw_ok_iff] at h
    simp only [g3, ↓reduceIte, pure_bind] at h
    cases h
    exact ⟨h0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [g2, Bool.false_eq_true, ↓reduceIte] at h
    generalize TlsWebSocketFrame.runByte PublicReceive.fast capacity (s.frame ++ [a, byte]) = F at h
    by_cases g3 : (PublicReceive.get F 0 == on) = true
    case neg => simp only [g3, Bool.false_eq_true, ↓reduceIte, throw_bind_ex, throw_ok_iff] at h
    simp only [g3, ↓reduceIte, pure_bind] at h
    cases h
    exact ⟨h0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem frameByte_keeps {s s1 : State} {b : Byte} {ev : List Byte} (h : frameByte s b = .ok (s1, ev)) :
    s.skip = 0 ∧ s1.skip = s.skip ∧ s1.message = s.message ∧ s1.inner = s.inner ∧ s1.request = s.request ∧
      s1.bodySkipped = s.bodySkipped ∧ s1.reply = s.reply ∧ s1.replySkipped = s.replySkipped ∧
      s1.openBody = s.openBody := by
  rw [frameByte_split] at h
  obtain ⟨a, u, ud, t, h⟩ := frameUpgrade_ok h
  have hr := frameRest_ok h
  exact hr

/-! ### The walk -/

/-- **The controller is walking a delivered envelope**: its revealed bytes are `h`, `p` payloads
have been passed over, `k` bytes of a payload are still to be passed over (`skip`), and `r` bytes of
the body are left (`k ≤ r`: `envelopeAdvance` refuses a payload running past the body). The
request's revealed bytes end at the body's length (`fieldMissing` is 0: `budget` is one byte inside
a data frame's payload, `budget_env`). -/
structure EnvAt (s : State) (h : List Byte) (p k r : Nat) : Prop where
  message : s.message = [8, 1]
  inner : s.inner = some (h, p, r)
  skip : s.skip = k
  le : k ≤ r
  missing : fieldMissing s.request = 0

/-- The walk has left the envelope (its body ended): no envelope, nothing to pass over. -/
def EnvDone (s : State) : Prop := s.inner = none ∧ s.skip = 0

/-- **A passed-over envelope byte is `envWalk`'s** (`stepSkipped`). -/
theorem env_pass {s s' : State} {h : List Byte} {p k r : Nat} (hs : EnvAt s h p (k + 1) r)
    (hok : stepSkipped s = .ok s') (x : Byte) (E : List Byte) :
    ∃ h' p' k', envWalk h p (k + 1) (x :: E) = false :: envWalk h' p' k' E ∧
      (r - 1 = 0 → EnvDone s') ∧ (r - 1 ≠ 0 → EnvAt s' h' p' k' (r - 1)) := by
  obtain ⟨hpos, hmsg, hr, t, s2, tskip, tmsg, treq, hadv, hnot, hin, hsk, hm⟩ := stepSkipped_inner hs.inner hok
  have hsk0 := hs.skip
  rw [hsk0] at tskip hadv hnot
  simp only [Nat.add_sub_cancel] at tskip hadv hnot
  have hle := hs.le
  have hmiss := hs.missing
  by_cases hk : k = 0
  · subst hk
    obtain ⟨⟨am, areq⟩, hcase⟩ := envelopeAdvance_ok (hadv rfl)
    rcases hcase with ⟨bd, hq, s2skip, hz, hnz⟩ | ⟨n, cf, hq, npos, nle, s2skip, s2inner⟩
    · refine ⟨h, p + 1, 0, by simp [envWalk, hq], fun e => ⟨hin.trans (hz e), hsk.trans (s2skip.trans tskip)⟩,
        fun e => ?_⟩
      have hi2 := hnz e
      rcases hm with ⟨hm1, hm2⟩ | hm
      · exact ⟨hm1.trans (am.trans (tmsg.trans hmsg)), hin.trans hi2, hsk.trans (s2skip.trans tskip),
          Nat.zero_le _, by rw [hm2, areq, treq]; exact hmiss⟩
      · rw [hi2] at hm; cases hm
    · refine ⟨h, p + 1, n, by simp [envWalk, hq], fun e => by omega, fun e => ?_⟩
      rcases hm with ⟨hm1, hm2⟩ | hm
      · exact ⟨hm1.trans (am.trans (tmsg.trans hmsg)), hin.trans s2inner, hsk.trans s2skip, nle,
          by rw [hm2, areq, treq]; exact hmiss⟩
      · rw [s2inner] at hm; cases hm
  · have e2 := hnot hk
    refine ⟨h, p, k, by simp [envWalk, hk], fun e => by omega, fun _ => ?_⟩
    subst e2
    rcases hm with ⟨hm1, hm2⟩ | hm
    · refine ⟨hm1.trans (tmsg.trans hmsg), hin, hsk.trans tskip, by omega, ?_⟩
      rw [hm2]; show fieldMissing t.request = 0; rw [treq]; exact hmiss
    · cases hm

/-- **A revealed envelope byte is `envWalk`'s** (`payloadByte` on a data byte). -/
theorem env_reveal {s s' : State} {h : List Byte} {p r : Nat} {b : Byte} {done : Bool} {flags : List Byte}
    {c : Bool} (hs : EnvAt s h p 0 r) (hok : payloadByte s b true done false flags = .ok (s', c)) (E : List Byte) :
    ∃ h' p' k', envWalk h p 0 (b :: E) = true :: envWalk h' p' k' E ∧
      (r - 1 = 0 → EnvDone s') ∧ (r - 1 ≠ 0 → EnvAt s' h' p' k' (r - 1)) := by
  obtain ⟨hr, t, s2, tmsg, tskip, treq, hadv, hin, hsk, hm⟩ := payloadByte_env hs.message hs.inner hok
  obtain ⟨⟨am, areq⟩, hcase⟩ := envelopeAdvance_ok hadv
  have hsk0 := hs.skip
  have hmiss := hs.missing
  rcases hcase with ⟨bd, hq, s2skip, hz, hnz⟩ | ⟨n, cf, hq, npos, nle, s2skip, s2inner⟩
  · refine ⟨h ++ [b], p, 0, by simp [envWalk, hq],
      fun e => ⟨hin.trans (hz e), hsk.trans (s2skip.trans (tskip.trans hsk0))⟩, fun e => ?_⟩
    have hi2 := hnz e
    rcases hm with ⟨hm1, hm2⟩ | hm
    · exact ⟨hm1.trans (am.trans (tmsg.trans hs.message)), hin.trans hi2,
        hsk.trans (s2skip.trans (tskip.trans hsk0)), Nat.zero_le _, by rw [hm2, areq, treq]; exact hmiss⟩
    · rw [hi2] at hm; cases hm
  · refine ⟨h ++ [b], p, n, by simp [envWalk, hq], fun e => by omega, fun e => ?_⟩
    rcases hm with ⟨hm1, hm2⟩ | hm
    · exact ⟨hm1.trans (am.trans (tmsg.trans hs.message)), hin.trans s2inner, hsk.trans s2skip, nle,
        by rw [hm2, areq, treq]; exact hmiss⟩
    · rw [s2inner] at hm; cases hm

/-! ### `step` -/

/-- Whether the frame parser reports `b` as a message payload byte (the `data` event of
`frameByte`). -/
def stepData (s : State) (b : Byte) : Bool :=
  match frameByte s b with
  | .ok (_, ev) => PublicReceive.get ev 1 == on
  | .error _ => false

/-- `step` is `frameByte`, then `payloadByte` with the event's flags. -/
theorem step_ok {s s' : State} {b : Byte} {c : Bool} (h : step s b = .ok (s', c)) :
    ∃ s1 ev, frameByte s b = .ok (s1, ev) ∧ stepData s b = (PublicReceive.get ev 1 == on) ∧
      payloadByte s1 b (PublicReceive.get ev 1 == on) (PublicReceive.get ev 5 == on)
        ((PublicReceive.get ev 1 == on) && s1.message.length == 0)
        [PublicReceive.get ev 1, PublicReceive.get ev 3, PublicReceive.get ev 5] = .ok (s', c) := by
  unfold step at h
  rw [bind_ok_iff] at h
  obtain ⟨⟨s1, ev⟩, h1, h2⟩ := h
  exact ⟨s1, ev, h1, by simp [stepData, h1], h2⟩

theorem envWalk_reveal_head (h : List Byte) (p : Nat) (b : Byte) (E : List Byte) :
    ∃ rest, envWalk h p 0 (b :: E) = true :: rest := by
  simp only [envWalk]
  split
  · exact ⟨[], rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-! ### The controller's moves over an envelope -/

/-- **The controller's moves over the bytes `E` of a delivered envelope's body**, from state `s`;
`F` says, for each body byte in order, whether it was revealed. A body byte is revealed (`reveal`)
by `step` when the frame parser reports it as payload (`stepData`), or revealed and then the
controller stops (`fail`: the byte was revealed at `skip = 0`, the only state in which the loop
reveals); or passed over unrevealed by `stepSkipped` (`pass`; `passBulk` is a run of these,
`passRun_bulk`). Stream bytes that are not the body's (the header of a continuation frame, a control
frame between two fragments) are taken by `step` without being payload (`other`) and are not in `E`.
The controller may stop at any point (`stop`: an error, or the end of the stream). -/
inductive EnvRun : State → List Byte → List Bool → Prop
  | stop {s : State} {E : List Byte} : EnvRun s E []
  | fail {s : State} {b : Byte} {E : List Byte} : s.skip = 0 → EnvRun s (b :: E) [true]
  | reveal {s s' : State} {b : Byte} {E : List Byte} {F : List Bool} {c : Bool} :
      step s b = .ok (s', c) → stepData s b = true → EnvRun s' E F → EnvRun s (b :: E) (true :: F)
  | pass {s s' : State} {b : Byte} {E : List Byte} {F : List Bool} :
      stepSkipped s = .ok s' → EnvRun s' E F → EnvRun s (b :: E) (false :: F)
  | other {s s' : State} {x : Byte} {E : List Byte} {F : List Bool} {c : Bool} :
      step s x = .ok (s', c) → stepData s x = false → EnvRun s' E F → EnvRun s E F

theorem envRun_nil {s : State} {F : List Bool} (h : EnvRun s [] F) : F = [] := by
  generalize hE : ([] : List Byte) = E at h
  induction h with
  | stop => rfl
  | fail _ => cases hE
  | reveal _ _ _ _ => cases hE
  | pass _ _ _ => cases hE
  | other _ _ _ ih => exact ih hE

/-- **The controller's moves over an envelope reveal a prefix of what `envWalk` reveals**, from any
point of the walk, whatever the envelope's bytes, however its body is cut into frames, whatever
control frames come between them. -/
theorem envRun_walk {s : State} {E : List Byte} {F : List Bool} (h : EnvRun s E F) :
    ∀ {hd : List Byte} {p k : Nat}, EnvAt s hd p k E.length → F <+: envWalk hd p k E := by
  induction h with
  | stop => intro _ _ _ _; exact List.nil_prefix
  | @fail s b E hs0 =>
    intro hd p k hs
    have hk : k = 0 := hs.skip.symm.trans hs0
    subst hk
    obtain ⟨rest, e⟩ := envWalk_reveal_head hd p b E
    rw [e]; exact List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩
  | @reveal s s' b E F c hstep hdata hrun ih =>
    intro hd p k hs
    obtain ⟨s1, ev, h1, hd1, h2⟩ := step_ok hstep
    obtain ⟨hz, k1, k2, k3, k4, -⟩ := frameByte_keeps h1
    have hk : k = 0 := hs.skip.symm.trans hz
    subst hk
    have hev : (PublicReceive.get ev 1 == on) = true := by rw [← hd1]; exact hdata
    have hs1 : EnvAt s1 hd p 0 (b :: E).length :=
      ⟨k2.trans hs.message, k3.trans hs.inner, k1.trans hs.skip, hs.le, by rw [k4]; exact hs.missing⟩
    rw [hev] at h2
    have hfirst : (true && s1.message.length == 0) = false := by rw [hs1.message]; rfl
    rw [hfirst] at h2
    obtain ⟨h', p', k', ew, hdone, hat⟩ := env_reveal hs1 h2 E
    rw [ew]
    refine List.cons_prefix_cons.mpr ⟨rfl, ?_⟩
    simp only [List.length_cons, Nat.add_sub_cancel] at hdone hat
    by_cases hE : E.length = 0
    · have : E = [] := List.eq_nil_of_length_eq_zero hE
      subst this
      rw [envRun_nil hrun]; exact List.nil_prefix
    · exact ih (hat hE)
  | @pass s s' b E F hss hrun ih =>
    intro hd p k hs
    obtain ⟨hpos, -, -, -⟩ := stepSkipped_inner hs.inner hss
    obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by have := hs.skip; omega⟩
    obtain ⟨h', p', k', ew, hdone, hat⟩ := env_pass hs hss b E
    rw [ew]
    refine List.cons_prefix_cons.mpr ⟨rfl, ?_⟩
    simp only [List.length_cons, Nat.add_sub_cancel] at hdone hat
    by_cases hE : E.length = 0
    · have : E = [] := List.eq_nil_of_length_eq_zero hE
      subst this
      rw [envRun_nil hrun]; exact List.nil_prefix
    · exact ih (hat hE)
  | @other s s' x E F c hstep hdata hrun ih =>
    intro hd p k hs
    obtain ⟨s1, ev, h1, hd1, h2⟩ := step_ok hstep
    obtain ⟨hz, k1, k2, k3, k4, -⟩ := frameByte_keeps h1
    have hev : (PublicReceive.get ev 1 == on) = false := by rw [← hd1]; exact hdata
    rw [hev, Bool.false_and] at h2
    have hs1inner : s1.inner = some (hd, p, E.length) := k3.trans hs.inner
    obtain ⟨m1, m2, m3, m4⟩ := payloadByte_nodata hs1inner h2
    exact ih ⟨m1.trans (k2.trans hs.message), m2.trans hs1inner, m3.trans (k1.trans hs.skip), hs.le,
      by rw [m4, k4]; exact hs.missing⟩

theorem safeFor_prefix {F R : List Bool} {C : List ReceiveSpec.Class} (hp : F <+: R) (h : SafeFor R C) :
    SafeFor F C := by
  obtain ⟨t, rfl⟩ := hp
  intro i hi
  apply h i
  have hlt : i < F.length := by
    rcases Nat.lt_or_ge i F.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hi; cases hi
  rw [List.getElem?_append_left hlt]; exact hi

/-- **No payload byte of a delivered envelope is revealed (controller level, every byte string).**
From the state in which the controller starts walking a delivered envelope of `E.length` bytes
(`EnvAt s [] 0 0 E.length`, which `payloadByte_request_envelope` gives at the byte completing the
body's length), whatever moves the controller then makes over the body's bytes `E` (revealing,
passing over, frame headers and control frames between fragments, stopping), every body byte it
reveals has a public class in the reference (`ReceiveSpec.envelope`, as `ReceiveSpec.requestBody`
applies it to the body of a `/api/v1/message` request): a key, a length or a varint value, never a
field's payload. -/
theorem envRun_safe {s : State} {E : List Byte} {F : List Bool} (hs : EnvAt s [] 0 0 E.length)
    (h : EnvRun s E F) : SafeFor F (ReceiveSpec.envelope (E.length + 1) E) :=
  safeFor_prefix (envRun_walk h hs) (envelope_payload_unrevealed E)

/-- Inside a delivered envelope, in a data frame's payload, the controller reveals one byte at a
time (so `EnvRun`'s reveal-then-check moves are the loop's runs). -/
theorem budget_env {s : State} {h : List Byte} {p k r : Nat} (hs : EnvAt s h p k r) (hu : s.upgraded = true)
    (h0 : (PublicReceive.get s.frame 0 == on) = false) (h2 : (PublicReceive.get s.frame 2 == on) = false)
    (h4 : (PublicReceive.get s.frame 4 == on) = true)
    (hr : (PublicReceive.get s.frame 10).toNat * 256 + (PublicReceive.get s.frame 11).toNat ≠ 0)
    (ho : (PublicReceive.get s.frame 7).toNat < 8) : budget s ≤ 1 := by
  have := budget_request s hu h0 h2 h4 hr ho hs.message
  rw [hs.missing] at this
  omega

/-! ### Where the walk starts: `scan` finds a delivered message's body -/

/-- One round of `scan`'s loop against one round of `fieldMissing`'s: both go on to the same
position, or `scan`'s ends; when it ends asking to pass over `c` bytes, `c > 0` and `fieldMissing`'s
round goes on to the end of the bytes. -/
theorem scanBody_missing (bytes : List Byte) (b : Bool) (f : Fields) (pos : Nat) :
    (∃ f' pos', scanBody bytes b ⟨none, f, pos⟩ = .yield ⟨none, f', pos'⟩ ∧
      missingBody bytes ⟨none, pos⟩ = .yield ⟨none, pos'⟩) ∨
    (∃ r, scanBody bytes b ⟨none, f, pos⟩ = .done r ∧ ∀ c f'', r.fst = some (.skip c, f'') →
      0 < c ∧ ∃ pos', missingBody bytes ⟨none, pos⟩ = .yield ⟨none, pos'⟩ ∧ bytes.length ≤ pos') := by
  by_cases hp : pos ≥ bytes.length
  · exact Or.inr ⟨_, by unfold scanBody; dsimp only; rw [if_pos hp], by intro c f'' h; simp at h⟩
  generalize hT : (PublicReceive.get bytes pos).toNat = T
  by_cases a : T = 0x0a ∨ T = 0x12 ∨ T = 0x2a
  · have c1 : (T == 0x20) = false := by rcases a with rfl | rfl | rfl <;> rfl
    have c2 : (T == 0x0a || T == 0x12 || T == 0x2a) = true := by rcases a with rfl | rfl | rfl <;> rfl
    cases hv : varintAt bytes (pos + 1) with
    | none =>
      exact Or.inr ⟨_,
        by unfold scanBody; dsimp only; rw [if_neg hp, hT, c1]; simp only [c2, Bool.false_eq_true, ↓reduceIte, hv] <;> rfl,
        by intro c f'' h; split at h <;> simp at h⟩
    | some v =>
      obtain ⟨count, next⟩ := v
      by_cases hn : next + count > bytes.length
      · exact Or.inr ⟨_,
          by unfold scanBody; dsimp only; rw [if_neg hp, hT, c1]
             simp only [c2, Bool.false_eq_true, ↓reduceIte, hv, hn] <;> rfl,
          by intro c f'' h; simp at h⟩
      · left
        have hm : missingBody bytes ⟨none, pos⟩ = .yield ⟨none, next + count⟩ := by
          unfold missingBody; dsimp only; rw [if_neg hp, hT]; simp only [c2, ↓reduceIte, hv, hn]
        unfold scanBody; dsimp only; rw [if_neg hp, hT, c1]
        simp only [c2, Bool.false_eq_true, ↓reduceIte, hv, hn]
        split
        · split
          · exact ⟨_, _, rfl, hm⟩
          · exact ⟨_, _, rfl, hm⟩
        · split
          · exact ⟨_, _, rfl, hm⟩
          · exact ⟨_, _, rfl, hm⟩
  have c2 : (T == 0x0a || T == 0x12 || T == 0x2a) = false := by
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]; omega
  by_cases b20 : T = 0x20
  · subst b20
    cases hv : varintAt bytes (pos + 1) with
    | none =>
      exact Or.inr ⟨_,
        by unfold scanBody; dsimp only; rw [if_neg hp, hT]; simp only [↓reduceIte, hv, beq_self_eq_true] <;> rfl,
        by intro c f'' h; split at h <;> simp at h⟩
    | some v =>
      obtain ⟨value, next⟩ := v
      exact Or.inl ⟨_, next,
        by unfold scanBody; dsimp only; rw [if_neg hp, hT]; simp only [↓reduceIte, hv, beq_self_eq_true] <;> rfl,
        by unfold missingBody; dsimp only; rw [if_neg hp, hT]; simp only [c2, Bool.false_eq_true, ↓reduceIte, hv]; rfl⟩
  have c20 : (T == 0x20) = false := by simp only [beq_eq_false_iff_ne]; exact b20
  by_cases b1a : T = 0x1a
  · subst b1a
    cases hv : varintAt bytes (pos + 1) with
    | none =>
      exact Or.inr ⟨_,
        by unfold scanBody; dsimp only; rw [if_neg hp, hT]
           simp only [c20, c2, Bool.false_eq_true, ↓reduceIte, hv, beq_self_eq_true] <;> rfl,
        by intro c f'' h; split at h <;> simp at h⟩
    | some v =>
      obtain ⟨count, next⟩ := v
      have hm : missingBody bytes ⟨none, pos⟩ = .yield ⟨none, next⟩ := by
        unfold missingBody; dsimp only; rw [if_neg hp, hT]; simp only [c2, Bool.false_eq_true, ↓reduceIte, hv]; rfl
      by_cases hb : f.body.isSome = true
      · exact Or.inr ⟨_,
          by unfold scanBody; dsimp only; rw [if_neg hp, hT]
             simp only [c20, c2, Bool.false_eq_true, ↓reduceIte, hv, hb, beq_self_eq_true] <;> rfl,
          by intro c f'' h; simp at h⟩
      by_cases hs : (next == bytes.length && !b && decide (count > 0)) = true
      · have hs' := hs
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at hs'
        exact Or.inr ⟨_,
          by unfold scanBody; dsimp only; rw [if_neg hp, hT]
             simp only [c20, c2, Bool.false_eq_true, ↓reduceIte, hv, hb, hs, beq_self_eq_true] <;> rfl,
          by intro c f'' h
             simp only [Option.some.injEq, Prod.mk.injEq, Need.skip.injEq] at h
             obtain ⟨rfl, -⟩ := h
             exact ⟨hs'.2, next, hm, by omega⟩⟩
      · exact Or.inl ⟨_, next,
          by unfold scanBody; dsimp only; rw [if_neg hp, hT]
             simp only [c20, c2, Bool.false_eq_true, ↓reduceIte, hv, hb, hs, beq_self_eq_true] <;> rfl,
          hm⟩
  · have c1a : (T == 0x1a) = false := by simp only [beq_eq_false_iff_ne]; exact b1a
    exact Or.inr ⟨_,
      by unfold scanBody; dsimp only; rw [if_neg hp, hT]
         simp only [c20, c2, c1a, Bool.false_eq_true, ↓reduceIte] <;> rfl,
      by intro c f'' h; simp at h⟩

theorem missingBody_end {bytes : List Byte} {x : Option Nat} {pos : Nat} (h : bytes.length ≤ pos) :
    missingBody bytes ⟨x, pos⟩ = .done ⟨some 0, pos⟩ := by
  unfold missingBody; dsimp only; rw [if_pos h]

theorem scan_loop_missing (bytes : List Byte) (b : Bool) {n : Nat} {f' : Fields} : ∀ (m : Nat) (f : Fields) (pos : Nat),
    loopResult (loopG (scanBody bytes b) m ⟨none, f, pos⟩) = (.skip n, f') →
    0 < n ∧ ∀ k, missingResult (loopG (missingBody bytes) k ⟨none, pos⟩) = 0
  | 0, f, pos, h => by simp [loopG, loopResult] at h
  | m + 1, f, pos, h => by
    rcases scanBody_missing bytes b f pos with ⟨f1, pos1, hy, hmy⟩ | ⟨r, hd, hr⟩
    · rw [loopG_yield m hy] at h
      obtain ⟨hn, hk⟩ := scan_loop_missing bytes b m f1 pos1 h
      refine ⟨hn, fun k => ?_⟩
      cases k with
      | zero => rfl
      | succ k => rw [loopG_yield k hmy]; exact hk k
    · rw [loopG_done m hd] at h
      have hfst : r.fst = some (.skip n, f') := by
        unfold loopResult at h
        split at h
        · cases h
        · next a e => rw [e, h]
      obtain ⟨hn, pos', hmy, hle⟩ := hr n f' hfst
      refine ⟨hn, fun k => ?_⟩
      cases k with
      | zero => rfl
      | succ k =>
        rw [loopG_yield k hmy]
        cases k with
        | zero => rfl
        | succ k => rw [loopG_done k (missingBody_end hle)]; rfl

/-- **When `scan` asks to pass over a body, the body is not empty and the request's revealed bytes
end at the body's length** (`fieldMissing` is 0: the controller's runs inside the body are one byte,
`budget_env`). -/
theorem scan_skip_missing (bytes : List Byte) (b : Bool) {n : Nat} {f : Fields} (h : scan bytes b = (.skip n, f)) :
    0 < n ∧ fieldMissing bytes = 0 := by
  rw [scan_eq] at h
  rw [fieldMissing_eq]
  by_cases hl : bytes.length < 3
  · rw [if_pos hl] at h; cases h
  rw [if_neg hl] at h ⊢
  by_cases hk : (bytes.take 2 == [8, 1] && PublicReceive.get bytes 2 == 0x12) = true
  case neg => rw [if_neg hk] at h; cases h
  rw [if_pos hk] at h
  cases hv : varintAt bytes 3 with
  | none => rw [hv] at h; simp only at h; split at h <;> cases h
  | some v =>
    obtain ⟨x, first⟩ := v
    rw [hv] at h
    simp only at h ⊢
    obtain ⟨hn, hk2⟩ := scan_loop_missing bytes b (bytes.length + 1) {} first h
    exact ⟨hn, hk2 _⟩

/-- **The walk of a delivered envelope starts where `scan` finds a `/api/v1/message` body.** At the
byte that completes the body's length of a server request whose path is `/api/v1/message`, the
controller starts walking the envelope: `EnvAt s' [] 0 0 n` with `n` the body's length (the start of
`envRun_safe`), the request's revealed bytes being those bytes. -/
theorem payloadByte_request_envelope {s s' : State} {b : Byte} {done : Bool} {flags : List Byte} {c : Bool}
    {n : Nat} {f : Fields} (hm : s.message = [8, 1]) (hi : s.inner = none) (hs : s.skip = 0)
    (hscan : scan (if s.request.isEmpty = true then [8, 1] else s.request ++ [b]) s.bodySkipped = (.skip n, f))
    (hpath : (f.path == "/api/v1/message".toUTF8.data.toList.map (fun b => BitVec.ofNat 8 b.toNat)) = true)
    (hok : payloadByte s b true done false flags = .ok (s', c)) :
    EnvAt s' [] 0 0 n ∧ s'.request = (if s.request.isEmpty = true then [8, 1] else s.request ++ [b]) := by
  obtain ⟨npos, hmiss⟩ := scan_skip_missing _ _ hscan
  unfold payloadByte at hok
  simp only [hm, hi, l81_82, l81_81, two_beq_one, List.length_cons, List.length_nil, Bool.true_and,
    Bool.false_and, Bool.and_false, Bool.false_eq_true, Bool.not_true, Bool.or_true, Bool.true_or,
    decide_true, decide_false, Nat.lt_irrefl, Nat.reduceAdd, Nat.reduceLT, List.forIn_nil, pure_bind,
    ite_self, beq_self_eq_true, ge_iff_le, Nat.le_refl, Bool.or_false, ↓reduceIte] at hok
  simp only [hscan, hpath, ↓reduceIte] at hok
  rw [bind_ok_iff] at hok
  obtain ⟨s2, hadv, hrest⟩ := hok
  obtain ⟨⟨am, areq⟩, hcase⟩ := envelopeAdvance_ok hadv
  rcases hcase with ⟨bd, -, s2skip, -, hnz⟩ | ⟨n', cf, hq', -⟩
  case inr =>
    have hq : (envelopeScan [] 0).1 = .more true := by rw [envelopeScan_eq]; rfl
    rw [hq] at hq'; cases hq'
  have hi2 := hnz (by omega)
  by_cases g1 : (PublicReceive.get s2.frame 4 == on && PublicReceive.get s2.frame 8 == on &&
      decide ((PublicReceive.get s2.frame 7).toNat < 8) &&
      decide (pendingField s2 > (PublicReceive.get s2.frame 10).toNat * 256 + (PublicReceive.get s2.frame 11).toNat)) = true
  · simp only [g1, ↓reduceIte, throw_bind_ex, throw_ok_iff] at hrest
  simp only [g1, Bool.false_eq_true, ↓reduceIte, pure_bind] at hrest
  cases done
  · simp only [Bool.false_eq_true, ↓reduceIte] at hrest
    cases hrest
    exact ⟨⟨am, hi2, s2skip.trans hs, Nat.zero_le _, by rw [areq]; exact hmiss⟩, areq⟩
  · simp only [↓reduceIte, hi2, Option.isNone_some, Bool.and_false, Bool.false_eq_true, throw_bind_ex,
      throw_ok_iff] at hrest

/-- **A delivered message's envelope, end to end (controller level, every byte string).** At the byte
that completes the body's length of a server request whose path is `/api/v1/message` (the request's
revealed bytes `R`, `scan` asking to pass over `n` bytes), and over the body's `n` bytes `E`, whatever
the controller's moves (`EnvRun`: revealed, passed over, frame headers and control frames between
fragments, stopping), every body byte it reveals has a public class in the reference's reading of
that body (`ReceiveSpec.requestBody` of the path `/api/v1/message`: an envelope). -/
theorem request_envelope_safe {s s' : State} {b : Byte} {done : Bool} {flags : List Byte} {c : Bool}
    {n : Nat} {f : Fields} {E : List Byte} {F : List Bool} (hm : s.message = [8, 1]) (hi : s.inner = none)
    (hs : s.skip = 0)
    (hscan : scan (if s.request.isEmpty = true then [8, 1] else s.request ++ [b]) s.bodySkipped = (.skip n, f))
    (hpath : (f.path == "/api/v1/message".toUTF8.data.toList.map (fun b => BitVec.ofNat 8 b.toNat)) = true)
    (hok : payloadByte s b true done false flags = .ok (s', c)) (hE : E.length = n) (hrun : EnvRun s' E F) :
    f.path = ReceiveSpec.messagePath ∧ SafeFor F (ReceiveSpec.requestBody f.path E) := by
  have hp : f.path = ReceiveSpec.messagePath := beq_iff_eq.mp hpath
  obtain ⟨hat, -⟩ := payloadByte_request_envelope hm hi hs hscan hpath hok
  refine ⟨hp, ?_⟩
  unfold ReceiveSpec.requestBody
  rw [if_pos hp]
  subst hE
  exact envRun_safe hat hrun

/-! ### A server request's own fields (`scan`), byte by byte

The request's revealed bytes grow by the revealed byte (`request := [8, 1]` at the second payload
byte, the kind's), and `skip` is set exactly when `scan` asks to pass over a body. -/

/-- `scan` asks for more: the byte joins the request's revealed bytes; nothing to pass over, no
envelope. -/
theorem payloadByte_request_more {s s' : State} {b : Byte} {done : Bool} {flags : List Byte} {c : Bool}
    {f : Fields} (hm : s.message = [8, 1]) (hi : s.inner = none)
    (hscan : scan (if s.request.isEmpty = true then [8, 1] else s.request ++ [b]) s.bodySkipped = (.more, f))
    (hok : payloadByte s b true done false flags = .ok (s', c)) :
    s'.skip = s.skip ∧ s'.inner = none ∧
      (done = false → s'.request = (if s.request.isEmpty = true then [8, 1] else s.request ++ [b]) ∧
        s'.message = [8, 1] ∧ s'.bodySkipped = s.bodySkipped) := by
  unfold payloadByte at hok
  simp only [hm, hi, l81_82, l81_81, two_beq_one, List.length_cons, List.length_nil, Bool.true_and,
    Bool.false_and, Bool.and_false, Bool.false_eq_true, Bool.not_true, Bool.or_true, Bool.true_or,
    decide_true, decide_false, Nat.lt_irrefl, Nat.reduceAdd, Nat.reduceLT, List.forIn_nil, pure_bind,
    ite_self, beq_self_eq_true, ge_iff_le, Nat.le_refl, Bool.or_false, ↓reduceIte] at hok
  simp only [hscan] at hok
  rcases ite_ok hok with hok | hok
  · simp only [throw_bind_ex, throw_ok_iff] at hok
  cases done
  · simp only [Bool.false_eq_true, ↓reduceIte] at hok
    cases hok
    exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩
  · simp only [↓reduceIte] at hok
    rcases ite_ok hok with hok | hok
    · rcases ite_ok hok with hok | hok
      · cases hok; exact ⟨rfl, rfl, fun e => by cases e⟩
      · simp only [throw_bind_ex, throw_ok_iff] at hok
    · simp only [throw_bind_ex, throw_ok_iff] at hok

/-- **`skip` is set to the body's length exactly when `scan` asks to pass over a body** (a body other
than a delivered message's, which is walked: `payloadByte_request_envelope`). -/
theorem payloadByte_request_skip {s s' : State} {b : Byte} {done : Bool} {flags : List Byte} {c : Bool}
    {n : Nat} {f : Fields} (hm : s.message = [8, 1]) (hi : s.inner = none)
    (hscan : scan (if s.request.isEmpty = true then [8, 1] else s.request ++ [b]) s.bodySkipped = (.skip n, f))
    (hpath : (f.path == "/api/v1/message".toUTF8.data.toList.map (fun b => BitVec.ofNat 8 b.toNat)) = false)
    (hok : payloadByte s b true done false flags = .ok (s', c)) :
    s'.skip = n ∧ 0 < n ∧ s'.inner = none ∧ s'.message = [8, 1] ∧ s'.bodySkipped = true ∧
      s'.request = (if s.request.isEmpty = true then [8, 1] else s.request ++ [b]) := by
  obtain ⟨npos, -⟩ := scan_skip_missing _ _ hscan
  unfold payloadByte at hok
  simp only [hm, hi, l81_82, l81_81, two_beq_one, List.length_cons, List.length_nil, Bool.true_and,
    Bool.false_and, Bool.and_false, Bool.false_eq_true, Bool.not_true, Bool.or_true, Bool.true_or,
    decide_true, decide_false, Nat.lt_irrefl, Nat.reduceAdd, Nat.reduceLT, List.forIn_nil, pure_bind,
    ite_self, beq_self_eq_true, ge_iff_le, Nat.le_refl, Bool.or_false, ↓reduceIte] at hok
  simp only [hscan, hpath, Bool.false_eq_true, ↓reduceIte] at hok
  rcases ite_ok hok with hok | hok
  · simp only [throw_bind_ex, throw_ok_iff] at hok
  cases done
  · simp only [Bool.false_eq_true, ↓reduceIte] at hok
    cases hok
    exact ⟨rfl, npos, rfl, rfl, rfl, rfl⟩
  · have hn : (n == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
    simp only [↓reduceIte, hn, Bool.false_and, Bool.false_eq_true, throw_bind_ex, throw_ok_iff] at hok

/-- A request that `scan` finds malformed is refused at that byte. -/
theorem payloadByte_request_malformed {s : State} {b : Byte} {done : Bool} {flags : List Byte} {f : Fields}
    (hm : s.message = [8, 1]) (hi : s.inner = none)
    (hscan : scan (if s.request.isEmpty = true then [8, 1] else s.request ++ [b]) s.bodySkipped = (.malformed, f))
    (s' : State) (c : Bool) : payloadByte s b true done false flags ≠ .ok (s', c) := by
  intro hok
  unfold payloadByte at hok
  simp only [hm, hi, l81_82, l81_81, two_beq_one, List.length_cons, List.length_nil, Bool.true_and,
    Bool.false_and, Bool.and_false, Bool.false_eq_true, Bool.not_true, Bool.or_true, Bool.true_or,
    decide_true, decide_false, Nat.lt_irrefl, Nat.reduceAdd, Nat.reduceLT, List.forIn_nil, pure_bind,
    ite_self, beq_self_eq_true, ge_iff_le, Nat.le_refl, Bool.or_false, ↓reduceIte] at hok
  simp only [hscan, throw_bind_ex, throw_ok_iff] at hok

/-! ### The frame side: the frame parser's state is the reference parser's

`TlsMpc/KernelSpecs/ParseWebSocketFrame.lean` relates `TlsWebSocketFrame.runByte` on the serialised
state to `TlsWebSocketFrame.step` (`runByte_active`). `frameByte` keeps that relation: if the
controller's frame state is `stateBytes S`, after a revealed byte `b` it is `stateBytes` of
`step S b`, and the byte's event is that step's (`eventBytes`, whose `data`, `controlData`,
`frameDone` are the reference's by `frame_extent`). -/

open TlsMpc.KernelSpecs.ParseWebSocketFrame (Shaped eventBytes runByte_active step_shaped eventBytes_length)

theorem frameRest_frame {s s2 : State} {b : Byte} {ev : List Byte} {S : TlsWebSocketFrame.State Byte}
    (hf : s.frame = TlsWebSocketFrame.stateBytes S) (hS : Shaped S) (h : frameRest s b on = .ok (s2, ev)) :
    s2.frame = TlsWebSocketFrame.stateBytes (TlsWebSocketFrame.step fast capacity S b).state ∧
      ev = eventBytes (TlsWebSocketFrame.step fast capacity S b) ∧
      Shaped (TlsWebSocketFrame.step fast capacity S b).state := by
  have hrun : TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, b]) =
      eventBytes (TlsWebSocketFrame.step fast capacity S b) ++
        TlsWebSocketFrame.stateBytes (TlsWebSocketFrame.step fast capacity S b).state := by
    rw [hf]; exact runByte_active capacity S hS b
  have hsh := step_shaped capacity S b hS
  have hl := eventBytes_length (TlsWebSocketFrame.step fast capacity S b)
  unfold frameRest at h
  by_cases g1 : (s.skip == 0) = true
  case neg => simp only [g1, Bool.false_eq_true, ↓reduceIte, throw_bind_ex, throw_ok_iff] at h
  simp only [g1, ↓reduceIte, pure_bind] at h
  by_cases g2 : (s.pending && s.message.isEmpty && PublicReceive.get s.frame 0 == on) = true
  · simp only [g2, ↓reduceIte, hrun] at h
    rcases ite_ok h with h | h
    · cases h
      exact ⟨List.drop_left' hl, List.take_left' hl, hsh⟩
    · simp only [throw_bind_ex, throw_ok_iff] at h
  · simp only [g2, Bool.false_eq_true, ↓reduceIte, hrun] at h
    rcases ite_ok h with h | h
    · cases h
      exact ⟨List.drop_left' hl, List.take_left' hl, hsh⟩
    · simp only [throw_bind_ex, throw_ok_iff] at h

/-- **(i) The frame parser's state, kept by `step`'s frame side.** Once upgraded, if the controller's
frame state is the serialisation of a (shaped) reference state `S`, then after a revealed byte `b`
it is the serialisation of `TlsWebSocketFrame.step S b`, and the event `payloadByte` is given is
that step's event. -/
theorem frameByte_frame {s s1 : State} {b : Byte} {ev : List Byte} {S : TlsWebSocketFrame.State Byte}
    (hu : s.upgraded = true) (hf : s.frame = TlsWebSocketFrame.stateBytes S) (hS : Shaped S)
    (h : frameByte s b = .ok (s1, ev)) :
    s1.frame = TlsWebSocketFrame.stateBytes (TlsWebSocketFrame.step fast capacity S b).state ∧
      ev = eventBytes (TlsWebSocketFrame.step fast capacity S b) ∧
      Shaped (TlsWebSocketFrame.step fast capacity S b).state := by
  rw [frameByte_split, frameUpgrade_eq, bind_ok_iff] at h
  obtain ⟨⟨a, s0⟩, h1, h2⟩ := h
  unfold upgradePart at h1
  rw [if_pos hu] at h1
  cases h1
  exact frameRest_frame hf hS h2

/-! ### A response's own fields (`replyScan`), byte by byte

The response's revealed bytes grow by the revealed byte, and `skip` is set exactly when `replyScan`
asks to pass over its body (the response parser's feed, which runs first, changes neither). -/

theorem l82_81 : (([8, 2] : List Byte) == [8, 1]) = false := by decide
theorem l82_82 : (([8, 2] : List Byte) == [8, 2]) = true := by decide

/-- **`skip` is set to a response body's length exactly when `replyScan` asks to pass over it**
(the message not ending at this byte). -/
theorem payloadByte_reply_skip {s s' : State} {b : Byte} {flags : List Byte} {c : Bool}
    {n : Nat} {f : ReplyFields} (hm : s.message = [8, 2])
    (hscan : replyScan (if s.reply.isEmpty = true then [8, 2] else s.reply ++ [b]) s.replySkipped s.openBody =
      (.skip n, f))
    (hok : payloadByte s b true false false flags = .ok (s', c)) :
    s'.skip = n ∧ s'.reply = (if s.reply.isEmpty = true then [8, 2] else s.reply ++ [b]) ∧
      s'.replySkipped = true ∧ s'.message = [8, 2] := by
  unfold payloadByte at hok
  simp only [hm, l82_81, l82_82, two_beq_one, List.length_cons, List.length_nil, Bool.true_and,
    Bool.false_and, Bool.and_false, Bool.false_eq_true, Bool.not_true, Bool.or_true, Bool.true_or,
    decide_true, decide_false, Nat.lt_irrefl, Nat.reduceAdd, Nat.reduceLT, pure_bind, ite_self,
    beq_self_eq_true, ge_iff_le, Nat.le_refl, Bool.or_false, ↓reduceIte, List.nil_append] at hok
  rcases ite_ok hok with hok | hok
  · rw [bind_ok_iff] at hok
    obtain ⟨r1, hfor, hrest⟩ := hok
    have hP := forIn_keeps (fun t => t.message = [8, 2] ∧ t.reply = s.reply ∧ t.replySkipped = s.replySkipped ∧
        t.openBody = s.openBody) _
      (by
        intro x r0 r' hP0 e
        rcases ite_ok e with e | e
        · rcases ite_ok e with e | e
          · rcases ite_ok e with e | e
            · rcases ite_ok e with e | e
              · cases e; exact hP0
              · simp only [throw_bind_ex, throw_ok_iff] at e
            · cases e; exact hP0
          · simp only [throw_bind_ex, throw_ok_iff] at e
        · cases e; exact hP0)
      _ _ _ ⟨rfl, rfl, rfl, rfl⟩ hfor
    obtain ⟨p1, p2, p3, p4⟩ := hP
    simp only [p1, p2, p3, p4, hscan, l82_82, l82_81, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hrest
    repeat' (first
      | (simp only [throw_bind_ex, throw_ok_iff] at hrest; done)
      | (cases hrest; exact ⟨rfl, rfl, rfl, by first | rfl | exact p1⟩)
      | (rcases ite_ok hrest with hrest | hrest))
  · simp only [hscan, l82_82, l82_81, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hok
    repeat' (first
      | (simp only [throw_bind_ex, throw_ok_iff] at hok; done)
      | (cases hok; exact ⟨rfl, rfl, rfl, rfl⟩)
      | (rcases ite_ok hok with hok | hok))

/-- `replyScan` asks for more: the byte joins the response's revealed bytes; `skip` is unchanged
(the message not ending at this byte). -/
theorem payloadByte_reply_more {s s' : State} {b : Byte} {flags : List Byte} {c : Bool}
    {f : ReplyFields} (hm : s.message = [8, 2])
    (hscan : replyScan (if s.reply.isEmpty = true then [8, 2] else s.reply ++ [b]) s.replySkipped s.openBody =
      (.more, f))
    (hok : payloadByte s b true false false flags = .ok (s', c)) :
    s'.skip = s.skip ∧ s'.reply = (if s.reply.isEmpty = true then [8, 2] else s.reply ++ [b]) ∧
      s'.replySkipped = s.replySkipped ∧ s'.message = [8, 2] := by
  unfold payloadByte at hok
  simp only [hm, l82_81, l82_82, two_beq_one, List.length_cons, List.length_nil, Bool.true_and,
    Bool.false_and, Bool.and_false, Bool.false_eq_true, Bool.not_true, Bool.or_true, Bool.true_or,
    decide_true, decide_false, Nat.lt_irrefl, Nat.reduceAdd, Nat.reduceLT, pure_bind, ite_self,
    beq_self_eq_true, ge_iff_le, Nat.le_refl, Bool.or_false, ↓reduceIte, List.nil_append] at hok
  rcases ite_ok hok with hok | hok
  · rw [bind_ok_iff] at hok
    obtain ⟨r1, hfor, hrest⟩ := hok
    have hP := forIn_keeps (fun t => t.message = [8, 2] ∧ t.reply = s.reply ∧ t.replySkipped = s.replySkipped ∧
        t.openBody = s.openBody ∧ t.skip = s.skip) _
      (by
        intro x r0 r' hP0 e
        rcases ite_ok e with e | e
        · rcases ite_ok e with e | e
          · rcases ite_ok e with e | e
            · rcases ite_ok e with e | e
              · cases e; exact hP0
              · simp only [throw_bind_ex, throw_ok_iff] at e
            · cases e; exact hP0
          · simp only [throw_bind_ex, throw_ok_iff] at e
        · cases e; exact hP0)
      _ _ _ ⟨rfl, rfl, rfl, rfl, rfl⟩ hfor
    obtain ⟨p1, p2, p3, p4, p5⟩ := hP
    simp only [p1, p2, p3, p4, hscan, l82_82, l82_81, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hrest
    repeat' (first
      | (simp only [throw_bind_ex, throw_ok_iff] at hrest; done)
      | (cases hrest; exact ⟨by first | rfl | exact p5, rfl, by first | rfl | exact p3, by first | rfl | exact p1⟩)
      | (rcases ite_ok hrest with hrest | hrest))
  · simp only [hscan, l82_82, l82_81, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hok
    repeat' (first
      | (simp only [throw_bind_ex, throw_ok_iff] at hok; done)
      | (cases hok; exact ⟨rfl, rfl, rfl, rfl⟩)
      | (rcases ite_ok hok with hok | hok))

end ReceiveProofs
