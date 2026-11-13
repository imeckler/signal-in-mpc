import TlsMpc.Node.Policy.Receive
import TlsMpc.Node.Policy.ReceiveSpec

/-!
# T1: the controller reveals only what the reference allows (proof track P1)

REORGANIZATION_PLAN.md section 8, T1. New file; it changes no definition. No emitter or executable
imports it.

## The record loop, modelled

The controller's `record` (handshake_backend/EmpHybridWork/PublicServiceController.lean) walks one
authenticated record. While `skip > 0` it passes over `min skip (bytes left)` bytes unrevealed
(`passBulk` as far as `passRoom` allows, then `passOne`). Otherwise it requires `mayReveal`, has the
engines reveal the next `budget s` bytes (fewer at the record's end), and then runs `step` on each
of them, checking after each byte but the last that the rest of the run is still within
`mayReveal`/`budget` of the new state. **The bytes are revealed before they are checked**: a run is
sound only if every byte of it may be revealed whatever the bytes before it in the run turn out to
be. `recordLoop` is that loop (`streamRun`: record after record, the state carried over), and its
`revealed` list is every stream position the engines revealed, including those of a run whose
check then failed.

(The section 8 statement of T1 restricts to runs "that do not throw". That is too weak: a policy
that revealed everything in one run and threw at the first body byte would satisfy it. The
statements below are about every revealed position.)

## What is proved (standard axioms only: propext, Classical.choice, Quot.sound)

**Passing over (any stream, any record boundaries).** Once the policy has set `skip = n`, the next
`n` stream positions are never revealed: `recordLoop_skip` (within a record), `recordLoop_skip_end`
(a record ending inside a body leaves `skip` lowered by exactly the bytes passed), `go_skip` (across
any later records). With `mayReveal_skip`, `passOne_skip`, `passRun_skip`, `passBulk_skip`.

**The body of a server request is found exactly, and no run reaches it** (`request_body_unrevealed`,
from `scan_requestHead`, `requestHead_prefix`, `budget_request`). For every server request in the
server's layout (verb, path, body, ...), whatever its verb and path bytes and however its lengths are
encoded as varints (at most 10 bytes, any encoding): on every proper prefix of its revealed bytes up
to the end of the body's length, `scan` neither skips nor refuses, and the controller's run (`budget`)
ends at or before the body's first byte; at the end of the body's length, `scan` returns
`skip n` (the body's length). With `go_skip`: no byte of the body is revealed.

**The same for a response** (`response_body_unrevealed`, from `replyScan_responseHead`,
`responseHead_prefix`, `budget_response`): id, status, message, body. The body of the `200` to a
prekey fetch (the contact's bundle) and of a 409/410 (the contact's devices) is passed over whole.

**Too-long varints are refused** (the P1 fix): `varintAt_tooLong`, `scanBody_tooLong`,
`scan_wrapper_tooLong`, `replyScanBody_tooLong`, `replyScan_wrapper_tooLong`; end to end on the two
former counterexamples, `ReceiveTest.overlongRequest_refused`, `overlongResponse_refused`,
`overlong_T1` (kernel-checked runs of the loop).

The scanners' `for` loops are rewritten as plain functions (`scan_eq`, `fieldMissing_eq`,
`replyScan_eq`, `replyBudget_eq`: the loop bodies are written out and checked by `rfl`).

`T1` states the property for every stream (with the one-byte allowance after the first malformed
byte; it stays: a response's next key and the byte after it are revealed in one run).

## What is proved elsewhere, and what is not proved

**`T1` for every stream is proved: `ReceiveLoop.t1_all`** (standard axioms only):

    ∀ (openBody : Bool) (accept : List Byte) (lenient : Bool) (records : List (List Byte)),
      T1 openBody { PublicReceive.start accept with upgraded := true, lenient, openBody } records

(`ReceiveTest.upgraded openBody` is the case `accept = []`, `lenient = true`), and more generally
`ReceiveLoop.t1_frames`: `T1 openBody s records` for every state `s` that simulates the reference's
initial state (`ReceiveSim.Sim openBody s Stream.init _`). Its parts: `ReceiveLoop.run_safe` (every
run, every state the loop reaches, every byte string), `loop_good` (one record, with `stepWindow` and
`passBulk`/`passOne`), `go_good` (records); `ReceiveSim.sim_step`, `sim_pass` (the simulation kept by
every accepted and every passed byte); `ReceiveComplete` (`complete = true`); `ReceiveEnvDone`
(delivered envelopes walked to their end have no `error`).

**What is not proved.**

* The fresh connection: from `PublicReceive.start accept` (not upgraded: the HTTP head first)
  against `ReceiveSpec.classify` (head, then frames). `ReceiveHead` has the head's runs
  (`upgrade_run_safe`, `frameByte_terminator`); still missing are that the frame parser is at a
  frame boundary when the head ends (the head's bytes leave it alone) and the composition of the two.
* `recordLoop` is a pure model of the controller's loop (`TlsMpc/Node/Session/Common.lean`,
  `record`, in `SessionM`); the theorems are about the model. The real loop has the same structure
  (`passBulk (min count passRoom)` then `passOne` one at a time; `insist mayReveal`; a run of
  `budget s` bytes; `step` on each, with the same check of the rest of the run; `envelopes := []`
  after each step), and differs in: the engines' `revealRange` returns the run and the record's
  length (the model takes `(bytes.drop offset).take (budget s)` of a known record); a completed
  envelope is handed to `Context.envelope` (which may throw) before `envelopes := []`; it has no fuel.
  Between records the session also applies `replies`, `requests := []` and `expect`; `Sim` depends
  on the state only through `view` (`ReceiveSim.sim_congr`), which `requests := []` and `expect` keep
  (`ReceiveLoop.view_requests`, `view_expect`) and `replies` keeps by construction (it returns
  `{ s with control := _ }`: `view_control`; the lemma about `replies` itself is not proved), but
  `t1_all` is stated for `streamRun`, which does not apply them.

The parts, in the files that prove them:

* Here: passing over (`go_skip`), the server's layouts (`request_body_unrevealed`,
  `response_body_unrevealed`), too-long varints refused.
* `Policy/ReceiveEnvelope.lean`, `Policy/ReceiveInvariant.lean`: delivered envelopes, scanner level
  (`envelope_payload_unrevealed`) and controller level (`envRun_safe`, `request_envelope_safe`); the
  per-byte glue for requests (`payloadByte_request_*`) and the frame side (`frameByte_frame`).
* `Policy/ReceiveStream.lean` (item 1): the reference byte by byte, equal to the recursive one for
  every stream (`classifyFrames_stream`, `classify_stream`); a byte's class depends only on the bytes
  before it, and on the message's length when it is complete (`message_causal`, `message_prefix`,
  `message_at`).
* `Policy/ReceiveReply.lean` (item 2, responses): every field order, every byte string, with or
  without `openBody`. The controller's view `RShape` is kept by every byte the scanner accepts and every
  body it passes over (`rshape_more`, `rshape_skip`); every run `replyBudget` allows from it is public,
  or ends at the reference's first `error` (`rshape_budget`). Controller level: `ReplyIn`,
  `payloadByte_replyIn`, `stepPassed_replyIn`, `reply_run_safe`.
* `Policy/ReceiveRequestScan.lean` (item 2, requests): the same for `scan` and `fieldMissing`, every
  field order, delivered message or not (`qshape_more`, `qshape_skip`, `qshape_run`: every run inside a
  request is public); controller level `QIn`, `payloadByte_qIn`, `stepSkipped_qIn`, `request_run_safe`.
* `Policy/ReceiveFrame.lean` (item 3, part): every header byte at which the reference enters its error
  state is refused by the frame parser and by `frameByte` (`first_reject`, `second_reject`,
  `extLo_reject`, `frameByte_reject`).
* `Policy/ReceiveHead.lean` (item 5): before the upgrade, every run stays inside the HTTP head
  (`upgrade_run_safe`, `frameByte_terminator`).

* `Policy/ReceiveSimFrame.lean`, `ReceiveSimByte.lean`, `ReceiveSim.lean` (T1 item 1): the
  frame-position simulation `ReceiveSim.Sim` (frame parser against `Stream.Phase`: `frame_sim_step`;
  the message state across fragments and control frames: `MsgSim`; `payloadByte` decomposed and
  depending only on `view`: `payloadByte_eq`, `payloadByte_view`), kept by every accepted byte
  (`sim_step`) and every passed byte (`sim_pass`, any byte value).
* `Policy/ReceiveComplete.lean` (item 2): `complete = true` (`rshape_run_c`, `rshape_noerr_c`,
  `qshape_run_c`, `qshape_noerr_c`, `qshape_body_c`; the open field from `replyMissing_fields`,
  `fieldMissing_open`).
* `Policy/ReceiveEnvDone.lean` (item 3): `envelope_noErr`, `envWalk_noErr`.
* `Policy/ReceiveLoop.lean` (item 4): `run_safe`, `window_sim`, `pass_sim`, `loop_good`, `go_good`,
  `t1_frames`, `start_sim`, `t1_all`.
-/

namespace ReceiveProofs

open PublicReceive

/-! ### The loop -/

/-- The controller's check of a revealed run: `step` each byte; after each but the last, the rest
of the run must be within `mayReveal` and `budget` of the new state. -/
def stepWindow (s : State) : List Byte → Except String State
  | [] => .ok s
  | b :: rest => do
    let (next, _) ← step s b
    if rest.isEmpty then pure next
    else if mayReveal next && decide (rest.length ≤ budget next) then stepWindow next rest
    else throw "revealed range went past what may be revealed"

/-- One record (`bytes`), from `offset`; `base` is the record's position in the stream; `acc` the
positions revealed so far. Returns every revealed position and the final state or the error. -/
def recordLoop : (fuel : Nat) → State → (bytes : List Byte) → (offset base : Nat) → List Nat →
    List Nat × Except String State
  | 0, s, _, _, _, acc => (acc, .ok s)
  | fuel + 1, s, bytes, offset, base, acc =>
    if offset < bytes.length then
      if s.skip > 0 then
        -- A body: passed over, never revealed.
        let count := min s.skip (bytes.length - offset)
        let bulk := min count (passRoom s)
        match passRun (count - bulk) (passBulk bulk s) with
        | .error e => (acc, .error e)
        | .ok (s, _) => recordLoop fuel { s with envelopes := [] } bytes (offset + count) base acc
      else if !mayReveal s then (acc, .error "refusing to reveal a server-initiated message")
      else
        -- The engines reveal the run first; the controller checks it byte by byte afterwards.
        let run := (bytes.drop offset).take (budget s)
        let acc := acc ++ (List.range run.length).map (base + offset + ·)
        if run.isEmpty then (acc, .error "missing revealed bytes") else
        match stepWindow s run with
        | .error e => (acc, .error e)
        | .ok s => recordLoop fuel { s with envelopes := [] } bytes (offset + run.length) base acc
    else (acc, .ok s)

/-- Record after record, the state carried over: every stream position revealed, and the final
state or the first error (after which nothing more is revealed). -/
def streamRun (s : State) (records : List (List Byte)) : List Nat × Except String State :=
  go s records 0 []
where
  go (s : State) : List (List Byte) → Nat → List Nat → List Nat × Except String State
    | [], _, acc => (acc, .ok s)
    | r :: rs, base, acc =>
      match recordLoop (r.length + 1) s r 0 base acc with
      | (acc, .error e) => (acc, .error e)
      | (acc, .ok s) => go s rs (base + r.length) acc

/-- **T1, for every stream.** From state `s`, over a stream of frames cut into `records` (any
cut), every position the record loop reveals is allowed by the reference
(`ReceiveSpec.classifyFrames`), or is the one byte right after the first malformed byte (the
allowance: the controller reveals a run before checking it, and a response's next key and the
byte after it are one run). Checked on generated streams by `ReceiveTest.checks`; its parts are
proved below. -/
def T1 (openBody : Bool) (s : State) (records : List (List Byte)) : Prop :=
  ∀ q ∈ (streamRun s records).1,
    ReceiveSpec.allowedIn (ReceiveSpec.classifyFrames openBody records.flatten) q = true ∨
      ReceiveSpec.firstError (ReceiveSpec.classifyFrames openBody records.flatten) = some q

instance (openBody : Bool) (s : State) (records : List (List Byte)) : Decidable (T1 openBody s records) := by
  unfold T1; infer_instance

/-! ### Passing over: a body being passed over is never revealed

Once the policy has set `skip = n` (a body's or an envelope payload's length, at the byte where
the length ends), the next `n` bytes of the stream are passed over: the loop reveals none of them,
whatever the record boundaries (`recordLoop_skip`, `go_skip`). Each passed byte lowers `skip` by
one (`passOne_skip`, `passRun_skip`), also in bulk (`passBulk`). -/

/-- The loop reveals nothing while `skip > 0`. -/
theorem mayReveal_skip {s : State} (h : mayReveal s = true) : s.skip = 0 := by
  unfold mayReveal at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem stepPassed_skip {s s' : State} {d : Bool} (h : stepPassed s = .ok (s', d)) : s'.skip = s.skip - 1 := by
  unfold stepPassed at h
  generalize TlsMpc.TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0]) = F at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  by_cases c1 : (s.upgraded && decide (s.skip > 0) && s.message == [8, 2]) = true
  · rw [if_pos c1] at h
    by_cases c2 : (PublicReceive.get F 0 == on && PublicReceive.get F 1 == on) = true
    · rw [if_pos c2] at h
      repeat' (split at h)
      all_goals (try simp only [reduceCtorEq] at h)
      all_goals (try (cases h; rfl))
      all_goals simp_all
    · rw [if_neg c2] at h; cases h
  · rw [if_neg c1] at h; cases h

/-- Passing a request body byte lowers `skip` by one, except at the last byte of a delivered
envelope's payload, where the walk of the envelope may set the next payload's length. -/
theorem stepSkipped_skip {s s' : State} (h : stepSkipped s = .ok s') (h2 : 2 ≤ s.skip) : s'.skip = s.skip - 1 := by
  have h3 : (s.skip - 1 == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
  unfold stepSkipped at h
  generalize TlsMpc.TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0]) = F at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, h3] at h
  repeat' (split at h)
  all_goals (try simp only [reduceCtorEq] at h)
  all_goals (try (cases h; rfl))
  all_goals simp_all

theorem passOne_skip {s s' : State} {d : Bool} (h : passOne s = .ok (s', d)) (h2 : 2 ≤ s.skip) :
    s'.skip = s.skip - 1 := by
  unfold passOne at h
  split at h
  · exact stepPassed_skip h
  · simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · next v hv => cases h; exact stepSkipped_skip hv h2

theorem passRun_skip : ∀ (k : Nat) (s s' : State) (d : Bool), passRun k s = .ok (s', d) → k < s.skip →
    s'.skip = s.skip - k
  | 0, s, s', d, h, _ => by cases h; rfl
  | k + 1, s, s', d, h, hk => by
    simp only [passRun, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · next r1 h1 =>
      obtain ⟨s1, d1⟩ := r1
      split at h
      · cases h
      · next r2 h2 =>
        obtain ⟨s2, d2⟩ := r2
        cases h
        have e1 := passOne_skip h1 (by omega)
        have e2 := passRun_skip k s1 s2 d2 h2 (by omega)
        dsimp only
        omega

theorem passBulk_skip (k : Nat) (s : State) : (passBulk k s).skip = s.skip - k := by
  unfold passBulk
  split
  · next h => subst h; rfl
  · rfl

/-- The record loop reveals only positions of the record, at or after where it starts. -/
theorem recordLoop_ge : ∀ (fuel : Nat) (s : State) (bytes : List Byte) (offset base : Nat) (acc : List Nat),
    ∀ q ∈ (recordLoop fuel s bytes offset base acc).1, q ∈ acc ∨ (base + offset ≤ q ∧ q < base + bytes.length)
  | 0, s, bytes, offset, base, acc, q, hq => Or.inl hq
  | fuel + 1, s, bytes, offset, base, acc, q, hq => by
    unfold recordLoop at hq
    dsimp only at hq
    split at hq
    · split at hq
      · split at hq
        · exact Or.inl hq
        · rcases recordLoop_ge fuel _ bytes _ base acc q hq with h | h
          · exact Or.inl h
          · exact Or.inr (by omega)
      · split at hq
        · exact Or.inl hq
        · have widen : ∀ q, q ∈ acc ++ (List.range ((bytes.drop offset).take (budget s)).length).map
              (base + offset + ·) → q ∈ acc ∨ (base + offset ≤ q ∧ q < base + bytes.length) := by
            intro q hq
            rcases List.mem_append.mp hq with h | h
            · exact Or.inl h
            · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
              have := List.mem_range.mp hi
              simp only [List.length_take, List.length_drop] at this
              exact Or.inr ⟨by omega, by omega⟩
          split at hq
          · exact widen q hq
          · split at hq
            · exact widen q hq
            · rcases recordLoop_ge fuel _ bytes _ base _ q hq with h | h
              · exact widen q h
              · exact Or.inr ⟨by omega, h.2⟩
    · exact Or.inl hq

/-- **No passed-over byte is revealed (one record).** If the loop reaches `offset` of a record with
`skip > 0`, it reveals none of the next `min skip (bytes left)` positions. -/
theorem recordLoop_skip (fuel : Nat) (s : State) (bytes : List Byte) (offset base : Nat) (acc : List Nat)
    (hs : 0 < s.skip) (ho : offset < bytes.length) :
    ∀ q ∈ (recordLoop (fuel + 1) s bytes offset base acc).1,
      q ∈ acc ∨ (base + offset + min s.skip (bytes.length - offset) ≤ q ∧ q < base + bytes.length) := by
  intro q hq
  unfold recordLoop at hq
  rw [if_pos ho, if_pos hs] at hq
  dsimp only at hq
  split at hq
  · exact Or.inl hq
  · rcases recordLoop_ge fuel _ bytes _ base acc q hq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨by omega, h.2⟩

/-- When a record ends inside a body (`skip` more than the bytes left), the loop ends the record
with `skip` lowered by exactly the bytes it passed. -/
theorem recordLoop_skip_end (fuel : Nat) (s s' : State) (bytes : List Byte) (offset base : Nat)
    (acc acc' : List Nat) (ho : offset < bytes.length) (hs : bytes.length - offset < s.skip)
    (h : recordLoop (fuel + 2) s bytes offset base acc = (acc', .ok s')) :
    s'.skip = s.skip - (bytes.length - offset) ∧ acc' = acc := by
  unfold recordLoop at h
  rw [if_pos ho, if_pos (by omega)] at h
  have hc : min s.skip (bytes.length - offset) = bytes.length - offset := by omega
  simp only [hc] at h
  split at h
  · cases h
  · next s1 d1 hr =>
    unfold recordLoop at h
    rw [if_neg (by omega)] at h
    cases h
    have hb := passBulk_skip (min (bytes.length - offset) (passRoom s)) s
    have hr' := passRun_skip _ _ _ _ hr (by rw [hb]; omega)
    refine ⟨?_, rfl⟩
    dsimp only
    rw [hr', hb]; omega

/-- `streamRun.go` reveals only positions at or after `base`. -/
theorem go_ge : ∀ (records : List (List Byte)) (s : State) (base : Nat) (acc : List Nat),
    ∀ q ∈ (streamRun.go s records base acc).1, q ∈ acc ∨ base ≤ q
  | [], s, base, acc, q, hq => Or.inl hq
  | r :: rs, s, base, acc, q, hq => by
    unfold streamRun.go at hq
    split at hq
    · next acc1 e h1 =>
      have := recordLoop_ge (r.length + 1) s r 0 base acc q
      rw [h1] at this
      rcases this hq with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    · next acc1 s1 h1 =>
      rcases go_ge rs s1 (base + r.length) acc1 q hq with h | h
      · have := recordLoop_ge (r.length + 1) s r 0 base acc q
        rw [h1] at this
        rcases this h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (by omega)
      · exact Or.inr (by omega)

/-- **No passed-over byte is revealed (across records).** If the loop starts a record at stream
position `base` with `skip = n`, none of the stream positions `base, …, base + n - 1` is ever
revealed, however the rest of the stream is cut into records. -/
theorem go_skip : ∀ (records : List (List Byte)) (s : State) (base : Nat) (acc : List Nat),
    ∀ q ∈ (streamRun.go s records base acc).1, q ∈ acc ∨ base + s.skip ≤ q
  | [], s, base, acc, q, hq => Or.inl hq
  | r :: rs, s, base, acc, q, hq => by
    by_cases hz : s.skip = 0
    · rcases go_ge (r :: rs) s base acc q hq with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    by_cases hr : r.length = 0
    · have e : recordLoop (r.length + 1) s r 0 base acc = (acc, .ok s) := by
        rw [hr]; unfold recordLoop; rw [if_neg (by omega)]
      unfold streamRun.go at hq
      rw [e] at hq
      have := go_skip rs s (base + r.length) acc q hq
      rw [hr] at this
      simpa using this
    have here := recordLoop_skip r.length s r 0 base acc (by omega) (by omega)
    unfold streamRun.go at hq
    split at hq
    · next acc1 err h1 =>
      rw [h1] at here
      rcases here q hq with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    · next acc1 s1 h1 =>
      rw [h1] at here
      rcases go_skip rs s1 (base + r.length) acc1 q hq with h | h
      · rcases here q h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (by omega)
      · by_cases hle : s.skip ≤ r.length
        · exact Or.inr (by omega)
        · have e : r.length + 1 = (r.length - 1) + 2 := by omega
          rw [e] at h1
          have := (recordLoop_skip_end (r.length - 1) s s1 r 0 base acc acc1 (by omega) (by omega) h1).1
          exact Or.inr (by omega)

/-! ### The scanners' loops as functions

`scan` (and the other scanners) walk the revealed bytes in a `for _ in [0:n]` loop with early
returns. `loopG` is such a loop as a plain function of its body; `scan_eq` rewrites `scan` with it,
its body being `scanBody` (the elaborated loop body, written out: `rfl`). -/

abbrev LoopState (α : Type) := MProd (Option (Need × α)) (MProd α Nat)

/-- A loop whose body ignores the index, as a function of the number of rounds. -/
def loopG {β : Type} (g : β → ForInStep β) : Nat → β → β
  | 0, b => b
  | n + 1, b => match g b with
    | .done b => b
    | .yield b => loopG g n b

theorem forIn_ignore {β : Type} (g : β → ForInStep β) : ∀ (l : List Nat) (f : Nat → β → Id (ForInStep β)),
    (∀ x b, f x b = g b) → ∀ init : β, forIn l init f = loopG g l.length init
  | [], f, _, init => rfl
  | x :: l, f, hf, init => by
    rw [List.forIn_cons, hf]
    simp only [List.length_cons, loopG]
    cases g init with
    | done b => rfl
    | yield b => exact forIn_ignore g l f hf b

theorem forIn_range (n : Nat) {β : Type} (f : Nat → β → Id (ForInStep β)) (i : β) :
    forIn [:n] i f = forIn (List.range' 0 n) i f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp [Std.Legacy.Range.size]

/-- One round of `scan`'s loop. -/
def scanBody (bytes : List Byte) (bodySkipped : Bool) (r : LoopState Fields) : ForInStep (LoopState Fields) :=
  if r.snd.snd ≥ bytes.length then .done ⟨some (.more, r.snd.fst), r.snd.fst, r.snd.snd⟩ else
  if (get bytes r.snd.snd).toNat == 0x20 then
    match varintAt bytes (r.snd.snd + 1) with
    | some (value, next) => .yield ⟨none, { r.snd.fst with id := some value }, next⟩
    | _ => .done ⟨some (if varintTooLong bytes (r.snd.snd + 1) then .malformed else .more, r.snd.fst), r.snd.fst, r.snd.snd⟩
  else if ((get bytes r.snd.snd).toNat == 0x0a || (get bytes r.snd.snd).toNat == 0x12 ||
      (get bytes r.snd.snd).toNat == 0x2a) then
    match varintAt bytes (r.snd.snd + 1) with
    | some (count, next) =>
      if next + count > bytes.length then .done ⟨some (.more, r.snd.fst), r.snd.fst, r.snd.snd⟩ else
      if (get bytes r.snd.snd).toNat == 0x0a then
        if (get bytes r.snd.snd).toNat == 0x12 then
          .yield ⟨none, { r.snd.fst with verb := (bytes.drop next).take count, path := (bytes.drop next).take count }, next + count⟩
        else .yield ⟨none, { r.snd.fst with verb := (bytes.drop next).take count }, next + count⟩
      else
        if (get bytes r.snd.snd).toNat == 0x12 then
          .yield ⟨none, { r.snd.fst with path := (bytes.drop next).take count }, next + count⟩
        else .yield ⟨none, r.snd.fst, next + count⟩
    | _ => .done ⟨some (if varintTooLong bytes (r.snd.snd + 1) then .malformed else .more, r.snd.fst), r.snd.fst, r.snd.snd⟩
  else if (get bytes r.snd.snd).toNat == 0x1a then
    match varintAt bytes (r.snd.snd + 1) with
    | some (count, next) =>
      if r.snd.fst.body.isSome then .done ⟨some (.malformed, r.snd.fst), r.snd.fst, r.snd.snd⟩ else
      if next == bytes.length && !bodySkipped && decide (count > 0) then
        .done ⟨some (.skip count, { r.snd.fst with body := some count }), { r.snd.fst with body := some count }, r.snd.snd⟩
      else .yield ⟨none, { r.snd.fst with body := some count }, next⟩
    | _ => .done ⟨some (if varintTooLong bytes (r.snd.snd + 1) then .malformed else .more, r.snd.fst), r.snd.fst, r.snd.snd⟩
  else .done ⟨some (.malformed, r.snd.fst), r.snd.fst, r.snd.snd⟩

/-- The result of a scanner's loop. -/
def loopResult {α : Type} (r : LoopState α) : Need × α :=
  match r.fst with
  | none => (.more, r.snd.fst)
  | some a => a

theorem scan_eq (bytes : List Byte) (b : Bool) : scan bytes b =
    if bytes.length < 3 then (.more, {}) else
    if (bytes.take 2 == [8, 1] && get bytes 2 == 0x12) = true then
      match varintAt bytes 3 with
      | some (_, first) => loopResult (loopG (scanBody bytes b) (bytes.length + 1) ⟨none, {}, first⟩)
      | none => (if varintTooLong bytes 3 then .malformed else .more, {})
    else (.malformed, {}) := by
  unfold scan
  simp only [Id.run, forIn_range]
  by_cases h1 : bytes.length < 3
  · simp only [h1, if_true]; rfl
  by_cases h2 : (bytes.take 2 == [8, 1] && get bytes 2 == 0x12) = true
  · simp only [h1, h2, if_true, if_false]
    cases hv : varintAt bytes 3 with
    | none => rfl
    | some v =>
      obtain ⟨_, first⟩ := v
      dsimp only
      rw [forIn_ignore (scanBody bytes b) _ _ ?hf, List.length_range']
      · unfold loopResult
        generalize loopG (scanBody bytes b) (bytes.length + 1) ⟨none, {}, first⟩ = r
        obtain ⟨fst, snd⟩ := r
        cases fst <;> rfl
      · intro x r; rfl
  · simp only [h1, h2, if_false]; rfl

/-! ### Varints -/

/-- `v` is a varint encoding of `n`: every byte but the last has its top bit set. (Any such
encoding, not only the shortest.) -/
inductive Varint : List Byte → Nat → Prop
  | last {b : Byte} : b.toNat < 128 → Varint [b] b.toNat
  | cont {b : Byte} {rest : List Byte} {n : Nat} : 128 ≤ b.toNat → Varint rest n →
      Varint (b :: rest) (b.toNat % 128 + 128 * n)

theorem get_of_drop {bytes : List Byte} {pos : Nat} {b : Byte} {rest : List Byte}
    (h : bytes.drop pos = b :: rest) : PublicReceive.get bytes pos = b := by
  unfold PublicReceive.get
  rw [List.getD_eq_getElem?_getD, ← List.head?_drop, h]
  rfl

theorem length_of_drop {bytes l : List Byte} {pos : Nat} (h : bytes.drop pos = l) (hl : l ≠ []) :
    bytes.length = pos + l.length := by
  have e := congrArg List.length h
  rw [List.length_drop] at e
  have : pos < bytes.length := by
    apply Classical.byContradiction; intro hc
    rw [List.drop_eq_nil_of_le (by omega)] at h; exact hl h.symm
  omega

theorem varint_go (bytes : List Byte) : ∀ {v : List Byte} {n : Nat}, Varint v n →
    ∀ (fuel pos shift acc : Nat) (rest : List Byte), v.length ≤ fuel → bytes.drop pos = v ++ rest →
    varintAt.go bytes fuel pos shift acc = some (acc + n * 2 ^ shift, pos + v.length)
  | _, _, .last (b := b) hb, fuel + 1, pos, shift, acc, rest, _, h => by
    have hlen := length_of_drop h (by simp)
    have hg := get_of_drop (by simpa using h)
    unfold varintAt.go
    simp only [hlen, List.length_append, List.length_singleton, hg]
    rw [if_neg (by omega), if_pos (by omega)]
    simp only [Nat.mod_eq_of_lt hb]
  | _, _, .last _, 0, _, _, _, _, hl, _ => by simp at hl
  | _, _, .cont (b := b) (rest := r) (n := n) hb hr, fuel + 1, pos, shift, acc, rest, hl, h => by
    have hlen := length_of_drop h (by simp)
    have hg := get_of_drop (by simpa using h)
    unfold varintAt.go
    simp only [hlen, List.length_append, List.length_cons, hg]
    rw [if_neg (by omega), if_neg (by omega)]
    have hd : bytes.drop (pos + 1) = r ++ rest := by
      rw [← List.drop_drop, h]; rfl
    rw [varint_go bytes hr fuel (pos + 1) (shift + 7) _ rest (by simp at hl; omega) hd]
    simp only [Option.some.injEq, Prod.mk.injEq]
    refine ⟨?_, by omega⟩
    have e : 2 ^ (shift + 7) = 128 * 2 ^ shift := by rw [Nat.pow_add, Nat.mul_comm]
    rw [e, Nat.add_mul, Nat.add_assoc, Nat.mul_left_comm n 128, Nat.mul_assoc 128 n]
  | _, _, .cont _ _, 0, _, _, _, _, hl, _ => by simp at hl

theorem varintAt_varint {bytes v rest : List Byte} {n pos : Nat} (hv : Varint v n) (hl : v.length ≤ 10)
    (h : bytes.drop pos = v ++ rest) : varintAt bytes pos = some (n, pos + v.length) := by
  unfold varintAt
  rw [varint_go bytes hv 10 pos 0 0 rest hl h]
  simp

/-- The bytes end inside a varint (all its bytes so far have the top bit set). -/
theorem varint_go_partial (bytes : List Byte) : ∀ (u : List Byte), (∀ b ∈ u, 128 ≤ b.toNat) →
    ∀ (fuel pos shift acc : Nat), bytes.drop pos = u → varintAt.go bytes fuel pos shift acc = none
  | _, _, 0, _, _, _, _ => rfl
  | [], _, fuel + 1, pos, shift, acc, h => by
    unfold varintAt.go
    rw [if_pos]
    have := congrArg List.length h
    simp at this; omega
  | b :: u, hu, fuel + 1, pos, shift, acc, h => by
    have hlen := length_of_drop h (by simp)
    simp only [List.length_cons] at hlen
    have hg := get_of_drop h
    have hb := hu b (by simp)
    unfold varintAt.go
    simp only [hg]
    rw [if_neg (by omega), if_neg (by omega)]
    have hd : bytes.drop (pos + 1) = u := by rw [← List.drop_drop, h]; rfl
    exact varint_go_partial bytes u (fun x hx => hu x (by simp [hx])) fuel (pos + 1) _ _ hd

theorem varintAt_partial {bytes u : List Byte} {pos : Nat} (hu : ∀ b ∈ u, 128 ≤ b.toNat)
    (h : bytes.drop pos = u) : varintAt bytes pos = none :=
  varint_go_partial bytes u hu 10 pos 0 0 h

theorem varint_go_tooLong (bytes : List Byte) : ∀ (fuel pos shift acc : Nat),
    (∀ i < fuel, pos + i < bytes.length ∧ 128 ≤ (PublicReceive.get bytes (pos + i)).toNat) →
    varintAt.go bytes fuel pos shift acc = none
  | 0, _, _, _, _ => rfl
  | fuel + 1, pos, shift, acc, h => by
    obtain ⟨h1, h2⟩ := h 0 (by omega)
    simp only [Nat.add_zero] at h1 h2
    unfold varintAt.go
    dsimp only
    rw [if_neg (by omega), if_neg (by omega)]
    exact varint_go_tooLong bytes fuel (pos + 1) _ _ (fun i hi => by
      have := h (i + 1) (by omega); rw [show pos + 1 + i = pos + (i + 1) by omega]; exact this)

/-- A too-long varint is not read. -/
theorem varintAt_tooLong {bytes : List Byte} {pos : Nat} (h : varintTooLong bytes pos = true) :
    varintAt bytes pos = none := by
  unfold varintAt
  apply varint_go_tooLong
  intro i hi
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

/-- Fewer than 10 bytes left: not a too-long varint (whatever they are). -/
theorem varintTooLong_short {bytes u : List Byte} {pos : Nat} (h : bytes.drop pos = u) (hu : u.length < 10) :
    varintTooLong bytes pos = false := by
  have hl := congrArg List.length h
  rw [List.length_drop] at hl
  unfold varintTooLong
  rw [Bool.eq_false_iff]
  intro hall
  have := List.all_eq_true.mp hall u.length (List.mem_range.mpr hu)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  omega

/-- Every proper prefix of a varint is an unfinished one. -/
theorem varint_prefix : ∀ {v : List Byte} {n : Nat}, Varint v n → ∀ j, j < v.length → ∀ b ∈ v.take j, 128 ≤ b.toNat
  | _, _, .last _, j, hj, b, hb => by
    have : j = 0 := by simp at hj; omega
    subst this; simp at hb
  | _, _, .cont (b := c) hc hr, j, hj, b, hb => by
    cases j with
    | zero => simp at hb
    | succ j =>
      simp only [List.take_succ_cons, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact hc
      · exact varint_prefix hr j (by simp at hj; omega) b hb

theorem drop_after {bytes A B : List Byte} {p : Nat} (h : bytes.drop p = A ++ B) :
    bytes.drop (p + A.length) = B := by
  rw [← List.drop_drop, h, List.drop_left]

theorem loopG_yield {β : Type} {g : β → ForInStep β} {b b' : β} (n : Nat) (h : g b = .yield b') :
    loopG g (n + 1) b = loopG g n b' := by
  simp only [loopG, h]

theorem loopG_done {β : Type} {g : β → ForInStep β} {b b' : β} (n : Nat) (h : g b = .done b') :
    loopG g (n + 1) b = b' := by
  simp only [loopG, h]

/-! ### `scan`, one round at a time -/

/-- What a complete verb, path or header field sets. -/
def textField (tag : Byte) (c : List Byte) (f : Fields) : Fields :=
  if tag = 0x0a then { f with verb := c } else if tag = 0x12 then { f with path := c } else f

theorem scanBody_end {bytes : List Byte} {b : Bool} {x : Option (Need × Fields)} {f : Fields} {pos : Nat}
    (h : bytes.length ≤ pos) : scanBody bytes b ⟨x, f, pos⟩ = .done ⟨some (.more, f), f, pos⟩ := by
  unfold scanBody; rw [if_pos h]

theorem tag_cases (tag : Byte) (ht : tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a) :
    (tag.toNat == 0x20) = false ∧ (tag.toNat == 0x0a || tag.toNat == 0x12 || tag.toNat == 0x2a) = true := by
  rcases ht with rfl | rfl | rfl <;> decide

theorem scanBody_text {bytes v c rest : List Byte} {tag : Byte} {b : Bool} {x : Option (Need × Fields)}
    {f : Fields} {pos : Nat} (ht : tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a) (hv : Varint v c.length)
    (hl : v.length ≤ 10) (h : bytes.drop pos = tag :: (v ++ (c ++ rest))) :
    scanBody bytes b ⟨x, f, pos⟩ = .yield ⟨none, textField tag c f, pos + 1 + v.length + c.length⟩ := by
  have hlen := length_of_drop h (by simp)
  simp only [List.length_cons, List.length_append] at hlen
  have hg := get_of_drop h
  have hd1 : bytes.drop (pos + 1) = v ++ (c ++ rest) := by
    rw [← List.drop_drop, h]; rfl
  have hvar := varintAt_varint hv hl hd1
  have hd2 : bytes.drop (pos + 1 + v.length) = c ++ rest := drop_after hd1
  obtain ⟨t1, t2⟩ := tag_cases tag ht
  have hp : ¬ bytes.length ≤ pos := by omega
  have hn : ¬ bytes.length < pos + 1 + v.length + c.length := by omega
  unfold scanBody
  simp only [hg, hvar, t1, t2, hd2, List.take_left, ge_iff_le, gt_iff_lt, hp, hn, if_false, if_true,
    Bool.false_eq_true]
  unfold textField
  rcases ht with rfl | rfl | rfl <;> rfl

/-- Inside a verb, path or header whose length is known: more is needed. -/
theorem scanBody_text_more {bytes v c : List Byte} {tag : Byte} {b : Bool} {x : Option (Need × Fields)}
    {f : Fields} {pos count : Nat} (ht : tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a) (hv : Varint v count)
    (hl : v.length ≤ 10) (hc : c.length < count) (h : bytes.drop pos = tag :: (v ++ c)) :
    scanBody bytes b ⟨x, f, pos⟩ = .done ⟨some (.more, f), f, pos⟩ := by
  have hlen := length_of_drop h (by simp)
  simp only [List.length_cons, List.length_append] at hlen
  have hg := get_of_drop h
  have hd1 : bytes.drop (pos + 1) = v ++ c := by rw [← List.drop_drop, h]; rfl
  have hvar := varintAt_varint hv hl hd1
  obtain ⟨t1, t2⟩ := tag_cases tag ht
  have hp : ¬ bytes.length ≤ pos := by omega
  have hn : bytes.length < pos + 1 + v.length + count := by omega
  unfold scanBody
  simp only [hg, hvar, t1, t2, ge_iff_le, gt_iff_lt, hp, hn, if_false, if_true, Bool.false_eq_true]

/-- After a key whose varint (a length or the id) is not complete yet: more is needed. -/
theorem scanBody_partial {bytes u : List Byte} {tag : Byte} {b : Bool} {x : Option (Need × Fields)}
    {f : Fields} {pos : Nat} (ht : tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a ∨ tag = 0x1a ∨ tag = 0x20)
    (hu : ∀ y ∈ u, 128 ≤ y.toNat) (hl : u.length < 10) (h : bytes.drop pos = tag :: u) :
    scanBody bytes b ⟨x, f, pos⟩ = .done ⟨some (.more, f), f, pos⟩ := by
  have hlen := length_of_drop h (by simp)
  simp only [List.length_cons] at hlen
  have hg := get_of_drop h
  have hd1 : bytes.drop (pos + 1) = u := by rw [← List.drop_drop, h]; rfl
  have hvar := varintAt_partial hu hd1
  have hp : ¬ bytes.length ≤ pos := by omega
  unfold scanBody
  simp only [hg, hvar, varintTooLong_short hd1 hl, ge_iff_le, hp, if_false, Bool.false_eq_true]
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- A body's key and complete length at the end of the revealed bytes: pass over `n` bytes. -/
theorem scanBody_skip {bytes v : List Byte} {x : Option (Need × Fields)} {f : Fields} {pos n : Nat}
    (hv : Varint v n) (hl : v.length ≤ 10) (hn : 0 < n) (hf : f.body = none)
    (h : bytes.drop pos = 0x1a :: v) :
    scanBody bytes false ⟨x, f, pos⟩ =
      .done ⟨some (.skip n, { f with body := some n }), { f with body := some n }, pos⟩ := by
  have hlen := length_of_drop h (by simp)
  simp only [List.length_cons] at hlen
  have hg := get_of_drop h
  have hd1 : bytes.drop (pos + 1) = v ++ [] := by rw [← List.drop_drop, h, List.append_nil]; rfl
  have hvar := varintAt_varint hv hl hd1
  have hp : ¬ bytes.length ≤ pos := by omega
  have he : (pos + 1 + v.length == bytes.length && !false && decide (n > 0)) = true := by
    simp only [Bool.not_false, Bool.and_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]; omega
  unfold scanBody
  simp only [hg, hvar, hf, ge_iff_le, hp, he, if_false, if_true, Option.isSome_none, Bool.false_eq_true]
  rfl

/-- **A too-long varint after a key is refused** (`scan`, at the varint's 10th byte). -/
theorem scanBody_tooLong {bytes rest : List Byte} {tag : Byte} {b : Bool} {x : Option (Need × Fields)}
    {f : Fields} {pos : Nat} (ht : tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a ∨ tag = 0x1a ∨ tag = 0x20)
    (h : bytes.drop pos = tag :: rest) (hl : varintTooLong bytes (pos + 1) = true) :
    scanBody bytes b ⟨x, f, pos⟩ = .done ⟨some (.malformed, f), f, pos⟩ := by
  have hlen := length_of_drop h (by simp)
  simp only [List.length_cons] at hlen
  have hg := get_of_drop h
  have hp : ¬ bytes.length ≤ pos := by omega
  unfold scanBody
  simp only [hg, varintAt_tooLong hl, hl, ge_iff_le, hp, if_false, if_true]
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem tooLong_length {bytes : List Byte} {pos : Nat} (h : varintTooLong bytes pos = true) :
    pos + 10 ≤ bytes.length := by
  have := List.all_eq_true.mp h 9 (by simp)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  omega

/-- **A too-long wrapper length is refused** (`scan`). -/
theorem scan_wrapper_tooLong (bytes : List Byte) (b : Bool)
    (hk : (bytes.take 2 == [8, 1] && PublicReceive.get bytes 2 == 0x12) = true)
    (h : varintTooLong bytes 3 = true) : (scan bytes b).1 = .malformed := by
  have := tooLong_length h
  rw [scan_eq, if_neg (by omega), if_pos hk, varintAt_tooLong h]
  simp [h]

theorem drop_field {bytes v c rest : List Byte} {tag : Byte} {p : Nat}
    (h : bytes.drop p = tag :: (v ++ (c ++ rest))) : bytes.drop (p + 1 + v.length + c.length) = rest := by
  have e : tag :: (v ++ (c ++ rest)) = (tag :: (v ++ c)) ++ rest := by simp
  rw [e] at h
  have := drop_after h
  simp only [List.length_cons, List.length_append] at this
  rw [show p + 1 + v.length + c.length = p + (v.length + c.length + 1) by omega]
  exact this

/-! ### The body of a server request is found exactly

A server request in the server's layout (`WebSocketRequestMessage` fields in number order: verb,
path, body, id, headers; Signal-Server and protobuf write them so). `requestHead` is its revealed
bytes up to the end of the body's length; the varint encodings are any (`Varint`, at most 10
bytes), the verb and path any bytes. -/

/-- Kind `08 01`, wrapper key `12` and length `lw`, verb (`0a`, length `vv`), path (`12`, length
`pv`), body key `1a` and length `bv`. -/
def requestHead (lw vv verb pv path bv : List Byte) : List Byte :=
  [8, 1, 0x12] ++ (lw ++ (0x0a :: (vv ++ (verb ++ (0x12 :: (pv ++ (path ++ (0x1a :: bv))))))))

/-- **The scanner finds the body.** On a server request's revealed bytes up to the end of its body's
length, `scan` asks to pass over exactly the body's length, with the verb and path read. -/
theorem scan_requestHead {lw vv verb pv path bv : List Byte} {L n : Nat}
    (hl : Varint lw L) (hl10 : lw.length ≤ 10) (hv : Varint vv verb.length) (hv10 : vv.length ≤ 10)
    (hp : Varint pv path.length) (hp10 : pv.length ≤ 10) (hb : Varint bv n) (hb10 : bv.length ≤ 10)
    (hn : 0 < n) :
    scan (requestHead lw vv verb pv path bv) false = (.skip n, { verb, path, id := none, body := some n }) := by
  generalize hP : requestHead lw vv verb pv path bv = P
  have h0 : P.drop 3 = lw ++ (0x0a :: (vv ++ (verb ++ (0x12 :: (pv ++ (path ++ (0x1a :: bv))))))) := by
    rw [← hP]; rfl
  have hlen : P.length = 3 + (lw.length + (vv.length + (verb.length + (pv.length + (path.length + bv.length + 1) + 1)) + 1)) := by
    rw [← hP]; simp [requestHead]; omega
  have h1 := drop_after h0
  have h2 := drop_field h1
  have h3 := drop_field h2
  rw [scan_eq]
  have hc : (P.take 2 == [8, 1] && PublicReceive.get P 2 == 0x12) = true := by rw [← hP]; rfl
  rw [if_neg (by omega), if_pos hc, varintAt_varint hl hl10 h0]
  dsimp only
  obtain ⟨m, hm⟩ : ∃ m, P.length + 1 = m + 3 := ⟨P.length - 2, by omega⟩
  rw [hm, loopG_yield _ (scanBody_text (Or.inl rfl) hv hv10 h1),
    loopG_yield _ (scanBody_text (Or.inr (Or.inl rfl)) hp hp10 h2),
    loopG_done _ (scanBody_skip hb hb10 hn rfl h3)]
  rfl

/-! ### Before the body: nothing is skipped, and no run reaches the body

`fieldMissing`, which bounds the controller's runs inside a request (`budget`), as a loop function
too, and the scanners on every proper prefix of `requestHead`. -/

/-- One round of `fieldMissing`'s loop. -/
def missingBody (bytes : List Byte) (r : MProd (Option Nat) Nat) : ForInStep (MProd (Option Nat) Nat) :=
  if r.snd ≥ bytes.length then .done ⟨some 0, r.snd⟩ else
  if ((get bytes r.snd).toNat == 0x0a || (get bytes r.snd).toNat == 0x12 || (get bytes r.snd).toNat == 0x2a) then
    match varintAt bytes (r.snd + 1) with
    | some (count, next) =>
      if next + count > bytes.length then .done ⟨some (next + count - bytes.length), r.snd⟩
      else .yield ⟨none, next + count⟩
    | _ => .done ⟨some 0, r.snd⟩
  else if ((get bytes r.snd).toNat == 0x20 || (get bytes r.snd).toNat == 0x1a) then
    match varintAt bytes (r.snd + 1) with
    | some (_, next) => .yield ⟨none, next⟩
    | _ => .done ⟨some 0, r.snd⟩
  else .done ⟨some 0, r.snd⟩

def missingResult (r : MProd (Option Nat) Nat) : Nat :=
  match r.fst with
  | none => 0
  | some a => a

theorem fieldMissing_eq (bytes : List Byte) : fieldMissing bytes =
    if bytes.length < 3 then 0 else
    match varintAt bytes 3 with
    | some (_, first) => missingResult (loopG (missingBody bytes) (bytes.length + 1) ⟨none, first⟩)
    | none => 0 := by
  unfold fieldMissing
  simp only [Id.run, forIn_range]
  by_cases h1 : bytes.length < 3
  · simp only [h1, if_true]; rfl
  · simp only [h1, if_false]
    cases hv : varintAt bytes 3 with
    | none => rfl
    | some v =>
      obtain ⟨_, first⟩ := v
      dsimp only
      rw [forIn_ignore (missingBody bytes) _ _ ?hf, List.length_range']
      · unfold missingResult
        generalize loopG (missingBody bytes) (bytes.length + 1) ⟨none, first⟩ = r
        obtain ⟨fst, snd⟩ := r
        cases fst <;> rfl
      · intro x r; rfl

theorem missingBody_text {bytes v c rest : List Byte} {tag : Byte} {x : Option Nat} {pos : Nat}
    (ht : tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a) (hv : Varint v c.length)
    (hl : v.length ≤ 10) (h : bytes.drop pos = tag :: (v ++ (c ++ rest))) :
    missingBody bytes ⟨x, pos⟩ = .yield ⟨none, pos + 1 + v.length + c.length⟩ := by
  have hlen := length_of_drop h (by simp)
  simp only [List.length_cons, List.length_append] at hlen
  have hg := get_of_drop h
  have hd1 : bytes.drop (pos + 1) = v ++ (c ++ rest) := by rw [← List.drop_drop, h]; rfl
  have hvar := varintAt_varint hv hl hd1
  obtain ⟨-, t2⟩ := tag_cases tag ht
  have hp : ¬ bytes.length ≤ pos := by omega
  have hn : ¬ bytes.length < pos + 1 + v.length + c.length := by omega
  unfold missingBody
  simp only [hg, hvar, t2, ge_iff_le, gt_iff_lt, hp, hn, if_false, if_true]

/-! The end of a proper prefix of `requestHead`, after its complete fields. -/

/-- Where a proper prefix of a request's revealed bytes can end, after its complete fields: at a
field boundary, after a key inside its varint, or inside a verb, path or header. -/
inductive Tail : List Byte → Nat → Prop
  | empty : Tail [] 0
  | unfinished {tag : Byte} {u : List Byte} : (tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a ∨ tag = 0x1a ∨ tag = 0x20) →
      (∀ y ∈ u, 128 ≤ y.toNat) → u.length < 10 → Tail (tag :: u) (u.length + 1)
  | short {tag : Byte} {v c : List Byte} {count : Nat} : (tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a) →
      Varint v count → v.length ≤ 10 → c.length < count → Tail (tag :: (v ++ c)) (1 + v.length + count)

theorem scan_tail {bytes : List Byte} {b : Bool} {f : Fields} {p m e : Nat} (ht : Tail (bytes.drop p) e) :
    loopResult (loopG (scanBody bytes b) (m + 1) ⟨none, f, p⟩) = (.more, f) := by
  generalize hd : bytes.drop p = d at ht
  cases ht with
  | empty =>
    rw [loopG_done _ (scanBody_end (by have := congrArg List.length hd; simp at this; omega))]; rfl
  | unfinished htag hu hl10 => rw [loopG_done _ (scanBody_partial htag hu hl10 hd)]; rfl
  | short htag hv hl hc => rw [loopG_done _ (scanBody_text_more htag hv hl hc hd)]; rfl

/-- `fieldMissing` at a tail: no more than what is left of the field it ends in. -/
theorem missing_tail {bytes : List Byte} {p m e : Nat} (ht : Tail (bytes.drop p) e) :
    missingResult (loopG (missingBody bytes) (m + 1) ⟨none, p⟩) + bytes.length ≤ p + e := by
  generalize hd : bytes.drop p = d at ht
  have hlen0 := congrArg List.length hd
  rw [List.length_drop] at hlen0
  cases ht with
  | empty =>
    have hle : bytes.length ≤ p := by simp at hlen0; omega
    rw [loopG_done _ (by unfold missingBody; rw [if_pos hle])]
    simp [missingResult]; omega
  | unfinished htag hu hl10 =>
    rename_i tag u
    have hlen := length_of_drop hd (by simp)
    simp only [List.length_cons] at hlen
    have hg := get_of_drop hd
    have hd1 : bytes.drop (p + 1) = u := by rw [← List.drop_drop, hd]; rfl
    have hvar := varintAt_partial hu hd1
    have hp : ¬ bytes.length ≤ p := by omega
    rw [loopG_done _ (by
      unfold missingBody
      simp only [hg, hvar, ge_iff_le, hp, if_false]
      rcases htag with rfl | rfl | rfl | rfl | rfl <;> rfl)]
    simp [missingResult]; omega
  | short htag hv hl hc =>
    rename_i tag v c count
    have hlen := length_of_drop hd (by simp)
    simp only [List.length_cons, List.length_append] at hlen
    have hg := get_of_drop hd
    have hd1 : bytes.drop (p + 1) = v ++ c := by rw [← List.drop_drop, hd]; rfl
    have hvar := varintAt_varint hv hl hd1
    have hvar0 : varintAt (v ++ c) 0 = some (count, v.length) := by
      have := varintAt_varint (bytes := v ++ c) (pos := 0) hv hl (rest := c) (by simp)
      simpa using this
    obtain ⟨-, t2⟩ := tag_cases tag htag
    have hp : ¬ bytes.length ≤ p := by omega
    have hn : bytes.length < p + 1 + v.length + count := by omega
    rw [loopG_done _ (by
      unfold missingBody
      simp only [hg, hvar, t2, ge_iff_le, gt_iff_lt, hp, hn, if_false, if_true]
      rfl)]
    simp only [missingResult]
    omega

theorem take_append_ge {α : Type} : ∀ (A B : List α) (n : Nat), A.length ≤ n →
    (A ++ B).take n = A ++ B.take (n - A.length)
  | [], B, n, _ => by simp
  | _ :: A, B, n + 1, h => by
    simp only [List.cons_append, List.take_succ_cons, List.length_cons, Nat.add_sub_add_right]
    rw [take_append_ge A B n (by simp at h; omega)]
  | _ :: _, _, 0, h => by simp at h

theorem drop_take' {α : Type} : ∀ (l : List α) (m n : Nat), (l.take n).drop m = (l.drop m).take (n - m)
  | [], m, n => by simp
  | a :: l, 0, n => by simp
  | a :: l, m + 1, 0 => by simp
  | a :: l, m + 1, n + 1 => by
    simp only [List.take_succ_cons, List.drop_succ_cons, Nat.add_sub_add_right]
    exact drop_take' l m n

theorem take_field {Z : List Byte} (tag : Byte) (v c : List Byte) (j : Nat) (h : 1 + v.length + c.length ≤ j) :
    (tag :: (v ++ (c ++ Z))).take j = tag :: (v ++ (c ++ Z.take (j - (1 + v.length + c.length)))) := by
  have e : tag :: (v ++ (c ++ Z)) = (tag :: (v ++ c)) ++ Z := by simp
  rw [e, take_append_ge _ _ _ (by simp; omega)]
  simp only [List.length_cons, List.length_append, List.cons_append, List.append_assoc]
  congr 4; omega

theorem tail_text {tag : Byte} {v c Z : List Byte} (ht : tag = 0x0a ∨ tag = 0x12 ∨ tag = 0x2a)
    (hv : Varint v c.length) (hl : v.length ≤ 10) (j : Nat) (hj : j < 1 + v.length + c.length) :
    ∃ e, e ≤ 1 + v.length + c.length ∧ Tail ((tag :: (v ++ (c ++ Z))).take j) e := by
  cases j with
  | zero => exact ⟨0, by omega, by simpa using Tail.empty⟩
  | succ j =>
    rw [List.take_succ_cons]
    by_cases hjv : j < v.length
    · rw [List.take_append_of_le_length (by omega)]
      refine ⟨(v.take j).length + 1, by simp; omega,
        Tail.unfinished (by rcases ht with h | h | h <;> simp [h]) ?_ (by simp; omega)⟩
      exact varint_prefix hv j hjv
    · rw [take_append_ge v _ j (by omega), List.take_append_of_le_length (by omega)]
      exact ⟨1 + v.length + c.length, by omega, Tail.short ht hv hl (by simp; omega)⟩

theorem tail_body {bv : List Byte} {n : Nat} (hb : Varint bv n) (hb10 : bv.length ≤ 10) (j : Nat)
    (hj : j < 1 + bv.length) :
    ∃ e, e ≤ 1 + bv.length ∧ Tail (((0x1a : Byte) :: bv).take j) e := by
  cases j with
  | zero => exact ⟨0, by omega, by simpa using Tail.empty⟩
  | succ j =>
    rw [List.take_succ_cons]
    exact ⟨(bv.take j).length + 1, by simp; omega,
      Tail.unfinished (by simp) (varint_prefix hb j (by omega)) (by simp; omega)⟩

/-- **Before the body, nothing is skipped and no run reaches the body.** On every proper prefix of
a server request's revealed bytes (from the kind bytes on), `scan` asks for more (it neither skips
nor refuses), and `fieldMissing`, which bounds the controller's next run (`budget`), stays within the
request's head: the run ends at or before the body's first byte. -/
theorem requestHead_prefix {lw vv verb pv path bv : List Byte} {L n : Nat}
    (hl : Varint lw L) (hl10 : lw.length ≤ 10) (hv : Varint vv verb.length) (hv10 : vv.length ≤ 10)
    (hp : Varint pv path.length) (hp10 : pv.length ≤ 10) (hb : Varint bv n) (hb10 : bv.length ≤ 10)
    (k : Nat) (hk2 : 2 ≤ k) (hk : k < (requestHead lw vv verb pv path bv).length) :
    (scan ((requestHead lw vv verb pv path bv).take k) false).1 = .more ∧
      fieldMissing ((requestHead lw vv verb pv path bv).take k) + k ≤ (requestHead lw vv verb pv path bv).length := by
  generalize hP : requestHead lw vv verb pv path bv = P at hk ⊢
  have h0 : P.drop 3 = lw ++ (0x0a :: (vv ++ (verb ++ (0x12 :: (pv ++ (path ++ (0x1a :: bv))))))) := by
    rw [← hP]; rfl
  have hlen : P.length = 3 + (lw.length + (vv.length + (verb.length + (pv.length + (path.length + bv.length + 1) + 1)) + 1)) := by
    rw [← hP]; simp [requestHead]; omega
  have h1 := drop_after h0
  have h2 := drop_field h1
  have h3 := drop_field h2
  generalize hQ : P.take k = Q
  have hQlen : Q.length = k := by rw [← hQ, List.length_take]; omega
  have hQd : ∀ p, Q.drop p = (P.drop p).take (k - p) := fun p => by rw [← hQ, drop_take']
  rw [scan_eq, fieldMissing_eq, hQlen]
  by_cases hk3 : k < 3
  · simp only [hk3, if_true]; exact ⟨by trivial, by omega⟩
  rw [if_neg hk3, if_neg hk3]
  have hc : (Q.take 2 == [8, 1] && PublicReceive.get Q 2 == 0x12) = true := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 3 := ⟨k - 3, by omega⟩
    rw [← hQ, ← hP]; rfl
  rw [if_pos hc]
  -- The wrapper's length.
  by_cases ha1 : k < 3 + lw.length
  · have hd : Q.drop 3 = lw.take (k - 3) := by
      rw [hQd, h0, List.take_append_of_le_length (by omega)]
    rw [varintAt_partial (varint_prefix hl (k - 3) (by omega)) hd,
      varintTooLong_short hd (by simp; omega)]
    exact ⟨by trivial, by simp only; omega⟩
  have hd3 : Q.drop 3 = lw ++ (0x0a :: (vv ++ (verb ++ (0x12 :: (pv ++ (path ++ (0x1a :: bv))))))).take (k - 3 - lw.length) := by
    rw [hQd, h0, take_append_ge _ _ _ (by omega)]
  rw [varintAt_varint hl hl10 hd3]
  dsimp only
  obtain ⟨m, hm⟩ : ∃ m, k + 1 = m + 1 := ⟨k, rfl⟩
  -- Inside the verb field (or at its start).
  by_cases ha2 : k < 3 + lw.length + 1 + vv.length + verb.length
  · obtain ⟨e, he, ht⟩ := tail_text (Z := 0x12 :: (pv ++ (path ++ (0x1a :: bv)))) (Or.inl rfl) hv hv10
      (k - (3 + lw.length)) (by omega)
    rw [← h1, ← hQd] at ht
    refine ⟨by rw [scan_tail ht], ?_⟩
    have := missing_tail (m := k) ht
    omega
  -- The verb is complete.
  have hq1 := take_field (Z := 0x12 :: (pv ++ (path ++ (0x1a :: bv)))) (0x0a : Byte) vv verb
    (k - (3 + lw.length)) (by omega)
  rw [← h1, ← hQd] at hq1
  have hk1 : k + 1 = (k - 1) + 1 + 1 := by omega
  rw [hk1, loopG_yield _ (scanBody_text (Or.inl rfl) hv hv10 hq1),
    loopG_yield _ (missingBody_text (Or.inl rfl) hv hv10 hq1)]
  -- Inside the path field (or at its start).
  by_cases ha3 : k < 3 + lw.length + 1 + vv.length + verb.length + 1 + pv.length + path.length
  · obtain ⟨e, he, ht⟩ := tail_text (Z := 0x1a :: bv) (Or.inr (Or.inl rfl)) hp hp10
      (k - (3 + lw.length + 1 + vv.length + verb.length)) (by omega)
    rw [← h2, ← hQd] at ht
    refine ⟨by rw [scan_tail ht], ?_⟩
    have := missing_tail (m := k - 1) ht
    omega
  -- The path is complete: inside the body's length.
  have hq2 := take_field (Z := 0x1a :: bv) (0x12 : Byte) pv path
    (k - (3 + lw.length + 1 + vv.length + verb.length)) (by omega)
  rw [← h2, ← hQd] at hq2
  have hk2' : k - 1 + 1 = (k - 2) + 1 + 1 := by omega
  rw [hk2', loopG_yield _ (scanBody_text (Or.inr (Or.inl rfl)) hp hp10 hq2),
    loopG_yield _ (missingBody_text (Or.inr (Or.inl rfl)) hp hp10 hq2)]
  obtain ⟨e, he, ht⟩ := tail_body hb hb10 (k - (3 + lw.length + 1 + vv.length + verb.length + 1 + pv.length + path.length))
    (by omega)
  rw [← h3, ← hQd] at ht
  refine ⟨by rw [scan_tail ht], ?_⟩
  have := missing_tail (m := k - 2) ht
  omega

/-- Inside a request's payload (a data frame's payload byte comes next, the message is a request,
no envelope being walked), the controller's run is at most `max 1 (fieldMissing request)`. -/
theorem budget_request (s : State) (hu : s.upgraded = true) (h0 : (PublicReceive.get s.frame 0 == on) = false)
    (h2 : (PublicReceive.get s.frame 2 == on) = false) (h4 : (PublicReceive.get s.frame 4 == on) = true)
    (hr : (PublicReceive.get s.frame 10).toNat * 256 + (PublicReceive.get s.frame 11).toNat ≠ 0)
    (ho : (PublicReceive.get s.frame 7).toNat < 8) (hm : s.message = [8, 1]) :
    budget s ≤ max 1 (fieldMissing s.request) := by
  unfold budget
  have hr' : ((PublicReceive.get s.frame 10).toNat * 256 + (PublicReceive.get s.frame 11).toNat == 0) = false := by
    simp only [beq_eq_false_iff_ne]; exact hr
  have h82 : (s.message == [8, 2]) = false := by rw [hm]; decide
  have h81 : (s.message == [8, 1]) = true := by rw [hm]; decide
  simp only [hu, h0, h2, h4, hr', h81, h82, Bool.not_true, Bool.or_false,
    Bool.false_eq_true, if_false, if_true, Nat.not_le.mpr ho]
  omega

/-- **T1 for a server request's head (scanner level).** Whatever its verb and path and however its
lengths are encoded: while the controller walks the revealed bytes of a server request up to its
body's length, every run it reveals from a state whose revealed request bytes are the first `k`
bytes ends at or before the body's first byte; and at the end of the body's length it is told to
pass over exactly the body (then `go_skip`: none of those bytes is ever revealed). -/
theorem request_body_unrevealed {lw vv verb pv path bv : List Byte} {L n : Nat}
    (hl : Varint lw L) (hl10 : lw.length ≤ 10) (hv : Varint vv verb.length) (hv10 : vv.length ≤ 10)
    (hp : Varint pv path.length) (hp10 : pv.length ≤ 10) (hb : Varint bv n) (hb10 : bv.length ≤ 10)
    (hn : 0 < n) :
    (∀ (s : State) (k : Nat), 2 ≤ k → k < (requestHead lw vv verb pv path bv).length →
      s.request = (requestHead lw vv verb pv path bv).take k → s.upgraded = true →
      (PublicReceive.get s.frame 0 == on) = false → (PublicReceive.get s.frame 2 == on) = false →
      (PublicReceive.get s.frame 4 == on) = true →
      (PublicReceive.get s.frame 10).toNat * 256 + (PublicReceive.get s.frame 11).toNat ≠ 0 →
      (PublicReceive.get s.frame 7).toNat < 8 → s.message = [8, 1] →
      (scan s.request false).1 = .more ∧ k + budget s ≤ (requestHead lw vv verb pv path bv).length) ∧
    scan (requestHead lw vv verb pv path bv) false = (.skip n, { verb, path, id := none, body := some n }) := by
  refine ⟨?_, scan_requestHead hl hl10 hv hv10 hp hp10 hb hb10 hn⟩
  intro s k hk2 hk hs hu h0 h2 h4 hr ho hm
  obtain ⟨hscan, hmiss⟩ := requestHead_prefix hl hl10 hv hv10 hp hp10 hb hb10 k hk2 hk
  rw [hs]
  refine ⟨hscan, ?_⟩
  have := budget_request s hu h0 h2 h4 hr ho hm
  rw [hs] at this
  omega

/-! ### The body of a response is found exactly

A response in the server's layout (`WebSocketResponseMessage` fields in number order: id, status,
message, body, headers). `responseHead` is its revealed bytes up to the end of the body's length.
`inline` is `openBody` (the ceremony), false in every send and receive session. -/

/-- One round of `replyScan`'s loop. -/
def replyScanBody (bytes : List Byte) (bodySkipped inline : Bool) (r : LoopState ReplyFields) :
    ForInStep (LoopState ReplyFields) :=
  if r.snd.snd ≥ bytes.length then .done ⟨some (.more, r.snd.fst), r.snd.fst, r.snd.snd⟩ else
  if ((get bytes r.snd.snd).toNat == 0x08 || (get bytes r.snd.snd).toNat == 0x10) then
    match varintAt bytes (r.snd.snd + 1) with
    | some (value, next) =>
      .yield ⟨none, if (get bytes r.snd.snd).toNat == 0x08 then { r.snd.fst with id := some value }
        else { r.snd.fst with status := some value }, next⟩
    | _ => .done ⟨some (if varintTooLong bytes (r.snd.snd + 1) then .malformed else .more, r.snd.fst), r.snd.fst, r.snd.snd⟩
  else if ((get bytes r.snd.snd).toNat == 0x1a || (get bytes r.snd.snd).toNat == 0x2a) then
    match varintAt bytes (r.snd.snd + 1) with
    | some (count, next) =>
      if next + count > bytes.length then .done ⟨some (.more, r.snd.fst), r.snd.fst, r.snd.snd⟩
      else .yield ⟨none, r.snd.fst, next + count⟩
    | _ => .done ⟨some (if varintTooLong bytes (r.snd.snd + 1) then .malformed else .more, r.snd.fst), r.snd.fst, r.snd.snd⟩
  else if (get bytes r.snd.snd).toNat == 0x22 then
    match varintAt bytes (r.snd.snd + 1) with
    | some (count, next) =>
      if r.snd.fst.body.isSome then .done ⟨some (.malformed, r.snd.fst), r.snd.fst, r.snd.snd⟩ else
      if (next == bytes.length && !bodySkipped && !inline && decide (count > 0)) then
        .done ⟨some (.skip count, { r.snd.fst with body := some count }), { r.snd.fst with body := some count }, r.snd.snd⟩
      else if (inline && decide (next + count > bytes.length)) then
        .done ⟨some (.more, { r.snd.fst with body := some count }), { r.snd.fst with body := some count }, r.snd.snd⟩
      else .yield ⟨none, { r.snd.fst with body := some count }, if inline then next + count else next⟩
    | _ => .done ⟨some (if varintTooLong bytes (r.snd.snd + 1) then .malformed else .more, r.snd.fst), r.snd.fst, r.snd.snd⟩
  else .done ⟨some (.malformed, r.snd.fst), r.snd.fst, r.snd.snd⟩

theorem replyScan_eq (bytes : List Byte) (b inline : Bool) : replyScan bytes b inline =
    if bytes.length < 3 then (.more, {}) else
    if (bytes.take 2 == [8, 2] && get bytes 2 == 0x1a) = true then
      match varintAt bytes 3 with
      | some (_, first) => loopResult (loopG (replyScanBody bytes b inline) (bytes.length + 1) ⟨none, {}, first⟩)
      | none => (if varintTooLong bytes 3 then .malformed else .more, {})
    else (.malformed, {}) := by
  unfold replyScan
  simp only [Id.run, forIn_range]
  by_cases h1 : bytes.length < 3
  · simp only [h1, if_true]; rfl
  by_cases h2 : (bytes.take 2 == [8, 2] && get bytes 2 == 0x1a) = true
  · simp only [h1, h2, if_true, if_false]
    cases hv : varintAt bytes 3 with
    | none => rfl
    | some v =>
      obtain ⟨_, first⟩ := v
      dsimp only
      rw [forIn_ignore (replyScanBody bytes b inline) _ _ ?hf, List.length_range']
      · unfold loopResult
        generalize loopG (replyScanBody bytes b inline) (bytes.length + 1) ⟨none, {}, first⟩ = r
        obtain ⟨fst, snd⟩ := r
        cases fst <;> rfl
      · intro x r; rfl
  · simp only [h1, h2, if_false]; rfl

/-- One round of `replyBudget`'s loop. -/
def budgetBody (bytes : List Byte) (inline : Bool) (r : MProd (Option Nat) Nat) : ForInStep (MProd (Option Nat) Nat) :=
  if r.snd ≥ bytes.length then .done ⟨some 2, r.snd⟩ else
  if ((get bytes r.snd).toNat == 0x08 || (get bytes r.snd).toNat == 0x10) then
    match varintAt bytes (r.snd + 1) with
    | some (_, next) => .yield ⟨none, next⟩
    | none => .done ⟨some (if r.snd + 1 ≥ bytes.length then 1 else min 3 (11 - (bytes.length - (r.snd + 1)))), r.snd⟩
  else if ((get bytes r.snd).toNat == 0x1a || (get bytes r.snd).toNat == 0x2a) then
    match varintAt bytes (r.snd + 1) with
    | some (count, next) =>
      if next + count > bytes.length then .done ⟨some (next + count - bytes.length), r.snd⟩
      else .yield ⟨none, next + count⟩
    | _ => .done ⟨some 1, r.snd⟩
  else if (get bytes r.snd).toNat == 0x22 then
    match varintAt bytes (r.snd + 1) with
    | some (count, next) =>
      if (inline && decide (next + count > bytes.length)) then .done ⟨some (next + count - bytes.length), r.snd⟩
      else .yield ⟨none, if inline then next + count else next⟩
    | _ => .done ⟨some 1, r.snd⟩
  else .done ⟨some 1, r.snd⟩

def budgetResult (r : MProd (Option Nat) Nat) : Nat :=
  match r.fst with
  | none => 1
  | some a => a

theorem replyBudget_eq (bytes : List Byte) (inline : Bool) : replyBudget bytes inline =
    if bytes.length < 3 then 2 else
    match varintAt bytes 3 with
    | some (_, first) => budgetResult (loopG (budgetBody bytes inline) (bytes.length + 1) ⟨none, first⟩)
    | none => 1 := by
  unfold replyBudget
  simp only [Id.run, forIn_range]
  by_cases h1 : bytes.length < 3
  · simp only [h1, if_true]; rfl
  · simp only [h1, if_false]
    cases hv : varintAt bytes 3 with
    | none => rfl
    | some v =>
      obtain ⟨_, first⟩ := v
      dsimp only
      rw [forIn_ignore (budgetBody bytes inline) _ _ ?hf, List.length_range']
      · unfold budgetResult
        generalize loopG (budgetBody bytes inline) (bytes.length + 1) ⟨none, first⟩ = r
        obtain ⟨fst, snd⟩ := r
        cases fst <;> rfl
      · intro x r; rfl

/-- What a complete id or status field sets. -/
def numberField (tag : Byte) (value : Nat) (f : ReplyFields) : ReplyFields :=
  if tag = 0x08 then { f with id := some value } else { f with status := some value }

theorem rtag_number (tag : Byte) (ht : tag = 0x08 ∨ tag = 0x10) :
    (tag.toNat == 0x08 || tag.toNat == 0x10) = true := by
  rcases ht with rfl | rfl <;> decide

theorem rtag_text (tag : Byte) (ht : tag = 0x1a ∨ tag = 0x2a) :
    (tag.toNat == 0x08 || tag.toNat == 0x10) = false ∧ (tag.toNat == 0x1a || tag.toNat == 0x2a) = true := by
  rcases ht with rfl | rfl <;> decide

/-- The facts every round lemma needs about a field at `pos`. -/
theorem field_at {bytes rest : List Byte} {tag : Byte} {pos : Nat} (h : bytes.drop pos = tag :: rest) :
    PublicReceive.get bytes pos = tag ∧ bytes.drop (pos + 1) = rest ∧ ¬ bytes.length ≤ pos ∧
      bytes.length = pos + 1 + rest.length := by
  have hlen := length_of_drop h (by simp)
  simp only [List.length_cons] at hlen
  exact ⟨get_of_drop h, by rw [← List.drop_drop, h]; rfl, by omega, by omega⟩

theorem replyScanBody_number {bytes v rest : List Byte} {tag : Byte} {x : Option (Need × ReplyFields)}
    {f : ReplyFields} {pos n : Nat} {b i : Bool} (ht : tag = 0x08 ∨ tag = 0x10) (hv : Varint v n)
    (hl : v.length ≤ 10) (h : bytes.drop pos = tag :: (v ++ rest)) :
    replyScanBody bytes b i ⟨x, f, pos⟩ = .yield ⟨none, numberField tag n f, pos + 1 + v.length⟩ := by
  obtain ⟨hg, hd1, hp, -⟩ := field_at h
  have hvar := varintAt_varint hv hl hd1
  unfold replyScanBody numberField
  simp only [hg, hvar, rtag_number tag ht, ge_iff_le, hp, if_false, if_true]
  rcases ht with rfl | rfl <;> rfl

theorem budgetBody_number {bytes v rest : List Byte} {tag : Byte} {x : Option Nat} {pos n : Nat} {i : Bool}
    (ht : tag = 0x08 ∨ tag = 0x10) (hv : Varint v n) (hl : v.length ≤ 10) (h : bytes.drop pos = tag :: (v ++ rest)) :
    budgetBody bytes i ⟨x, pos⟩ = .yield ⟨none, pos + 1 + v.length⟩ := by
  obtain ⟨hg, hd1, hp, -⟩ := field_at h
  have hvar := varintAt_varint hv hl hd1
  unfold budgetBody
  simp only [hg, hvar, rtag_number tag ht, ge_iff_le, hp, if_false, if_true]

theorem replyScanBody_text {bytes v c rest : List Byte} {tag : Byte} {x : Option (Need × ReplyFields)}
    {f : ReplyFields} {pos : Nat} {b i : Bool} (ht : tag = 0x1a ∨ tag = 0x2a) (hv : Varint v c.length)
    (hl : v.length ≤ 10) (h : bytes.drop pos = tag :: (v ++ (c ++ rest))) :
    replyScanBody bytes b i ⟨x, f, pos⟩ = .yield ⟨none, f, pos + 1 + v.length + c.length⟩ := by
  obtain ⟨hg, hd1, hp, hlen⟩ := field_at h
  simp only [List.length_append] at hlen
  have hvar := varintAt_varint hv hl hd1
  have hn : ¬ bytes.length < pos + 1 + v.length + c.length := by omega
  obtain ⟨t1, t2⟩ := rtag_text tag ht
  unfold replyScanBody
  simp only [hg, hvar, t1, t2, ge_iff_le, gt_iff_lt, hp, hn, if_false, if_true, Bool.false_eq_true]

theorem budgetBody_text {bytes v c rest : List Byte} {tag : Byte} {x : Option Nat} {pos : Nat} {i : Bool}
    (ht : tag = 0x1a ∨ tag = 0x2a) (hv : Varint v c.length) (hl : v.length ≤ 10)
    (h : bytes.drop pos = tag :: (v ++ (c ++ rest))) :
    budgetBody bytes i ⟨x, pos⟩ = .yield ⟨none, pos + 1 + v.length + c.length⟩ := by
  obtain ⟨hg, hd1, hp, hlen⟩ := field_at h
  simp only [List.length_append] at hlen
  have hvar := varintAt_varint hv hl hd1
  have hn : ¬ bytes.length < pos + 1 + v.length + c.length := by omega
  obtain ⟨t1, t2⟩ := rtag_text tag ht
  unfold budgetBody
  simp only [hg, hvar, t1, t2, ge_iff_le, gt_iff_lt, hp, hn, if_false, if_true, Bool.false_eq_true]

/-- A response body's key and complete length at the end of the revealed bytes: pass over `n` bytes. -/
theorem replyScanBody_skip {bytes v : List Byte} {x : Option (Need × ReplyFields)} {f : ReplyFields} {pos n : Nat}
    (hv : Varint v n) (hl : v.length ≤ 10) (hn : 0 < n) (hf : f.body = none) (h : bytes.drop pos = 0x22 :: v) :
    replyScanBody bytes false false ⟨x, f, pos⟩ =
      .done ⟨some (.skip n, { f with body := some n }), { f with body := some n }, pos⟩ := by
  obtain ⟨hg, hd1, hp, hlen⟩ := field_at h
  have hvar := varintAt_varint (rest := []) hv hl (by rw [hd1, List.append_nil])
  have he : (pos + 1 + v.length == bytes.length && !false && !false && decide (n > 0)) = true := by
    simp only [Bool.not_false, Bool.and_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]; omega
  unfold replyScanBody
  simp only [hg, hvar, hf, ge_iff_le, hp, he, if_false, if_true, Option.isSome_none, Bool.false_eq_true]
  rfl

/-- **A too-long varint after a key is refused** (`replyScan`, at the varint's 10th byte). -/
theorem replyScanBody_tooLong {bytes rest : List Byte} {tag : Byte} {x : Option (Need × ReplyFields)}
    {f : ReplyFields} {pos : Nat} {b i : Bool}
    (ht : tag = 0x08 ∨ tag = 0x10 ∨ tag = 0x1a ∨ tag = 0x2a ∨ tag = 0x22)
    (h : bytes.drop pos = tag :: rest) (hl : varintTooLong bytes (pos + 1) = true) :
    replyScanBody bytes b i ⟨x, f, pos⟩ = .done ⟨some (.malformed, f), f, pos⟩ := by
  obtain ⟨hg, -, hp, -⟩ := field_at h
  unfold replyScanBody
  simp only [hg, varintAt_tooLong hl, hl, ge_iff_le, hp, if_false, if_true]
  rcases ht with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **A too-long wrapper length is refused** (`replyScan`). -/
theorem replyScan_wrapper_tooLong (bytes : List Byte) (b i : Bool)
    (hk : (bytes.take 2 == [8, 2] && PublicReceive.get bytes 2 == 0x1a) = true)
    (h : varintTooLong bytes 3 = true) : (replyScan bytes b i).1 = .malformed := by
  have := tooLong_length h
  rw [replyScan_eq, if_neg (by omega), if_pos hk, varintAt_tooLong h]
  simp [h]

/-- Where a proper prefix of a response's revealed bytes can end after its complete fields, and how
far `replyBudget` may then reach: at a field boundary (the next key and the byte after it), just
after an id or status key (one byte), inside an id or status (three), after a message, header or
body key inside its length (one), inside a message or header (the rest of it). -/
inductive RTail : List Byte → Nat → Prop
  | boundary : RTail [] 2
  | numberKey {tag : Byte} : (tag = 0x08 ∨ tag = 0x10) → RTail [tag] 1
  | number {tag : Byte} {u : List Byte} : (tag = 0x08 ∨ tag = 0x10) → u ≠ [] → (∀ y ∈ u, 128 ≤ y.toNat) →
      u.length < 10 → RTail (tag :: u) 3
  | lengthKey {tag : Byte} {u : List Byte} : (tag = 0x1a ∨ tag = 0x2a ∨ tag = 0x22) → (∀ y ∈ u, 128 ≤ y.toNat) →
      u.length < 10 → RTail (tag :: u) 1
  | short {tag : Byte} {v c : List Byte} {count : Nat} : (tag = 0x1a ∨ tag = 0x2a) → Varint v count →
      v.length ≤ 10 → c.length < count → RTail (tag :: (v ++ c)) (count - c.length)

theorem scan_rtail {bytes : List Byte} {f : ReplyFields} {p m e : Nat} (ht : RTail (bytes.drop p) e) :
    loopResult (loopG (replyScanBody bytes false false) (m + 1) ⟨none, f, p⟩) = (.more, f) := by
  generalize hd : bytes.drop p = d at ht
  have hl0 := congrArg List.length hd
  rw [List.length_drop] at hl0
  cases ht with
  | boundary =>
    have hle : bytes.length ≤ p := by simp at hl0; omega
    rw [loopG_done _ (by unfold replyScanBody; rw [if_pos hle])]; rfl
  | numberKey htag =>
    rename_i tag
    obtain ⟨hg, hd1, hp, -⟩ := field_at (rest := []) hd
    rw [loopG_done _ (by
      unfold replyScanBody
      simp only [hg, varintAt_partial (u := []) (by simp) hd1, varintTooLong_short hd1 (by simp),
        rtag_number tag htag, ge_iff_le, hp, if_false, if_true, Bool.false_eq_true]
      rfl)]; rfl
  | number htag hne hu hl10 =>
    rename_i tag u
    obtain ⟨hg, hd1, hp, -⟩ := field_at hd
    rw [loopG_done _ (by
      unfold replyScanBody
      simp only [hg, varintAt_partial hu hd1, varintTooLong_short hd1 hl10, rtag_number tag htag, ge_iff_le, hp,
        if_false, if_true, Bool.false_eq_true]
      rfl)]; rfl
  | lengthKey htag hu hl10 =>
    rename_i tag u
    obtain ⟨hg, hd1, hp, -⟩ := field_at hd
    rw [loopG_done _ (by
      unfold replyScanBody
      simp only [hg, varintAt_partial hu hd1, varintTooLong_short hd1 hl10, ge_iff_le, hp, if_false,
        Bool.false_eq_true]
      rcases htag with rfl | rfl | rfl <;> rfl)]; rfl
  | short htag hv hl hc =>
    rename_i tag v c count
    obtain ⟨hg, hd1, hp, hlen⟩ := field_at hd
    simp only [List.length_append] at hlen
    have hvar := varintAt_varint hv hl hd1
    have hn : bytes.length < p + 1 + v.length + count := by omega
    obtain ⟨t1, t2⟩ := rtag_text tag htag
    rw [loopG_done _ (by
      unfold replyScanBody
      simp only [hg, hvar, t1, t2, ge_iff_le, gt_iff_lt, hp, hn, if_false, if_true, Bool.false_eq_true]
      rfl)]; rfl

theorem budget_rtail {bytes : List Byte} {p m e : Nat} (ht : RTail (bytes.drop p) e) :
    budgetResult (loopG (budgetBody bytes false) (m + 1) ⟨none, p⟩) ≤ e := by
  generalize hd : bytes.drop p = d at ht
  have hl0 := congrArg List.length hd
  rw [List.length_drop] at hl0
  cases ht with
  | boundary =>
    have hle : bytes.length ≤ p := by simp at hl0; omega
    rw [loopG_done _ (by unfold budgetBody; rw [if_pos hle])]; simp [budgetResult]
  | numberKey htag =>
    rename_i tag
    obtain ⟨hg, hd1, hp, hlen⟩ := field_at (rest := []) hd
    have h1 : bytes.length ≤ p + 1 := by simp at hlen; omega
    rw [loopG_done _ (by
      unfold budgetBody
      simp only [hg, varintAt_partial (u := []) (by simp) hd1, rtag_number tag htag, ge_iff_le, hp, h1,
        if_false, if_true]
      rfl)]; simp [budgetResult]
  | number htag hne hu hl10 =>
    rename_i tag u
    obtain ⟨hg, hd1, hp, hlen⟩ := field_at hd
    rw [loopG_done _ (by
      unfold budgetBody
      simp only [hg, varintAt_partial hu hd1, rtag_number tag htag, ge_iff_le, hp, if_false, if_true]
      rfl)]
    simp only [budgetResult]; split <;> omega
  | lengthKey htag hu hl10 =>
    rename_i tag u
    obtain ⟨hg, hd1, hp, -⟩ := field_at hd
    rw [loopG_done _ (by
      unfold budgetBody
      simp only [hg, varintAt_partial hu hd1, ge_iff_le, hp, if_false]
      rcases htag with rfl | rfl | rfl <;> rfl)]; simp [budgetResult]
  | short htag hv hl hc =>
    rename_i tag v c count
    obtain ⟨hg, hd1, hp, hlen⟩ := field_at hd
    simp only [List.length_append] at hlen
    have hvar := varintAt_varint hv hl hd1
    have hn : bytes.length < p + 1 + v.length + count := by omega
    obtain ⟨t1, t2⟩ := rtag_text tag htag
    rw [loopG_done _ (by
      unfold budgetBody
      simp only [hg, hvar, t1, t2, ge_iff_le, gt_iff_lt, hp, hn, if_false, if_true, Bool.false_eq_true]
      rfl)]
    simp only [budgetResult]; omega

theorem varint_ne_nil {v : List Byte} {n : Nat} (hv : Varint v n) : 1 ≤ v.length := by
  cases hv <;> simp

theorem drop_number {bytes v rest : List Byte} {tag : Byte} {p : Nat}
    (h : bytes.drop p = tag :: (v ++ rest)) : bytes.drop (p + 1 + v.length) = rest := by
  have := drop_field (c := []) (by simpa using h)
  simpa using this

theorem rtail_number {tag : Byte} {v Z : List Byte} {n : Nat} (ht : tag = 0x08 ∨ tag = 0x10) (hv : Varint v n)
    (hl : v.length ≤ 10) (j : Nat) (hj : j < 1 + v.length) :
    ∃ e, j + e ≤ 1 + v.length + 2 ∧ RTail ((tag :: (v ++ Z)).take j) e := by
  match j with
  | 0 => exact ⟨2, by omega, by simpa using RTail.boundary⟩
  | 1 => exact ⟨1, by omega, by simpa using RTail.numberKey ht⟩
  | j + 2 =>
    rw [List.take_succ_cons, List.take_append_of_le_length (by omega)]
    refine ⟨3, by omega, RTail.number ht ?_ (varint_prefix hv (j + 1) (by omega)) (by simp; omega)⟩
    apply List.ne_nil_of_length_pos; simp only [List.length_take]; omega

theorem rtail_text {tag : Byte} {v c Z : List Byte} (ht : tag = 0x1a ∨ tag = 0x2a) (hv : Varint v c.length)
    (hl : v.length ≤ 10) (j : Nat) (hj : j < 1 + v.length + c.length) :
    ∃ e, j + e ≤ 1 + v.length + c.length + 2 ∧ RTail ((tag :: (v ++ (c ++ Z))).take j) e := by
  cases j with
  | zero => exact ⟨2, by omega, by simpa using RTail.boundary⟩
  | succ j =>
    rw [List.take_succ_cons]
    by_cases hjv : j < v.length
    · rw [List.take_append_of_le_length (by omega)]
      exact ⟨1, by omega, RTail.lengthKey (by rcases ht with h | h <;> simp [h]) (varint_prefix hv j hjv)
        (by simp; omega)⟩
    · rw [take_append_ge v _ j (by omega), List.take_append_of_le_length (by omega)]
      refine ⟨c.length - (c.take (j - v.length)).length, ?_, RTail.short ht hv hl (by simp; omega)⟩
      simp only [List.length_take]; omega

theorem rtail_body {bv : List Byte} {n : Nat} (hb : Varint bv n) (hb10 : bv.length ≤ 10) (j : Nat)
    (hj : j < 1 + bv.length) :
    ∃ e, j + e ≤ 1 + bv.length ∧ RTail (((0x22 : Byte) :: bv).take j) e := by
  have := varint_ne_nil hb
  cases j with
  | zero => exact ⟨2, by omega, by simpa using RTail.boundary⟩
  | succ j =>
    rw [List.take_succ_cons]
    exact ⟨1, by omega, RTail.lengthKey (by simp) (varint_prefix hb j (by omega)) (by simp; omega)⟩

/-- Kind `08 02`, wrapper key `1a` and length `lw`, id (`08`, varint `iv`), status (`10`, varint
`sv`), message (`1a`, length `mv`), body key `22` and length `bv`. -/
def responseHead (lw iv sv mv msg bv : List Byte) : List Byte :=
  [8, 2, 0x1a] ++ (lw ++ (0x08 :: (iv ++ (0x10 :: (sv ++ (0x1a :: (mv ++ (msg ++ (0x22 :: bv)))))))))

/-- **The scanner finds a response's body.** On a response's revealed bytes up to the end of its
body's length, `replyScan` asks to pass over exactly the body's length, with the id and the status
read (so the controller can tell whether it is the `200` to its prekey fetch). -/
theorem replyScan_responseHead {lw iv sv mv msg bv : List Byte} {L i st n : Nat}
    (hl : Varint lw L) (hl10 : lw.length ≤ 10) (hi : Varint iv i) (hi10 : iv.length ≤ 10)
    (hs : Varint sv st) (hs10 : sv.length ≤ 10) (hm : Varint mv msg.length) (hm10 : mv.length ≤ 10)
    (hb : Varint bv n) (hb10 : bv.length ≤ 10) (hn : 0 < n) :
    replyScan (responseHead lw iv sv mv msg bv) false false =
      (.skip n, { id := some i, status := some st, body := some n }) := by
  generalize hP : responseHead lw iv sv mv msg bv = P
  have h0 : P.drop 3 = lw ++ (0x08 :: (iv ++ (0x10 :: (sv ++ (0x1a :: (mv ++ (msg ++ (0x22 :: bv)))))))) := by
    rw [← hP]; rfl
  have hlen : P.length = 3 + (lw.length + (iv.length + (sv.length + (mv.length + (msg.length + bv.length + 1) + 1) + 1) + 1)) := by
    rw [← hP]; simp [responseHead]; omega
  have h1 := drop_after h0
  have h2 := drop_number h1
  have h3 := drop_number h2
  have h4 := drop_field h3
  rw [replyScan_eq]
  have hc : (P.take 2 == [8, 2] && PublicReceive.get P 2 == 0x1a) = true := by rw [← hP]; rfl
  rw [if_neg (by omega), if_pos hc, varintAt_varint hl hl10 h0]
  dsimp only
  obtain ⟨m, hm'⟩ : ∃ m, P.length + 1 = m + 4 := ⟨P.length - 3, by omega⟩
  rw [hm', loopG_yield _ (replyScanBody_number (Or.inl rfl) hi hi10 h1),
    loopG_yield _ (replyScanBody_number (Or.inr rfl) hs hs10 h2),
    loopG_yield _ (replyScanBody_text (Or.inl rfl) hm hm10 h3),
    loopG_done _ (replyScanBody_skip hb hb10 hn rfl h4)]
  rfl

theorem take_number {Z : List Byte} (tag : Byte) (v : List Byte) (j : Nat) (h : 1 + v.length ≤ j) :
    (tag :: (v ++ Z)).take j = tag :: (v ++ Z.take (j - (1 + v.length))) := by
  have := take_field (Z := Z) tag v [] j (by simpa using h)
  simpa using this

/-- **Before a response's body, nothing is skipped and no run reaches the body.** On every proper
prefix of a response's revealed bytes (from the kind bytes on), `replyScan` asks for more, and
`replyBudget`, which bounds the controller's next run (`budget`), stays within the response's head. -/
theorem responseHead_prefix {lw iv sv mv msg bv : List Byte} {L i st n : Nat}
    (hl : Varint lw L) (hl10 : lw.length ≤ 10) (hi : Varint iv i) (hi10 : iv.length ≤ 10)
    (hs : Varint sv st) (hs10 : sv.length ≤ 10) (hm : Varint mv msg.length) (hm10 : mv.length ≤ 10)
    (hb : Varint bv n) (hb10 : bv.length ≤ 10) (k : Nat) (hk2 : 2 ≤ k)
    (hk : k < (responseHead lw iv sv mv msg bv).length) :
    (replyScan ((responseHead lw iv sv mv msg bv).take k) false false).1 = .more ∧
      k + replyBudget ((responseHead lw iv sv mv msg bv).take k) false ≤ (responseHead lw iv sv mv msg bv).length := by
  generalize hP : responseHead lw iv sv mv msg bv = P at hk ⊢
  have h0 : P.drop 3 = lw ++ (0x08 :: (iv ++ (0x10 :: (sv ++ (0x1a :: (mv ++ (msg ++ (0x22 :: bv)))))))) := by
    rw [← hP]; rfl
  have hlen : P.length = 3 + (lw.length + (iv.length + (sv.length + (mv.length + (msg.length + bv.length + 1) + 1) + 1) + 1)) := by
    rw [← hP]; simp [responseHead]; omega
  have hiv := varint_ne_nil hi
  have hsv := varint_ne_nil hs
  have hmv := varint_ne_nil hm
  have hbv := varint_ne_nil hb
  have h1 := drop_after h0
  have h2 := drop_number h1
  have h3 := drop_number h2
  have h4 := drop_field h3
  generalize hQ : P.take k = Q
  have hQlen : Q.length = k := by rw [← hQ, List.length_take]; omega
  have hQd : ∀ p, Q.drop p = (P.drop p).take (k - p) := fun p => by rw [← hQ, drop_take']
  rw [replyScan_eq, replyBudget_eq, hQlen]
  by_cases hk3 : k < 3
  · simp only [hk3, if_true]; exact ⟨by trivial, by omega⟩
  rw [if_neg hk3, if_neg hk3]
  have hc : (Q.take 2 == [8, 2] && PublicReceive.get Q 2 == 0x1a) = true := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 3 := ⟨k - 3, by omega⟩
    rw [← hQ, ← hP]; rfl
  rw [if_pos hc]
  by_cases ha1 : k < 3 + lw.length
  · have hd : Q.drop 3 = lw.take (k - 3) := by
      rw [hQd, h0, List.take_append_of_le_length (by omega)]
    rw [varintAt_partial (varint_prefix hl (k - 3) (by omega)) hd,
      varintTooLong_short hd (by simp; omega)]
    exact ⟨by trivial, by simp only; omega⟩
  have hd3 : Q.drop 3 = lw ++ (0x08 :: (iv ++ (0x10 :: (sv ++ (0x1a :: (mv ++ (msg ++ (0x22 :: bv)))))))).take (k - 3 - lw.length) := by
    rw [hQd, h0, take_append_ge _ _ _ (by omega)]
  rw [varintAt_varint hl hl10 hd3]
  dsimp only
  -- Inside the id field.
  by_cases ha2 : k < 3 + lw.length + 1 + iv.length
  · obtain ⟨e, he, ht⟩ := rtail_number (Z := 0x10 :: (sv ++ (0x1a :: (mv ++ (msg ++ (0x22 :: bv)))))) (Or.inl rfl) hi hi10
      (k - (3 + lw.length)) (by omega)
    rw [← h1, ← hQd] at ht
    refine ⟨by rw [scan_rtail ht], ?_⟩
    have := budget_rtail (m := k) ht
    omega
  have hq1 := take_number (Z := 0x10 :: (sv ++ (0x1a :: (mv ++ (msg ++ (0x22 :: bv)))))) (0x08 : Byte) iv
    (k - (3 + lw.length)) (by omega)
  rw [← h1, ← hQd] at hq1
  have e1 : k + 1 = (k - 1) + 1 + 1 := by omega
  rw [e1, loopG_yield _ (replyScanBody_number (Or.inl rfl) hi hi10 hq1),
    loopG_yield _ (budgetBody_number (Or.inl rfl) hi hi10 hq1)]
  -- Inside the status field.
  by_cases ha3 : k < 3 + lw.length + 1 + iv.length + 1 + sv.length
  · obtain ⟨e, he, ht⟩ := rtail_number (Z := 0x1a :: (mv ++ (msg ++ (0x22 :: bv)))) (Or.inr rfl) hs hs10
      (k - (3 + lw.length + 1 + iv.length)) (by omega)
    rw [← h2, ← hQd] at ht
    refine ⟨by rw [scan_rtail ht], ?_⟩
    have := budget_rtail (m := k - 1) ht
    omega
  have hq2 := take_number (Z := 0x1a :: (mv ++ (msg ++ (0x22 :: bv)))) (0x10 : Byte) sv
    (k - (3 + lw.length + 1 + iv.length)) (by omega)
  rw [← h2, ← hQd] at hq2
  have e2 : k - 1 + 1 = (k - 2) + 1 + 1 := by omega
  rw [e2, loopG_yield _ (replyScanBody_number (Or.inr rfl) hs hs10 hq2),
    loopG_yield _ (budgetBody_number (Or.inr rfl) hs hs10 hq2)]
  -- Inside the message field.
  by_cases ha4 : k < 3 + lw.length + 1 + iv.length + 1 + sv.length + 1 + mv.length + msg.length
  · obtain ⟨e, he, ht⟩ := rtail_text (Z := 0x22 :: bv) (Or.inl rfl) hm hm10
      (k - (3 + lw.length + 1 + iv.length + 1 + sv.length)) (by omega)
    rw [← h3, ← hQd] at ht
    refine ⟨by rw [scan_rtail ht], ?_⟩
    have := budget_rtail (m := k - 2) ht
    omega
  have hq3 := take_field (Z := 0x22 :: bv) (0x1a : Byte) mv msg
    (k - (3 + lw.length + 1 + iv.length + 1 + sv.length)) (by omega)
  rw [← h3, ← hQd] at hq3
  have e3 : k - 2 + 1 = (k - 3) + 1 + 1 := by omega
  rw [e3, loopG_yield _ (replyScanBody_text (Or.inl rfl) hm hm10 hq3),
    loopG_yield _ (budgetBody_text (Or.inl rfl) hm hm10 hq3)]
  -- Inside the body's length.
  obtain ⟨e, he, ht⟩ := rtail_body hb hb10
    (k -(3 + lw.length + 1 + iv.length + 1 + sv.length + 1 + mv.length + msg.length)) (by omega)
  rw [← h4, ← hQd] at ht
  refine ⟨by rw [scan_rtail ht], ?_⟩
  have := budget_rtail (m := k - 3) ht
  omega

/-- Inside a response's payload (a data frame's payload byte comes next, the message is a response),
the controller's run is at most `max 1 (replyBudget reply openBody)`. -/
theorem budget_response (s : State) (hu : s.upgraded = true) (h0 : (PublicReceive.get s.frame 0 == on) = false)
    (h2 : (PublicReceive.get s.frame 2 == on) = false) (h4 : (PublicReceive.get s.frame 4 == on) = true)
    (hr : (PublicReceive.get s.frame 10).toNat * 256 + (PublicReceive.get s.frame 11).toNat ≠ 0)
    (ho : (PublicReceive.get s.frame 7).toNat < 8) (hm : s.message = [8, 2]) :
    budget s ≤ max 1 (replyBudget s.reply s.openBody) := by
  unfold budget
  have hr' : ((PublicReceive.get s.frame 10).toNat * 256 + (PublicReceive.get s.frame 11).toNat == 0) = false := by
    simp only [beq_eq_false_iff_ne]; exact hr
  have h82 : (s.message == [8, 2]) = true := by rw [hm]; decide
  simp only [hu, h0, h2, h4, hr', h82, Bool.not_true, Bool.or_false,
    Bool.false_eq_true, if_false, if_true, Nat.not_le.mpr ho]
  omega

/-- **T1 for a response's head (scanner level), e.g. the `200` to a prekey fetch.** Whatever its id,
status and message: while the controller walks the revealed bytes of a response up to its body's
length, every run it reveals from a state whose revealed response bytes are the first `k` bytes ends
at or before the body's first byte; and at the end of the body's length it is told to pass over
exactly the body (`go_skip`: none of it is ever revealed), with the id and status it needs to hand a
prekey bundle to the engines unopened. -/
theorem response_body_unrevealed {lw iv sv mv msg bv : List Byte} {L i st n : Nat}
    (hl : Varint lw L) (hl10 : lw.length ≤ 10) (hi : Varint iv i) (hi10 : iv.length ≤ 10)
    (hs : Varint sv st) (hs10 : sv.length ≤ 10) (hm : Varint mv msg.length) (hm10 : mv.length ≤ 10)
    (hb : Varint bv n) (hb10 : bv.length ≤ 10) (hn : 0 < n) :
    (∀ (s : State) (k : Nat), 2 ≤ k → k < (responseHead lw iv sv mv msg bv).length →
      s.reply = (responseHead lw iv sv mv msg bv).take k → s.openBody = false → s.upgraded = true →
      (PublicReceive.get s.frame 0 == on) = false → (PublicReceive.get s.frame 2 == on) = false →
      (PublicReceive.get s.frame 4 == on) = true →
      (PublicReceive.get s.frame 10).toNat * 256 + (PublicReceive.get s.frame 11).toNat ≠ 0 →
      (PublicReceive.get s.frame 7).toNat < 8 → s.message = [8, 2] →
      (replyScan s.reply false s.openBody).1 = .more ∧ k + budget s ≤ (responseHead lw iv sv mv msg bv).length) ∧
    replyScan (responseHead lw iv sv mv msg bv) false false =
      (.skip n, { id := some i, status := some st, body := some n }) := by
  refine ⟨?_, replyScan_responseHead hl hl10 hi hi10 hs hs10 hm hm10 hb hb10 hn⟩
  intro s k hk2 hk hs' hob hu h0 h2 h4 hr ho hmsg
  obtain ⟨hscan, hbud⟩ := responseHead_prefix hl hl10 hi hi10 hs hs10 hm hm10 hb hb10 k hk2 hk
  rw [hs', hob]
  refine ⟨hscan, ?_⟩
  have := budget_response s hu h0 h2 h4 hr ho hmsg
  rw [hs', hob] at this
  omega

end ReceiveProofs
