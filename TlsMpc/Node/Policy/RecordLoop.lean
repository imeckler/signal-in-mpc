import TlsMpc.Node.Policy.Receive

/-!
# The record loop: the policy core the session runs (T1; PROOF_GAPS.md C1)

`Session/Common.lean`'s `record` reveals and parses one authenticated server record byte by byte.
Its whole policy core is `RecordLoop.run` below: per record it decides the runs to reveal
(`mayReveal`, `budget`), steps the policy state over them (`step`, checked byte by byte:
`stepRun`), passes bodies over unrevealed (`passBulk` as far as `passRoom` allows, then `passOne`:
`passRun`), and hands every completed envelope on before clearing the list. Everything else is a
parameter (`Ops`): the engines' length probe and reveal (`Flow.Tls.recordLength`, `revealRange`),
what happens to passed-over bytes (`Flow.Receive.take`, `Flow.Refresh.take`, the record of events),
the bookkeeping of a revealed run (report, trace, record) and the envelope callback
(`Context.envelope`). The definition is monad-generic; the session runs it at `SessionM` with its
operations (`Common.recordOps`), and T1 is proved about the same definition at pure operations
(`ReceiveLoop.t1_all`, `TlsMpc/Node/Policy/ReceiveLoop.lean`).

**Fuel.** The loop that ran before (a `while` loop) had none. `run` gives `loop` the record's length
plus one steps: every step with `offset < length` advances `offset` by at least one, so the length
plus one steps always suffice when the engines report the same length at every reveal (the
assumption of T1 on `revealRange`, below); the loop then behaves exactly as the `while` loop did.
If an engine reported a longer record at a later reveal than its length probe did, the loop now
fails ("the record's length changed while it was read") where the `while` loop would have read on.

No I/O primitive; no emitter imports this module.
-/

namespace RecordLoop
open PublicReceive

/-- What one record's loop does besides the reveal policy (`β`: the engines' byte type).
- `length`: the record's length (the engines' length probe; the session also records the event);
- `reveal offset count`: the engines reveal `count` bytes of the record from `offset` (fewer at its
  end): the record's length and the bytes;
- `passed offset count capture collect`: `count` body bytes from `offset` are passed over unrevealed
  (`capture`: a delivered envelope's sealed content, `collect`: a prekey response's body, to the
  engines);
- `revealed offset bytes`: a run was revealed (the report, the trace, the record of events);
- `envelope kind size`: a delivered envelope was completed (dealt with before anything further is
  read);
- `byte`: an engine byte as the parsers' byte. -/
structure Ops (m : Type → Type) (β : Type) where
  length : m Nat
  reveal : Nat → Nat → m (Nat × List β)
  passed : Nat → Nat → Bool → Bool → m Unit
  revealed : Nat → List β → m Unit
  envelope : Nat → Nat → m Unit
  byte : β → Byte

/-- The check of a revealed run, byte by byte: `step` each byte; after each byte but the last, the
rest of the run must still be within `mayReveal` and `budget` of the new state (the bytes were
revealed before they are checked). Also whether a response to the pending request completed. -/
def stepRun : State → Bool → List Byte → Except String (State × Bool)
  | s, c, [] => .ok (s, c)
  | s, c, b :: rest =>
    match step s b with
    | .error e => .error e
    | .ok (next, done) =>
      if rest.length == 0 || (mayReveal next && decide (rest.length ≤ budget next)) then
        stepRun next (c || done) rest
      else .error "revealed range went past what may be revealed"

section Generic
variable {m : Type → Type} [Monad m] [MonadExceptOf String m] {β : Type}

/-- An `Except` result in the loop's monad. -/
def lift {α : Type} : Except String α → m α
  | .ok a => pure a
  | .error e => throw e

/-- Every completed envelope, in order, to `Ops.envelope`. -/
def envelopes (o : Ops m β) : List (Nat × Nat) → m Unit
  | [] => pure ()
  | (kind, size) :: rest => do
    o.envelope kind size
    envelopes o rest

/-- The record loop from `offset`, `length` as last reported, with `fuel` steps (`run`). -/
def loop (o : Ops m β) : Nat → State → Bool → Nat → Nat → m (State × Bool)
  | 0, _, _, _, _ => throw "the record's length changed while it was read"
  | fuel + 1, s, complete, offset, length =>
    if offset < length then
      if s.skip > 0 then do
        -- A server request's body (or a response's): passed over, never revealed.
        let count := min s.skip (length - offset)
        o.passed offset count s.capture s.collect
        -- As much of it as `passRoom` allows in one step (`passRun_bulk`: the state the byte-by-byte
        -- steps would give), the rest one byte at a time. A response may complete in its body.
        let bulk := min count (passRoom s)
        let (s, done) ← lift (passRun (count - bulk) (passBulk bulk s))
        -- A completed envelope is dealt with before anything further is read.
        envelopes o s.envelopes
        loop o fuel { s with envelopes := [] } (complete || done) (offset + count) length
      else do
        if !mayReveal s then throw "refusing to reveal a server-initiated message"
        -- The engines reveal the run first; it is checked byte by byte afterwards.
        let (length, bytes) ← o.reveal offset (budget s)
        let (s, complete) ← if offset < length then do
            if bytes.isEmpty then throw "missing revealed bytes"
            o.revealed offset bytes
            lift (stepRun s complete (bytes.map o.byte))
          else pure (s, complete)
        envelopes o s.envelopes
        loop o fuel { s with envelopes := [] } complete (offset + (if bytes.isEmpty then 1 else bytes.length)) length
    else pure (s, complete)

/-- **One authenticated record, revealed and parsed** from the policy state `start`: the state
after it, and whether a response to the pending request completed in it. -/
def run (o : Ops m β) (start : State) : m (State × Bool) := do
  let length ← o.length
  loop o (length + 1) start false 0 length

end Generic

end RecordLoop
