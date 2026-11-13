import TlsMpc.Node.Session.State

/-!
# What every session kind uses (REORGANIZATION_PLAN.md stage S7)

- the agreed values: `peer` (the other node, `PeerMsg`), `peerClock` / `agreedNow`, joint `nonce`,
  `nextId` (request ids outside the sends' counter);
- the server's records: `record` (reveal and parse one authenticated record byte by byte, within
  the reveal policy `PublicReceive.mayReveal` / `budget`; a completed envelope is handed to the
  context's `envelope`), `sendPublic`;
- waiting for a response: `awaitReply`, `keepAlive` (a failure ends the session) and their
  recovery forms `receiveSoft`, `awaitSoft`, `keepAliveSoft`, `drainOne` (a closed connection is
  an outcome);
- `note`: a public event of the recovery path (report, log, record).

Moved from the controller's `main` (stage S7) with the same operations, order and error texts; the
references it closed over are fields of `State`. No I/O primitive (the lint's `io-baseline`).
-/

namespace TlsMpc.Node.Session
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.Node TlsMpc.Node.Bytes

/-- One masking key per queued control reply (`PublicReceive.replies`), each the first 4 bytes of
its own joint randomness: RFC 6455 section 5.3 requires a fresh key for each frame. None when
nothing is queued. -/
def controlMasks (on : Flow.Worker) (s : PublicReceive.State) : M (List (List (BitVec 8))) :=
  (List.range (PublicReceive.queuedReplies s)).mapM fun _ => do
    let random ← Flow.Random.joint on
    pure (toBits (random.val.take 4))

/-- The connection in use. -/
def current : SessionM Nat := return (← get).pool.current

/-- The TLS session of the connection in use. -/
def appNow : SessionM (TlsApplication.Session TlsWorker.BufferHandle) := do
  let pool := (← get).pool
  return (pool.connection pool.current).session

/-- Public bytes (a frame or request built here) to the server on the connection in use. -/
def sendPublic (bytes : Bytes) : SessionM Unit := do
  let c ← read
  c.ch.record (.sentPublic (← current) bytes)
  let handle ← Flow.Tls.publicBuffer c.w bytes
  TlsApplication.send (← appNow) handle bytes.length

/-- The other node (`PeerMsg`, through the worker's exchange): its message of the same kind. -/
def peer (msg : PeerMsg) : SessionM PeerMsg := do
  let c ← read
  c.ch.exchange c.w.link msg

/-- The two clocks: each controller reads its own, they tell each other, and both use the later one
if the two are within two minutes (`Clock.agreed_within`). -/
def peerClock : SessionM Nat := do
  let mine ← (← read).ch.clock
  match ← peer (.clock mine) with
  | .clock theirs => liftResult (Node.Policy.Clock.agree mine theirs)
  | _ => throw "invalid clock reply"

/-- The agreed clock (as `peerClock`). -/
def agreedClock : SessionM Nat := peerClock

/-- The current time (milliseconds), agreed. (A test may fix it with SIGNAL_LOCAL_TIMESTAMP, the
same for both.) -/
def agreedNow : SessionM Nat := do
  match (← read).hooks.timestamp with
  | some fixed => pure fixed
  | none => peerClock

/-- A new nonce for each seal of a contact's state: joint randomness. -/
def nonce : SessionM Bytes := do
  let random := (← Flow.Random.joint (← read).w).val
  insist (random.take 8 != List.replicate 8 255) "invalid joint randomness"
  pure (random.take 8)

/-- Request ids of the session's own requests (keepalives, fetches, ceremony calls), apart from
the sends' counter from 2^63. -/
def nextId : SessionM Nat :=
  modifyGet fun s => (2 ^ 63 + 2 ^ 32 + s.extraIds, { s with extraIds := s.extraIds + 1 })

/-- Note the agreed time of an exchange with the server (`keepAlive` counts from it). -/
def touch : SessionM Unit := do
  let now ← agreedClock
  modify fun s => { s with quiet := now }

/-- TEST (no database): this party's key share of a contact, its own randomness. -/
def freshShare : SessionM (Secret Bytes) := do
  let random ← (← read).ch.random 32
  -- below 2^254, so below the share modulus
  pure (random.map fun bytes => bytes.take 31 ++ [(bytes.getD 31 0) &&& 0x3f])

/-- A public event of the recovery path: in the report, on standard error and in the record. -/
def note (event : String) : SessionM Unit := do
  let c ← read
  modifyReport fun r => { r with recoveryLog := r.recoveryLog ++ [event] }
  c.ch.log (.recovery event)
  c.ch.record (.recovery event)

/-- Reveal and parse one authenticated record, byte by byte. A server request's body is passed
over unrevealed; a delivered envelope's sealed content and a prekey response's body go to the
engines as they are. A completed envelope is dealt with (`Context.envelope`) before anything
further is read. -/
def record (handle : Nat) (start : PublicReceive.State) : SessionM (PublicReceive.State × Bool) := do
  let c ← read
  let w := c.w
  let mut s := start
  let mut complete := false
  let mut offset := 0
  -- The length alone (an offset past any record reveals no byte).
  let mut length := (← Flow.Tls.recordLength w handle).val.1
  c.ch.record (.record (← current) handle length)
  while offset < length do
    if s.skip > 0 then
      -- A server request's body: passed over, never revealed.
      let count := min s.skip (length - offset)
      c.ch.record (.passedOver handle offset count
        (if s.capture then .envelope else if s.collect then .prekeyResponse else .nowhere))
      if s.capture then
        -- A delivered envelope's sealed content goes to the engines as it is.
        Flow.Receive.take w handle offset count
      if s.collect then
        -- The body of the 200 to the pending prekey fetch goes to the engines as it is.
        Flow.Refresh.take w handle offset count
      -- As much of it as `passRoom` allows in one step (`passRun_bulk`: the state the byte-by-byte
      -- steps would give), the rest one byte at a time. A response may complete in its body.
      let bulk := min count (PublicReceive.passRoom s)
      s := PublicReceive.passBulk bulk s
      for _ in [0:count - bulk] do
        let (next, done) ← liftResult (PublicReceive.passOne s)
        s := next
        complete := complete || done
      offset := offset + count
      -- A completed envelope is dealt with before anything further is read.
      for (kind, size) in s.envelopes do c.envelope kind size
      s := { s with envelopes := [] }
      continue
    insist (PublicReceive.mayReveal s) "refusing to reveal a server-initiated message"
    let count := PublicReceive.budget s
    let out ← Flow.Tls.revealRange w handle offset count
    length := out.val.1
    let bytes := out.val.2
    if offset < length then
      insist (!bytes.isEmpty) "missing revealed bytes"
      modifyReport fun r => { r with revealed := r.revealed + bytes.length }
      -- Diagnostics: the revealed (public) bytes, on request.
      if c.hooks.trace then
        c.ch.log (.revealed bytes)
      c.ch.record (.revealed handle offset bytes)
      for (byte, index) in bytes.zipIdx do
        let (next, done) ← liftResult (PublicReceive.step s (BitVec.ofNat 8 byte.toNat))
        -- What is left of this step must still be within what may be revealed.
        insist (bytes.length - (index + 1) == 0 || (PublicReceive.mayReveal next && bytes.length - (index + 1) ≤ PublicReceive.budget next))
          "revealed range went past what may be revealed"
        s := next
        complete := complete || done
    offset := offset + (if bytes.isEmpty then 1 else bytes.length)
    for (kind, size) in s.envelopes do c.envelope kind size
    s := { s with envelopes := [] }
  return (s, complete)

/-- Wait for the pending response; records are read and answered as in the send loop. -/
def awaitReply : Nat → PublicReceive.State → SessionM PublicReceive.State
  | 0, _ => throw "receive budget exhausted"
  | fuel+1, s => do
    let c ← read
    match ← TlsApplication.receive (← appNow) with
    | .application handle =>
      let (s, complete) ← record handle.id s
      let (s, frames) ← liftResult (PublicReceive.replies s (← controlMasks c.w s))
      for (kind, frame) in frames do
        sendPublic (toBytes frame)
        insist (kind != 8) "WebSocket peer closed before completion"
      for request in s.requests do
        let random := (← Flow.Random.joint c.w).val
        let (frame, message) ← liftResult (PublicReceive.reply request (toBits (random.take 4)))
        unless message do sendPublic (toBytes frame)
      let s := { s with requests := [] }
      if complete then return s
      awaitReply fuel s
    | .control => awaitReply fuel s
    | .closed => throw "TLS closed before a response"

/-- The server drops a socket that is silent for 90 seconds, and establishing one device's session
takes about that long. Before each step: if 20 seconds have passed on the agreed clock since the
last exchange, a keepalive is sent and its answer awaited. -/
def keepAlive (s : PublicReceive.State) : SessionM PublicReceive.State := do
  let c ← read
  let now ← agreedClock
  if now < (← get).quiet + 20000 then return s
  let id ← nextId
  let random := (← Flow.Random.joint c.w).val
  sendPublic (toBytes (← liftResult (PublicReceive.keepalive id (toBits (random.take 4)))))
  modify fun st => { st with quiet := now }   -- the time it was sent: reading its answer may itself take long
  let s ← awaitReply 64 (PublicReceive.expect s id)
  insist (s.status == 200) "keepalive was refused"
  pure s

/-- The next record of the connection in use, or `none`: the worker reported that the server or
the proxy closed the connection (`pollRecord` replies `[0]`; both parties see it at the same
request). The worker and the other connections are unaffected. -/
def receiveSoft : SessionM (Option (TlsApplication.Received TlsWorker.BufferHandle)) := do
  let c ← read
  let pool := (← get).pool
  let index := pool.current
  let on := c.w.on index
  let slot := (pool.connection index).slot
  if (← io slot.get).isNone then
    let deadline := (← c.ch.monotonic) + 30000
    let mut waitingFor := true
    while waitingFor do
      insist ((← c.ch.monotonic) < deadline) "no record from the server within 30 seconds"
      match ← Flow.Server.poll on with
      | .closed => return none
      | .nothing => c.ch.sleep 10
      | .record wire =>
        io (slot.set (some wire))
        waitingFor := false
  match ← TlsApplication.receive (← appNow) with
  | .closed =>
    -- close_notify: the connection itself goes next.
    for _ in [0:1000] do
      match ← Flow.Server.poll on with
      | .closed => return none
      | .nothing => pure ()
      | .record _ => throw "a record after close_notify"
      c.ch.sleep 10
    throw "the server closed TLS but kept the connection open"
  | other => return some other

/-- Wait for the pending response on the connection in use. `false`: the connection was closed
first (whatever was in flight on it is unanswered). -/
def awaitSoft : Nat → PublicReceive.State → SessionM (PublicReceive.State × Bool)
  | 0, _ => throw "receive budget exhausted"
  | fuel+1, s => do
    let c ← read
    match ← receiveSoft with
    | none => return (s, false)
    | some (.application handle) =>
      let (s, complete) ← record handle.id s
      let (s, frames) ← liftResult (PublicReceive.replies s (← controlMasks c.w s))
      -- A close frame from the server is answered; the closed connection is then reported by the worker.
      for (_, frame) in frames do sendPublic (toBytes frame)
      for request in s.requests do
        let random := (← Flow.Random.joint c.w).val
        let (frame, message) ← liftResult (PublicReceive.reply request (toBits (random.take 4)))
        unless message do sendPublic (toBytes frame)
      let s := { s with requests := [] }
      if complete then return (s, true)
      awaitSoft fuel s
    | some .control => awaitSoft fuel s
    | some .closed => return (s, false)

/-- `keepAlive` with a closed connection as an outcome (`false`). -/
def keepAliveSoft (s : PublicReceive.State) : SessionM (PublicReceive.State × Bool) := do
  let c ← read
  let now ← agreedClock
  if now < (← get).quiet + 20000 then return (s, true)
  let id ← nextId
  let random := (← Flow.Random.joint c.w).val
  sendPublic (toBytes (← liftResult (PublicReceive.keepalive id (toBits (random.take 4)))))
  modify fun st => { st with quiet := now }
  awaitSoft 64 (PublicReceive.expect s id)

/-- One record that arrived on the connection in use while nothing was awaited (a pong, a ping or
close of the server). `false`: the connection is gone. -/
def drainOne (s : PublicReceive.State) : SessionM (PublicReceive.State × Bool) := do
  let c ← read
  match ← receiveSoft with
  | none => return (s, false)
  | some (.application handle) =>
    let (s, complete) ← record handle.id s
    insist (!complete) "unsolicited service response"
    let (s, frames) ← liftResult (PublicReceive.replies s (← controlMasks c.w s))
    for (_, frame) in frames do sendPublic (toBytes frame)
    for request in s.requests do
      let random := (← Flow.Random.joint c.w).val
      let (frame, message) ← liftResult (PublicReceive.reply request (toBits (random.take 4)))
      unless message do sendPublic (toBytes frame)
    return ({ s with requests := [] }, true)
  | some .control => return (s, true)
  | some .closed => return (s, false)

end TlsMpc.Node.Session
