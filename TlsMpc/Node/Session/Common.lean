import TlsMpc.Node.Session.State
import TlsMpc.Node.Policy.RecordLoop
import TlsMpc.Node.Policy.Close

/-!
# What every session kind uses (REORGANIZATION_PLAN.md stage S7)

- the agreed values: `peer` (the other node, `PeerMsg`), `peerClock` / `agreedNow`, joint `nonce`,
  `nextId` (request ids outside the sends' counter);
- the server's records: `record` (reveal and parse one authenticated record byte by byte, within
  the reveal policy `PublicReceive.mayReveal` / `budget`; a completed envelope is handed to the
  context's `envelope`): the policy core `RecordLoop.run` (`Policy/RecordLoop.lean`, the
  definition T1 is proved about: `ReceiveLoop.t1_all`) at this session's operations
  (`recordOps`); `sendPublic`;
- waiting for a response: `awaitReply`, `keepAlive` (a failure ends the session) and their
  recovery forms `receiveSoft`, `awaitSoft`, `keepAliveSoft`, `drainOne` (a closed connection is
  an outcome); under the libsignal profile the keepalive is a WebSocket ping after 31 s (`sendPing`);
- `closeWebSocket`: the orderly end of a session under the libsignal profile (a WebSocket Close
  1000 on every connection);
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

/-- The TLS session of the connection in use (monad-generic: the send functions' definitions use it). -/
def appNowG {m : Type → Type} [Monad m] [MonadStateOf State m] : m (TlsApplication.Session TlsWorker.BufferHandle) := do
  let pool := (← get).pool
  return (pool.connection pool.current).session

abbrev appNow : SessionM (TlsApplication.Session TlsWorker.BufferHandle) := appNowG

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

/-- The effects of one record's loop (`RecordLoop.Ops`): the engines' length probe and reveal of
record `handle`, the passed-over bytes to the engines, the bookkeeping of a revealed run, and the
context's envelope callback. -/
def recordOps (c : Context) (handle : Nat) : RecordLoop.Ops SessionM UInt8 where
  length := do
    -- The length alone (an offset past any record reveals no byte).
    let length := (← Flow.Tls.recordLength c.w handle).val.1
    c.ch.record (.record (← current) handle length)
    pure length
  reveal offset count := do
    let out ← Flow.Tls.revealRange c.w handle offset count
    pure out.val
  passed offset count capture collect := do
    c.ch.record (.passedOver handle offset count
      (if capture then .envelope else if collect then .prekeyResponse else .nowhere))
    if capture then
      -- A delivered envelope's sealed content goes to the engines as it is.
      Flow.Receive.take c.w handle offset count
    if collect then
      -- The body of the 200 to the pending prekey fetch goes to the engines as it is.
      Flow.Refresh.take c.w handle offset count
  revealed offset bytes := do
    modifyReport fun r => { r with revealed := r.revealed + bytes.length }
    -- Diagnostics: the revealed (public) bytes, on request.
    if c.hooks.trace then
      c.ch.log (.revealed bytes)
    c.ch.record (.revealed handle offset bytes)
  envelope kind size := do c.envelope kind size
  byte b := BitVec.ofNat 8 b.toNat

/-- Reveal and parse one authenticated record, byte by byte: the policy core `RecordLoop.run`
(`TlsMpc/Node/Policy/RecordLoop.lean`, the definition T1 is proved about) with this session's
operations. A server request's body is passed over unrevealed; a delivered envelope's sealed content
and a prekey response's body go to the engines as they are. A completed envelope is dealt with
(`Context.envelope`) before anything further is read. -/
def record (handle : Nat) (start : PublicReceive.State) : SessionM (PublicReceive.State × Bool) := do
  RecordLoop.run (recordOps (← read) handle) start

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

/-- libsignal profile: the keepalive of a send session, as libsignal-net's (`rust/net/infra/src/ws/
connection.rs` lines 304-326, `Event::ConnectionIdle`: `Message::Ping(vec![*ping_count])`, the
count from 1 per connection; `WS_KEEP_ALIVE_INTERVAL` 31 s): a masked ping on the connection in use
(`PublicReceive.ping`, a fresh joint mask), not awaited (the pong is a control frame the parser
skips when the next record is read). -/
def sendPing : SessionM Unit := do
  let c ← read
  let index ← current
  let count ← modifyGet fun st =>
    let (pool, count) := st.pool.nextPing index
    (count, { st with pool })
  let random := (← Flow.Random.joint c.w).val
  sendPublic (toBytes (PublicReceive.ping (count % 256) (toBits (random.take 4))))

/-- The server drops a socket that is silent for 90 seconds, and establishing one device's session
takes about that long. Before each step: if 20 seconds have passed on the agreed clock since the
last exchange, a keepalive is sent and its answer awaited. Under the libsignal profile, as an
Android client: after 31 seconds without an exchange, a WebSocket ping (`sendPing`), no request and
nothing awaited. -/
def keepAlive (s : PublicReceive.State) : SessionM PublicReceive.State := do
  let c ← read
  let now ← agreedClock
  if c.official then
    if now < (← get).quiet + 31000 then return s
    sendPing
    modify fun st => { st with quiet := now }
    return s
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

/-- `keepAlive` with a closed connection as an outcome (`false`). Under the libsignal profile the
ping is not answered, so the connection is polled once before it (a record found is kept for the
next read): a connection the server or the proxy closed is the outcome a keepalive left unanswered
gives. -/
def keepAliveSoft (s : PublicReceive.State) : SessionM (PublicReceive.State × Bool) := do
  let c ← read
  let now ← agreedClock
  if c.official then
    if now < (← get).quiet + 31000 then return (s, true)
    let pool := (← get).pool
    let slot := (pool.connection pool.current).slot
    if (← io slot.get).isNone then
      match ← Flow.Server.poll (c.w.on pool.current) with
      | .closed => return (s, false)
      | .nothing => pure ()
      | .record wire => io (slot.set (some wire))
    sendPing
    modify fun st => { st with quiet := now }
    return (s, true)
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

/-- Polls for the server's answer to our Close (each at most 20 ms apart: about three seconds). -/
def closePolls : Nat := 150

/-- Connection `index` at the orderly end of a session (libsignal profile): skipped if the server or
the proxy already closed it; otherwise our Close (`PublicReceive.close`: code 1000, no reason, a
fresh joint mask), sealed as a public buffer like every control frame, then at most `closePolls`
polls until the server ends the connection. What arrives meanwhile (the server's Close echo) is not
opened: nothing more of the server's bytes is revealed, and nothing is answered after a Close (RFC
6455 section 5.5.1). The polls are counted, not timed, so both controllers stop at the same one. -/
def closeConnection (index : Nat) : SessionM Unit := do
  let c ← read
  let on := c.w.on index
  let connection := (← get).pool.connection index
  let slot := connection.slot
  if (← io slot.get).isNone then
    match ← Flow.Server.poll on with
    | .closed => return
    | .nothing => pure ()
    | .record _ => pure ()
  io (slot.set none)
  let random := (← Flow.Random.joint c.w).val
  let frame := toBytes (PublicReceive.close (toBits (random.take 4)))
  c.ch.record (.sentPublic index frame)
  let handle ← Flow.Tls.publicBuffer c.w frame
  TlsApplication.send connection.session handle frame.length
  for _ in [0:closePolls] do
    match ← Flow.Server.poll on with
    | .closed => return
    | .nothing => c.ch.sleep 20
    | .record _ => pure ()

/-- **The orderly end of a session** (not of a failed one: that stays an abort), libsignal profile:
every connection of the session gets a WebSocket Close 1000 with no reason (`closeConnection`), as
libsignal-net sends one when it lets a connection go (`Policy/Close.lean`); the caller then aborts
the TLS session as before. No TLS close_notify: libsignal's WebSocket over HTTP/1.1 drops the
stream after the Close without `SSL_shutdown` (tokio-tungstenite's `send` only flushes, and
tokio-boring/boring's `SslStream` sends close_notify only from `poll_shutdown`, which nothing on that
path calls; its `Drop` frees the `SSL` without it). A connection that cannot be closed (the server
went first, or the worker refused) is logged and skipped: the session's work is done by then and
its outcome stands. Legacy profile: nothing (the session ends as before). -/
def closeWebSocket : SessionM Unit := do
  let c ← read
  if !c.official then return
  for index in [0:(← get).pool.connections.size] do
    try closeConnection index
    catch e => c.ch.log (.recovery s!"connection {index} was not closed with a WebSocket Close: {e}")

end TlsMpc.Node.Session
