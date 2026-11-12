import TlsMpc.Node.Session.Common

/-!
# The session's connections (REORGANIZATION_PLAN.md stage S7; X2 builds on it)

Several circuits (SIGNAL_TOR_CIRCUITS = N ≥ 2, a send session): connections 1..N-1 are opened
before the first send, each with its own handshake, TLS session and unauthenticated WebSocket,
whose 101 is read at once. Per connection the controller keeps the response parser's state and the
request-id counter (`Pool`); the worker keeps its TLS and WebSocket state. Established up front
rather than lazily: the handshakes then cost nothing on the way to a send, and a proxy or circuit
that does not work fails the session before any contact's state has advanced.

- the non-recovery path (`Send.loop`): `openCircuits`, `toCircuit` (parked parser states);
- the recovery path (`Send.deliverJob`, `Serve.serve`): `openAll`, `openConnection`, `reconnect`
  (a connection the server or the proxy closed is replaced on the same index), `saveState`.

Moved from the controller's `main` (stage S7), same operations and order. No I/O primitive.
-/

namespace TlsMpc.Node.Session
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.Node TlsMpc.Node.Bytes

/-- The 101 to a connection's upgrade request. -/
def readUpgrade (session : TlsApplication.Session TlsWorker.BufferHandle) (on : Flow.Worker)
    (expected : List (BitVec 8)) : SessionM PublicReceive.State := do
  let mut s : PublicReceive.State := { PublicReceive.start expected with lenient := true }
  let mut fuel := 64
  while !s.upgraded do
    insist (fuel > 0) "receive budget exhausted"
    fuel := fuel - 1
    match ← TlsApplication.receive session with
    | .application handle =>
      let (next, complete) ← record handle.id s
      insist (!complete && next.requests.isEmpty) "unexpected server traffic during the upgrade"
      let (next, frames) ← liftResult (PublicReceive.replies next (← controlMasks on next))
      for (kind, frame) in frames do
        let handle ← Flow.Tls.publicBuffer on (toBytes frame)
        TlsApplication.send session handle frame.length
        insist (kind != 8) "WebSocket peer closed before completion"
      s := next
    | .control => pure ()
    | .closed => throw "TLS closed before the upgrade"
  return s

/-- Connection `index` from nothing: connect (through the proxy, with that connection's
credentials), handshake, unauthenticated WebSocket and its 101. A failure here is the session's.
Returns the connection's parser state. -/
def openConnection (index : Nat) : SessionM PublicReceive.State := do
  let c ← read
  let on := c.w.on index
  Flow.Server.connect on c.endpoint (← io (natural c.port)) (c.proxyFor (some index))
  let handshake ← Flow.Tls.handshake on c.tlsConfig
  insist (handshake.serverCertificateVerified && handshake.serverFinishedVerified) "handshake not accepted after retirement"
  let slot ← io (IO.mkRef (none : Option Bytes))
  let session ← io (Flow.Tls.application on handshake slot)
  let upgrade ← Flow.Upgrade.anonymous on
  let request := toBytes (c.anonymousUpgrade (toBits upgrade.val.1))
  let handle ← Flow.Tls.publicBuffer on request
  TlsApplication.send session handle request.length
  let connection : Connection := { session, slot }
  modifyPool fun p => { p with connections :=
    if index < p.connections.size then p.connections.set! index connection else p.connections.push connection }
  readUpgrade session on (toBits upgrade.val.2)

/-- The non-recovery path: connections 1..N-1 (N = `Context.sendCircuits`), each with its 101 read;
their parser states parked. Nothing with one connection. -/
def openCircuits : SessionM Unit := do
  let c ← read
  -- parked[i]: connection i's state while another is in use (0's is the loop's until then).
  modifyPool fun p => { p with parked := #[PublicReceive.start []] }
  for index in [1:c.sendCircuits] do
    let on := c.w.on index
    Flow.Server.connect on c.endpoint (← io (natural c.port)) (c.proxyFor (some index))
    let handshake ← Flow.Tls.handshake on c.tlsConfig
    insist (handshake.serverCertificateVerified && handshake.serverFinishedVerified) "handshake not accepted after retirement"
    let waitingFor ← io (IO.mkRef (none : Option Bytes))
    let session ← io (Flow.Tls.application on handshake waitingFor)
    let sendOn (bytes : Bytes) : SessionM Unit := do
      let handle ← Flow.Tls.publicBuffer on bytes
      TlsApplication.send session handle bytes.length
    let upgrade ← Flow.Upgrade.anonymous on
    sendOn (toBytes (c.anonymousUpgrade (toBits upgrade.val.1)))
    let mut s : PublicReceive.State := { PublicReceive.start (toBits upgrade.val.2) with lenient := c.exportPath.isSome }
    let mut fuel := 64
    while !s.upgraded do
      insist (fuel > 0) "receive budget exhausted"
      fuel := fuel - 1
      match ← TlsApplication.receive session with
      | .application handle =>
        let (next, complete) ← record handle.id s
        insist (!complete && next.requests.isEmpty) "unexpected server traffic during the upgrade"
        let (next, frames) ← liftResult (PublicReceive.replies next (← controlMasks on next))
        for (kind, frame) in frames do
          sendOn (toBytes frame)
          insist (kind != 8) "WebSocket peer closed before completion"
        s := next
      | .control => pure ()
      | .closed => throw "TLS closed before the upgrade"
    let connection : Connection := { session, slot := waitingFor }
    modifyPool fun p => { p with connections := p.connections.push connection, parked := p.parked.push s }

/-- The non-recovery path, before each send: move to the contact's connection
(`Circuits.assign` over the session's `recipients`). Returns that connection's parser state and
the send's request id (2^63 + the sends so far on that connection). One connection (N ≤ 1): the
state and id the loop gave, exactly as without Tor. -/
def toCircuit (recipients : List Nat) (s : PublicReceive.State) (contact id : Nat) :
    SessionM (PublicReceive.State × Nat) := do
  let c ← read
  let target := Circuits.assign recipients (max c.sendCircuits 1) contact
  modifyReport fun r => { r with circuitSends := r.circuitSends ++ [(contact, target)] }
  if c.sendCircuits ≤ 1 then return (s, id)
  let pool := (← get).pool
  let here := pool.current
  let sent := pool.counters.getD target 0
  modifyPool fun p => { p with counters := p.counters.set! target (sent + 1) }
  if target == here then return (s, 2 ^ 63 + sent)
  -- The connection in use parks its state; the target's is taken up.
  modifyPool fun p => { p with parked := p.parked.set! here s, current := target }
  return ((← get).pool.parked.getD target s, 2 ^ 63 + sent)

/-- The recovery path: the parser state of the connection in use, kept for the next send on it. -/
def saveState (s : PublicReceive.State) : SessionM Unit :=
  modifyPool fun p => { p with states := p.states.set! p.current s }

/-- Replace the connection in use after it was reported closed: a new handshake and upgrade on the
same index (and the same proxy credentials); the other connections are kept. -/
def reconnect : SessionM Unit := do
  let c ← read
  let index := (← get).pool.current
  Flow.Refresh.drop c.w   -- a response body half collected on it
  Flow.Server.reset (c.w.on index)
  let opened ← openConnection index
  modifyPool fun p => { p with states := p.states.set! index opened }
  note s!"connection {index} was closed and replaced"

/-- The recovery path: connection 0 is connected and its upgrade request sent (`Start`); its 101 is
read, then connections 1..N-1 are opened. Returns connection 0's parser state. -/
def openAll (accept : Bytes) : SessionM PublicReceive.State := do
  let c ← read
  let first ← readUpgrade (← get).pool.first.session (c.w.on 0) (toBits accept)
  modifyPool fun p => { p with states := #[first] }
  for index in [1:max c.sendCircuits 1] do
    let opened ← openConnection index
    modifyPool fun p => { p with states := p.states.push opened }
  pure first

end TlsMpc.Node.Session
