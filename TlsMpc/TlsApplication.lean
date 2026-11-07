import TlsMpc.TlsClient
import TlsMpc.TlsApplicationPolicy
import Std.Sync.Mutex

/-! Application controller over opaque MPC handles. There is no operation
returning application plaintext to Lean. Authenticated protocol-control events
are the backend's deliberately narrow public output; ticket/fragment contents
remain private. Durable restart of this live state is not supported: reconnect
with fresh keys after process loss. Native binding and erasure are separate
backend obligations and must not be acknowledged without implementation. -/
namespace TlsMpc.TlsApplication
open TlsWire TlsClient

inductive Event (S : Type) where
  | application (payload : S)
  | keyUpdate (request : Bool)
  | skippedControl
  | closeNotify
  | fatal

structure Backend (S : Type) where
  /-- Plaintext is an opaque shared buffer. Only the TLS ciphertext is public. -/
  sealApplication : ApplicationKeys S → Nat → S → Nat → Nat → M Bytes
  /-- Only public TLS controls, never application or Signal plaintext. -/
  sealControl : ApplicationKeys S → Nat → Nat → Bytes → M Bytes
  /-- Authenticate first. Parse/assemble post-handshake fragments inside MPC.
  The backend must never reinterpret unvalidated bytes as a public Event. -/
  openRecord : ApplicationKeys S → Nat → Bytes → M (Event S)
  /-- Derive new sending handles and retire their predecessors. -/
  rotateSend : ApplicationKeys S → M (ApplicationKeys S)
  /-- Receive generations have no artificial sender-policy epoch ceiling. -/
  rotateReceive : ApplicationKeys S → M (ApplicationKeys S)
  abort : M Unit

private structure Live (S : Type) where
  keys : ApplicationKeys S
  policy : TlsApplicationPolicy.State := {}

structure Session (S : Type) where private mk ::
  private backend : Backend S
  private transport : Transport
  private state : Std.Mutex (Live S)
  private receiveGate : Std.Mutex Unit

def make (backend : Backend S) (transport : Transport) (handshake : TlsClient.Session S) : IO (Session S) := do
  return ⟨backend,transport,← Std.Mutex.new {
    keys := handshake.keys
    policy := { sendNext := handshake.sendSequence, receiveNext := handshake.receiveSequence } },
    ← Std.Mutex.new ()⟩

private def guarded (session : Session S) (action : IO.Ref (Live S) → M α) : M α :=
  ExceptT.mk <| session.state.atomically fun state => do
    (cleanupOnError (action state) (do
      liftM (m := IO) (n := M) (state.modify fun live =>
        { live with policy := TlsApplicationPolicy.abort live.policy })
      session.backend.abort)).run

private def reserve (state : IO.Ref (Live S))
    (operation : TlsApplicationPolicy.State → Option (TlsApplicationPolicy.Reservation × TlsApplicationPolicy.State)) : M TlsApplicationPolicy.Reservation := do
  let live ← liftM (m := IO) (n := M) state.get
  let some (ticket,after) := operation live.policy | throw "TLS traffic reservation rejected"
  liftM (m := IO) (n := M) (state.set { live with policy := after })
  return ticket

private def sendWire (session : Session S) (wire : Bytes) : M Unit := do
  let (records,pending) ← liftResult (TlsWire.records 2 wire)
  insist (records.length == 1 && pending.isEmpty && wire.length ≥ 22 && wire.length ≤ 16406 &&
    records.head!.kind == 23 && records.head!.version == 0x0303) "invalid protected application record"
  session.transport.send wire

private def finishClose (session : Session S) (state : IO.Ref (Live S)) : M Unit := do
  let live ← liftM (m := IO) (n := M) state.get
  if live.policy.sendClosed && live.policy.receiveClosed then
    liftM (m := IO) (n := M) (state.set { live with policy := TlsApplicationPolicy.abort live.policy })
    session.backend.abort

private def updateLocked (session : Session S) (state : IO.Ref (Live S)) (request : Bool) : M Unit := do
  let ticket ← reserve state (fun p => TlsApplicationPolicy.reserveUpdate p request)
  let live ← liftM (m := IO) (n := M) state.get
  -- Reserve, seal and SEND under old keys. Only then derive/install new keys.
  let wire ← session.backend.sealControl live.keys ticket.sequence 22 [24,0,0,1,if request then 1 else 0]
  insist (wire.length == 27) "TLS KeyUpdate ciphertext length mismatch"
  sendWire session wire
  let keys ← session.backend.rotateSend live.keys
  let some policy := TlsApplicationPolicy.commitUpdate live.policy | throw "TLS key-update commit rejected"
  liftM (m := IO) (n := M) (state.set { keys,policy })

def keyUpdate (session : Session S) (request : Bool := false) : M Unit :=
  guarded session fun state => updateLocked session state request

def send (session : Session S) (payload : S) (bytes : Nat) (padding : Nat := 0) : M Unit :=
  guarded session fun state => do
    insist (bytes + 1 + padding ≤ 16385) "TLS application payload exceeds record bound"
    let live ← liftM (m := IO) (n := M) state.get
    if TlsApplicationPolicy.needsUpdate live.policy then updateLocked session state false
    let ticket ← reserve state TlsApplicationPolicy.reserveApplication
    let current ← liftM (m := IO) (n := M) state.get
    let wire ← session.backend.sealApplication current.keys ticket.sequence payload bytes padding
    insist (wire.length == bytes + padding + 22) "TLS ciphertext length mismatch"
    sendWire session wire

inductive Received (S : Type) where
  | application (payload : S)
  | control
  | closed

def receive (session : Session S) : M (Received S) :=
  ExceptT.mk <| session.receiveGate.atomically fun _ => (show M (Received S) from do
    let closed ← guarded session fun state => do
      let before ← liftM (m := IO) (n := M) state.get
      insist (!before.policy.aborted) "TLS application session aborted"
      return before.policy.receiveClosed
    if closed then return .closed
    -- Serialize readers, but do not hold the MPC/state lock while waiting for
    -- the peer: a pending receive must not prevent sending the peer's request.
    let incoming ← liftM (m := IO) (n := M) (do
      try session.transport.receive.run catch _ => pure (.error "TLS receive I/O failed"))
    guarded session fun state => do
      let wire ← liftResult incoming
      let ticket ← reserve state TlsApplicationPolicy.reserveReceive
      let (records,pending) ← liftResult (TlsWire.records 2 wire)
      insist (records.length == 1 && pending.isEmpty && wire.length ≥ 22 && wire.length ≤ 16406 &&
        records.head!.kind == 23 && records.head!.version == 0x0303) "invalid protected incoming record"
      let live ← liftM (m := IO) (n := M) state.get
      match ← session.backend.openRecord live.keys ticket.sequence wire with
      | .application handle => return .application handle
      | .skippedControl => return .control
      | .keyUpdate request =>
          let keys ← session.backend.rotateReceive live.keys
          liftM (m := IO) (n := M) (state.set { keys, policy := TlsApplicationPolicy.receiveUpdate live.policy request })
          return .control
      | .closeNotify =>
          liftM (m := IO) (n := M) (state.set { live with policy := TlsApplicationPolicy.receiveClose live.policy })
          finishClose session state
          return .closed
      | .fatal => throw "TLS authenticated alert or record rejection").run

def close (session : Session S) : M Unit :=
  guarded session fun state => do
    let ticket ← reserve state TlsApplicationPolicy.reserveClose
    let live ← liftM (m := IO) (n := M) state.get
    let wire ← session.backend.sealControl live.keys ticket.sequence 21 [1,0]
    insist (wire.length == 24) "TLS close_notify ciphertext length mismatch"
    sendWire session wire
    finishClose session state

def abort (session : Session S) : M Unit :=
  guarded session fun state => do
    liftM (m := IO) (n := M) (state.modify fun live => { live with policy := TlsApplicationPolicy.abort live.policy })
    session.backend.abort

end TlsMpc.TlsApplication
