import TlsMpc.TlsApplication
import TlsMpc.Node.Channels
import TlsMpc.Node.Flows.Legacy

/-!
# Flows `Server` and `Tls`, legacy implementations (worker ops 1-17, 30, 43, 90, 91)

Plan section 6.2: ops 1-8 `Tls.handshake` (the `TlsClient.Backend` instance `legacyBackend`),
12-16 `Tls.application` (the `TlsApplication.Backend` instance `legacyApplicationBackend`), 30
`Tls.publicBuffer`, 43 `Tls.revealRange`; 9, 10, 11, 17, 90, 91 `Server.*`. The server operations
move to Rust in S8, the TLS ones to Lean scripts in S12.

Moved here from `TlsMpc/TlsWorker.lean` (`backend`, `applicationBackend`, `transport`,
`waitingTransport`, `pollRecordLoop`, `awaitRecord`, `connectVia`): the same operations and
checks. The poll deadlines and sleeps take the clock and sleep of `Channels.Real` (plan 3.2), so
this file has no I/O primitive. `TlsWorker.lean` keeps its copies for the fixtures, which do not
import `TlsMpc/Node`.

The TLS openings pass through `Reveal.*` and are handed to `TlsClient` / `TlsApplication` as the
public bytes their backends take (their types are not `Opened` until S12).
-/

namespace TlsMpc.Node.Flow
open TlsMpc.TlsWire TlsMpc.TlsClient

namespace Server

/-- **Agree one public server endpoint; only the leader opens its TCP socket** (op 9). Through
`proxy` when there is one (a local Tor client, numeric address): the server is asked for BY
HOSTNAME, so no node resolves it; the username and password choose the Tor circuit. The proxy part
is in the agreed request, so both parties must have the same proxy and credentials. -/
def connect (w : Worker) (hostname : String) (port : Nat) : Option TlsWorker.Proxy → M Unit
  | none => do
    let host := hostname.toUTF8.data.toList
    insist (!host.isEmpty && host.length ≤ 253 && 0 < port && port < 65536) "invalid public TLS endpoint"
    Legacy.empty w .connect (uint 2 host.length ++ host ++ uint 2 port)
  | some proxy => do
    let host := hostname.toUTF8.data.toList
    let via := proxy.host.toUTF8.data.toList
    let user := proxy.username.toUTF8.data.toList
    let pass := proxy.password.toUTF8.data.toList
    insist (!host.isEmpty && host.length ≤ 253 && 0 < port && port < 65536 && !via.isEmpty && via.length ≤ 253 &&
      0 < proxy.port && proxy.port < 65536 && 0 < user.length && user.length < 256 && 0 < pass.length && pass.length < 256)
      "invalid proxied TLS endpoint"
    Legacy.empty w .connect (uint 2 host.length ++ host ++ uint 2 port ++ uint 2 via.length ++ via ++ uint 2 proxy.port ++
      uint 1 user.length ++ user ++ uint 1 pass.length ++ pass)

/-- **One poll of the selected connection** (op 17): a record, nothing yet, or closed (`[0]`). -/
def poll (w : Worker) : M Polled := do
  let wire ← Legacy.call w .pollRecord []
  if wire == [0] then return .closed
  if wire.isEmpty then return .nothing
  return .record wire

/-- **Replace the selected connection** (op 91) after a poll reported it closed, by a fresh one to
connect and shake hands on again; the other connections are untouched. With `tls` selected (J22)
the scripts own the connection's TLS state: op 91 with payload `[1]` replaces only the socket (the
legacy library's connection never left its fresh phase, so there is nothing of it to reset), and the
selection's `serverReset` gives the connection a fresh script TLS state. -/
def reset (w : Worker) : M Unit := do
  if let some f := w.overrides.serverReset then
    Legacy.empty w .resetConnection [1]
    return ← f w.connection
  Legacy.empty w .resetConnection []

/-- The handshake's transport: records sent (op 10) and received (op 11) by the leader's socket. -/
def handshakeTransport (w : Worker) : Transport where
  send wire := Legacy.empty w .sendRecord wire
  receive := Legacy.call w .receiveRecord []

/-- Poll until a record arrives, the deadline (monotonic ms) passes or the fuel runs out. -/
def pollRecordLoop (w : Worker) (deadline : Nat) : Nat → M Bytes
  | 0 => throw "worker application receive poll limit exhausted"
  | fuel+1 => do
      insist ((← liftM Channels.Real.monotonic) < deadline) "worker application receive timed out"
      let wire ← Legacy.call w .pollRecord []
      -- `[0]`: the worker reports that the server or the proxy closed this connection (no record
      -- is one byte). A caller that can replace the connection polls itself and never gets here.
      insist (wire != [0]) "the server or the proxy closed the connection"
      if !wire.isEmpty then return wire
      liftM (Channels.Real.sleep 10)
      pollRecordLoop w deadline fuel

/-- For a long-lived connection: a record kept by `awaitRecord` (or put in `kept` by the caller)
is taken first; otherwise poll for up to 30 seconds. Every party sees the same poll results. -/
def waitingTransport (w : Worker) (kept : IO.Ref (Option Bytes)) : Transport where
  send wire := Legacy.empty w .sendRecord wire
  receive := do
    match ← liftM (kept.get : IO (Option Bytes)) with
    | some wire => liftM (kept.set none : IO Unit); return wire
    | none =>
      let now ← liftM Channels.Real.monotonic
      pollRecordLoop w (now+30000) 3000

/-- **Wait a bounded number of polls for the next record** and keep it for the transport's next
`receive`. `false`: nothing arrived; every party sees that at the same point and can send a
keepalive in step. -/
def awaitRecord (w : Worker) (kept : IO.Ref (Option Bytes)) (interval : Nat) : Nat → M Bool
  | 0 => return false
  | polls+1 => do
      if (← liftM (kept.get : IO (Option Bytes))).isSome then return true
      let wire ← Legacy.call w .pollRecord []
      insist (wire != [0]) "the server or the proxy closed the connection"
      if !wire.isEmpty then
        liftM (kept.set (some wire) : IO Unit)
        return true
      liftM (Channels.Real.sleep interval)
      awaitRecord w kept interval polls

end Server

namespace Tls

private def handshakeKeys : HandshakeKeys Unit := ⟨(),(),(),(),(),(),()⟩
private def applicationKeys : ApplicationKeys Unit := ⟨(),(),(),(),(),()⟩
private def applicationHandleKeys : ApplicationKeys TlsWorker.BufferHandle := ⟨⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩⟩

/-- **The handshake on the engines** (ops 1-8): `TlsClient`'s backend. Openings:
`Reveal.handshakeShare` (op 1), `handshakeRecord` (3), `finishedAccepted` (5), `clientFinished` (6).
The certificate check is local (`Rpc.authenticate`) and its request and decision are agreed
(op 4). -/
def legacyBackend (w : Worker) : Backend Unit where
  begin := do
    let result ← Legacy.call w .begin []
    insist (result.length == 64) "invalid worker public key/random length"
    let opened := Reveal.handshakeShare (result.take 32) (result.drop 32)
    return ((), opened.val.1, opened.val.2)
  derive _ peer hash := do
    insist (peer.length == 32 && hash.length == 32) "invalid public agreement inputs"
    Legacy.empty w .derive (peer ++ hash)
    return handshakeKeys
  openHandshake _ sequence wire := do
    insist (sequence < 2^64) "worker receive sequence exhausted"
    let output ← Legacy.call w .openHandshake (uint 8 sequence ++ wire)
    insist (output.length ≥ 4 && output[0]?.getD 0 == 255) "worker handshake record rejected"
    let kind := (output[1]?.getD 0).toNat
    let size := number ((output.drop 2).take 2)
    insist ((kind == 21 || kind == 22) && size ≤ output.length - 4) "invalid worker public handshake output"
    return (Reveal.handshakeRecord kind ((output.drop 4).take size)).val
  authenticate hostname chain scheme hash signature := do
    let host := hostname.toUTF8.data.toList
    insist (host.length < 2^16 && chain.length < 2^16 &&
      chain.all (fun cert => cert.length < 2^24) && scheme < 2^16 &&
      hash.length == 32 && signature.length < 2^16) "invalid public authentication dimensions"
    let valid ← w.pipe.authenticate hostname chain scheme hash signature
    -- Include the entire request and local decision in collective agreement.
    -- A disagreement must abort rather than accepting a leader's decision.
    Legacy.empty w .authenticate (TlsWorker.authRequest hostname chain scheme hash signature valid)
    return valid
  verifyFinished _ hash message := do
    insist (hash.length == 32 && message.length == 36) "invalid Finished inputs"
    let output ← Legacy.call w .verifyFinished (hash ++ message)
    insist (output == [0] || output == [255]) "invalid worker acceptance byte"
    return (Reveal.finishedAccepted (output == [255])).val
  finish _ serverHash clientHash certificate := do
    insist (serverHash.length == 32 && clientHash.length == 32 &&
      (certificate.isEmpty || certificate == TlsClient.emptyCertificate)) "invalid client Finished context"
    let wire ← Legacy.call w .finish (serverHash ++ clientHash ++ certificate)
    let (records, pending) ← liftResult (TlsWire.records 2 wire)
    insist (records.length == 1 && pending.isEmpty &&
      records.head!.kind == 23 && records.head!.version == 0x0303) "invalid encrypted worker Finished record"
    return (applicationKeys, (Reveal.clientFinished wire).val)
  retire _ _ := Legacy.empty w .retire []
  abort := Legacy.empty w .abort []

/-- **The application records on the engines** (ops 12-16): `TlsApplication`'s backend. Only
ciphertext, typed control events and opaque buffer handles cross it; receiving does not disclose
plaintext length. Openings: `Reveal.recordEvent` (op 12), `Reveal.sealedRecord` (13, 14). -/
def legacyApplicationBackend (w : Worker) : TlsApplication.Backend TlsWorker.BufferHandle where
  sealApplication _ sequence payload size padding := do
    insist (sequence < 2^64 && 0 < payload.id && payload.id < 2^64 &&
      size + padding ≤ 16384) "invalid worker application seal request"
    let wire ← Legacy.call w .sealApplication (uint 8 sequence ++ uint 8 payload.id ++ uint 2 size ++ uint 2 padding)
    return (Reveal.sealedRecord wire).val
  sealControl _ sequence kind content := do
    insist (sequence < 2^64 &&
      ((kind == 22 && (content == [24,0,0,1,0] || content == [24,0,0,1,1])) ||
        (kind == 21 && content == [1,0]))) "invalid worker TLS control"
    let wire ← Legacy.call w .sealControl (uint 8 sequence ++ [UInt8.ofNat kind] ++ content)
    return (Reveal.sealedRecord wire).val
  openRecord _ sequence wire := do
    insist (sequence < 2^64 && 22 ≤ wire.length && wire.length ≤ 16406)
      "invalid worker application open request"
    let output ← Legacy.call w .openApplication (uint 8 sequence ++ wire)
    insist (output.length ≥ 2) "truncated worker application event"
    let event := (output[0]?.getD 255).toNat
    let request := (output[1]?.getD 255).toNat
    if event == 1 then
      insist (output.length == 10 && request == 0) "invalid worker payload handle response"
      let id := number (output.drop 2)
      insist (id != 0) "zero worker payload handle"
      return (Reveal.recordEvent (.application ⟨id⟩)).val
    insist (output.length == 2) "worker control event contains unexpected bytes"
    match event with
    | 0 => insist (request == 0) "invalid rejection flag"; return (Reveal.recordEvent .fatal).val
    | 2 => insist (request == 0) "invalid ignored-control flag"; return (Reveal.recordEvent .skippedControl).val
    | 3 => insist (request ≤ 1) "invalid KeyUpdate request flag"; return (Reveal.recordEvent (.keyUpdate (request == 1))).val
    | 4 => insist (request == 0) "invalid close flag"; return (Reveal.recordEvent .closeNotify).val
    | _ => throw "invalid worker application event" -- DEFER must remain inside worker.
  rotateSend _ := do
    Legacy.empty w .rotateSend []
    return applicationHandleKeys
  rotateReceive _ := do
    Legacy.empty w .rotateReceive []
    return applicationHandleKeys
  abort := Legacy.empty w .abort []

/-- A selected script handshake backend, each operation recorded under its legacy code
(`Legacy.note`: the final report counts the operations performed, however they ran). -/
def notedBackend (w : Worker) (b : Backend Unit) : Backend Unit where
  begin := do Legacy.note w 1; b.begin
  derive k peer hash := do Legacy.note w 2; b.derive k peer hash
  openHandshake k sequence wire := do Legacy.note w 3; b.openHandshake k sequence wire
  authenticate hostname chain scheme hash signature := do
    Legacy.note w 4
    b.authenticate hostname chain scheme hash signature
  verifyFinished k hash message := do Legacy.note w 5; b.verifyFinished k hash message
  finish k serverHash clientHash certificate := do Legacy.note w 6; b.finish k serverHash clientHash certificate
  retire k a := do Legacy.note w 7; b.retire k a
  abort := b.abort

/-- A selected script record backend, each operation recorded under its legacy code. -/
def notedApplicationBackend (w : Worker) (b : TlsApplication.Backend TlsWorker.BufferHandle) :
    TlsApplication.Backend TlsWorker.BufferHandle where
  sealApplication keys sequence payload size padding := do
    Legacy.note w 13
    b.sealApplication keys sequence payload size padding
  sealControl keys sequence kind content := do Legacy.note w 14; b.sealControl keys sequence kind content
  openRecord keys sequence wire := do Legacy.note w 12; b.openRecord keys sequence wire
  rotateSend keys := do Legacy.note w 15; b.rotateSend keys
  rotateReceive keys := do Legacy.note w 16; b.rotateReceive keys
  abort := b.abort

/-- **A TLS session with the server** on the selected connection (ops 1-11): the handshake on the
engines, records through the leader's socket. -/
def handshake (w : Worker) (config : TlsWire.Config) : M (TlsClient.Session Unit) :=
  TlsClient.run ((w.overrides.tlsBackend.map fun f => notedBackend w (f w.connection)).getD (legacyBackend w))
    (Server.handshakeTransport w) config

/-- **The application session after `handshake`** (ops 12-17), records received through
`Server.waitingTransport` with `kept` (the slot `Server.awaitRecord` and the session loops fill). -/
def application (w : Worker) (handshake : TlsClient.Session Unit) (kept : IO.Ref (Option Bytes)) :
    IO (TlsApplication.Session TlsWorker.BufferHandle) :=
  TlsApplication.make ((w.overrides.tlsApplicationBackend.map fun f => notedApplicationBackend w (f w.connection)).getD
      (legacyApplicationBackend w))
      (Server.waitingTransport w kept) {
    keys := applicationHandleKeys, hostname := handshake.hostname, alpn := handshake.alpn
    sendSequence := handshake.sendSequence, receiveSequence := handshake.receiveSequence
    serverCertificateVerified := handshake.serverCertificateVerified
    serverFinishedVerified := handshake.serverFinishedVerified, accepted := handshake.accepted }

/-- **Public bytes into the engines, to be sealed and sent** (op 30): a WebSocket frame or request
built here in the clear. The reply is the payload's buffer handle. -/
def publicBuffer (w : Worker) (bytes : Bytes) : M TlsWorker.BufferHandle := do
  if let some f := w.overrides.tlsPublicBuffer then
    Legacy.note w 30
    return ← f w.connection bytes
  Legacy.handle (← Legacy.call w .publicBuffer bytes) "invalid public buffer handle"

/-- **The length of an authenticated record** (op 43 at an offset past any record): no byte. -/
def recordLength (w : Worker) (handle : Nat) : M (Opened .serverBytes (Nat × Bytes)) := do
  if let some f := w.overrides.tlsRecordLength then
    Legacy.note w 43
    return ← f w.connection handle
  let probe ← Legacy.call w .revealRange (uint 8 handle ++ uint 2 65535 ++ uint 2 1)
  insist (probe.length == 2) "invalid reveal reply"
  pure (Reveal.serverBytes (number probe) [])

/-- **Reveal `count` bytes of an authenticated record from `offset`** (op 43): the record's length
and the bytes (none past the length). The caller keeps to T1's budget (`PublicReceive.mayReveal`,
`PublicReceive.budget`). -/
def revealRange (w : Worker) (handle offset count : Nat) : M (Opened .serverBytes (Nat × Bytes)) := do
  if let some f := w.overrides.tlsRevealRange then
    Legacy.note w 43
    return ← f w.connection handle offset count
  let out ← Legacy.call w .revealRange (uint 8 handle ++ uint 2 offset ++ uint 2 count)
  insist (out.length ≥ 2 && out.length ≤ 2 + count) "invalid reveal reply"
  pure (Reveal.serverBytes (number (out.take 2)) (out.drop 2))

/-- **Erase the session's engine state after a failed session** (op 8), not recorded among the
operations used. -/
def abortWorker (w : Worker) : M Unit := TlsWorker.emptyReply w.pipe .abort []

end Tls
end TlsMpc.Node.Flow
