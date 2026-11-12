import TlsMpc.TlsWorker

/-!
Polling transports over the worker pipe, for the fixtures (`session_application_fixture`,
`provider_controller_fixture`). Moved out of `TlsMpc/TlsWorker.lean` in stage S6 of
REORGANIZATION_PLAN.md: these are the poll deadlines and sleeps (I/O primitives), and the
controller's import closure must not contain them. The controller's copies are in
`TlsMpc/Node/Flows/TlsLegacy.lean` (`Flow.Server.waitingTransport`, `Flow.Server.awaitRecord`),
taking the clock and sleep of `TlsMpc/Node/Channels.lean`. Not imported by the controller.
-/
namespace TlsMpc.TlsWorker
open TlsWire TlsClient

def pollRecordLoop (rpc : Rpc) (deadline : Nat) : Nat → M Bytes
  | 0 => throw "worker application receive poll limit exhausted"
  | fuel+1 => do
      insist ((← liftM (IO.monoMsNow : IO Nat)) < deadline) "worker application receive timed out"
      let wire ← rpc.call .pollRecord []
      -- `[0]`: the worker reports that the server or the proxy closed this connection (no record
      -- is one byte). A caller that can replace the connection polls itself and never gets here.
      insist (wire != [0]) "the server or the proxy closed the connection"
      if !wire.isEmpty then return wire
      liftM (IO.sleep 10)
      pollRecordLoop rpc deadline fuel

/-- Poll exchanges release the single RPC pipe between empty replies, allowing
a concurrent send to proceed. All parties still need an agreed request order. -/
def applicationTransport (rpc : Rpc) : Transport where
  send wire := emptyReply rpc .sendRecord wire
  receive := do
    let now ← liftM (IO.monoMsNow : IO Nat)
    pollRecordLoop rpc (now+30000) 3000

/-- For a long-lived connection: `awaitRecord` waits a bounded number of polls
for the next record and keeps it for the following `receive`. Every party sees
the same poll results, so all of them see "nothing arrived" at the same point
and can then send a keepalive in step. -/
def waitingTransport (rpc : Rpc) (kept : IO.Ref (Option Bytes)) : Transport where
  send wire := emptyReply rpc .sendRecord wire
  receive := do
    match ← liftM (kept.get : IO (Option Bytes)) with
    | some wire => liftM (kept.set none : IO Unit); return wire
    | none =>
      let now ← liftM (IO.monoMsNow : IO Nat)
      pollRecordLoop rpc (now+30000) 3000

def awaitRecord (rpc : Rpc) (kept : IO.Ref (Option Bytes)) (interval : Nat) : Nat → M Bool
  | 0 => return false
  | polls+1 => do
      if (← liftM (kept.get : IO (Option Bytes))).isSome then return true
      let wire ← rpc.call .pollRecord []
      insist (wire != [0]) "the server or the proxy closed the connection"
      if !wire.isEmpty then
        liftM (kept.set (some wire) : IO Unit)
        return true
      liftM (IO.sleep interval.toUInt32)
      awaitRecord rpc kept interval polls

def applicationSession (rpc : Rpc) (handshake : TlsClient.Session Unit)
    (transport : Option Transport := none) : IO (TlsApplication.Session BufferHandle) :=
  TlsApplication.make (applicationBackend rpc) (transport.getD (applicationTransport rpc)) {
    keys := applicationHandleKeys, hostname := handshake.hostname, alpn := handshake.alpn
    sendSequence := handshake.sendSequence, receiveSequence := handshake.receiveSequence
    serverCertificateVerified := handshake.serverCertificateVerified
    serverFinishedVerified := handshake.serverFinishedVerified, accepted := handshake.accepted }

end TlsMpc.TlsWorker
