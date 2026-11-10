import TlsMpc.TlsClient
import TlsMpc.TlsApplication

/-! Public RPC binding for a single persistent MPC session. No private key or
share is represented in this controller process. The service owns all opaque
state. The RPC transport must agree operation, payload and pinned program
manifest across parties before performing an operation. Retire/abort require
real backend erasure; a service that only invalidates handles is insufficient.
-/
namespace TlsMpc.TlsWorker
open TlsWire TlsClient

inductive Operation where
  | begin | derive | openHandshake | authenticate | verifyFinished | finish | retire | abort
  | connect | sendRecord | receiveRecord
  | openApplication | sealApplication | sealControl | rotateSend | rotateReceive
  | pollRecord | processWebSocket | providerCatalogue | providerUpgrade | providerProduce
  | muxCatalogue | muxUpgrade | muxProduce | muxProcess | muxProduceBatch | muxResumeOutbox | muxCheckpointOutcomes
  /- Public-receive profile: only contacts and client keys are secret, so the
  contents of authenticated server records may be revealed to the controllers. -/
  | revealApplication | publicBuffer | providerProduceOpen | providerUpgradeOpen | publicRandom
  deriving Repr, BEq

structure Rpc where
  call : Operation → Bytes → M Bytes
  /-- Local public X.509/hostname/CertificateVerify validation. -/
  authenticate : String → List Bytes → Nat → Bytes → Bytes → M Bool

def emptyReply (rpc : Rpc) (operation : Operation) (input : Bytes) : M Unit := do
  let output ← rpc.call operation input
  insist output.isEmpty "unexpected worker response payload"

def handshakeKeys : HandshakeKeys Unit := ⟨(),(),(),(),(),(),()⟩
def applicationKeys : ApplicationKeys Unit := ⟨(),(),(),(),(),()⟩

def authRequest (hostname : String) (chain : List Bytes) (scheme : Nat)
    (hash signature : Bytes) (valid : Bool) : Bytes :=
  let host := hostname.toUTF8.data.toList
  uint 2 host.length ++ host ++ uint 2 chain.length ++
    chain.flatMap (fun cert => uint 3 cert.length ++ cert) ++
    uint 2 scheme ++ hash ++ uint 2 signature.length ++ signature ++
    [if valid then 1 else 0]

def backend (rpc : Rpc) : Backend Unit where
  begin := do
    let result ← rpc.call .begin []
    insist (result.length == 64) "invalid worker public key/random length"
    return ((), result.take 32, result.drop 32)
  derive _ peer hash := do
    insist (peer.length == 32 && hash.length == 32) "invalid public agreement inputs"
    emptyReply rpc .derive (peer ++ hash)
    return handshakeKeys
  openHandshake _ sequence wire := do
    insist (sequence < 2^64) "worker receive sequence exhausted"
    let output ← rpc.call .openHandshake (uint 8 sequence ++ wire)
    insist (output.length ≥ 4 && output[0]?.getD 0 == 255) "worker handshake record rejected"
    let kind := (output[1]?.getD 0).toNat
    let size := number ((output.drop 2).take 2)
    insist ((kind == 21 || kind == 22) && size ≤ output.length - 4) "invalid worker public handshake output"
    return (kind, (output.drop 4).take size)
  authenticate hostname chain scheme hash signature := do
    let host := hostname.toUTF8.data.toList
    insist (host.length < 2^16 && chain.length < 2^16 &&
      chain.all (fun cert => cert.length < 2^24) && scheme < 2^16 &&
      hash.length == 32 && signature.length < 2^16) "invalid public authentication dimensions"
    let valid ← rpc.authenticate hostname chain scheme hash signature
    -- Include the entire request and local decision in collective agreement.
    -- A disagreement must abort rather than accepting a leader's decision.
    emptyReply rpc .authenticate (authRequest hostname chain scheme hash signature valid)
    return valid
  verifyFinished _ hash message := do
    insist (hash.length == 32 && message.length == 36) "invalid Finished inputs"
    let output ← rpc.call .verifyFinished (hash ++ message)
    insist (output == [0] || output == [255]) "invalid worker acceptance byte"
    return output == [255]
  finish _ serverHash clientHash certificate := do
    insist (serverHash.length == 32 && clientHash.length == 32 &&
      (certificate.isEmpty || certificate == TlsClient.emptyCertificate)) "invalid client Finished context"
    let wire ← rpc.call .finish (serverHash ++ clientHash ++ certificate)
    let (records, pending) ← liftResult (TlsWire.records 2 wire)
    insist (records.length == 1 && pending.isEmpty &&
      records.head!.kind == 23 && records.head!.version == 0x0303) "invalid encrypted worker Finished record"
    return (applicationKeys, wire)
  retire _ _ := emptyReply rpc .retire []
  abort := emptyReply rpc .abort []

/-- Agree one public server endpoint; only the leader opens its TCP socket. -/
def connect (rpc : Rpc) (hostname : String) (port : Nat := 443) : M Unit := do
  let host := hostname.toUTF8.data.toList
  insist (!host.isEmpty && host.length ≤ 253 && 0 < port && port < 65536) "invalid public TLS endpoint"
  emptyReply rpc .connect (uint 2 host.length ++ host ++ uint 2 port)

def transport (rpc : Rpc) : Transport where
  send wire := emptyReply rpc .sendRecord wire
  receive := rpc.call .receiveRecord []

def pollRecordLoop (rpc : Rpc) (deadline : Nat) : Nat → M Bytes
  | 0 => throw "worker application receive poll limit exhausted"
  | fuel+1 => do
      insist ((← liftM (IO.monoMsNow : IO Nat)) < deadline) "worker application receive timed out"
      let wire ← rpc.call .pollRecord []
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

/-- Public identifier only. The worker owns the secret buffer and its private
length. Zero is reserved for implicit session key handles, never a payload.
Identifiers are scoped to one worker lifetime and must never be reused. -/
structure BufferHandle where
  id : Nat
  deriving BEq, Repr

def applicationHandleKeys : ApplicationKeys BufferHandle :=
  ⟨⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩⟩

/-- Only ciphertext, typed control events and opaque buffer IDs cross this
binding. Receiving does not disclose plaintext length. The service must keep
the parser output/private length in its handle table and enforce all transitions. -/
def applicationBackend (rpc : Rpc) : TlsApplication.Backend BufferHandle where
  sealApplication _ sequence payload size padding := do
    insist (sequence < 2^64 && 0 < payload.id && payload.id < 2^64 &&
      size + padding ≤ 16384) "invalid worker application seal request"
    rpc.call .sealApplication (uint 8 sequence ++ uint 8 payload.id ++ uint 2 size ++ uint 2 padding)
  sealControl _ sequence kind content := do
    insist (sequence < 2^64 &&
      ((kind == 22 && (content == [24,0,0,1,0] || content == [24,0,0,1,1])) ||
        (kind == 21 && content == [1,0]))) "invalid worker TLS control"
    rpc.call .sealControl (uint 8 sequence ++ [UInt8.ofNat kind] ++ content)
  openRecord _ sequence wire := do
    insist (sequence < 2^64 && 22 ≤ wire.length && wire.length ≤ 16406)
      "invalid worker application open request"
    let output ← rpc.call .openApplication (uint 8 sequence ++ wire)
    insist (output.length ≥ 2) "truncated worker application event"
    let event := (output[0]?.getD 255).toNat
    let request := (output[1]?.getD 255).toNat
    if event == 1 then
      insist (output.length == 10 && request == 0) "invalid worker payload handle response"
      let id := number (output.drop 2)
      insist (id != 0) "zero worker payload handle"
      return .application ⟨id⟩
    insist (output.length == 2) "worker control event contains unexpected bytes"
    match event with
    | 0 => insist (request == 0) "invalid rejection flag"; return .fatal
    | 2 => insist (request == 0) "invalid ignored-control flag"; return .skippedControl
    | 3 => insist (request ≤ 1) "invalid KeyUpdate request flag"; return .keyUpdate (request == 1)
    | 4 => insist (request == 0) "invalid close flag"; return .closeNotify
    | _ => throw "invalid worker application event" -- DEFER must remain inside worker.
  rotateSend _ := do
    emptyReply rpc .rotateSend []
    return applicationHandleKeys
  rotateReceive _ := do
    emptyReply rpc .rotateReceive []
    return applicationHandleKeys
  abort := emptyReply rpc .abort []

def applicationSession (rpc : Rpc) (handshake : TlsClient.Session Unit) : IO (TlsApplication.Session BufferHandle) :=
  TlsApplication.make (applicationBackend rpc) (applicationTransport rpc) {
    keys := applicationHandleKeys, hostname := handshake.hostname, alpn := handshake.alpn
    sendSequence := handshake.sendSequence, receiveSequence := handshake.receiveSequence
    serverCertificateVerified := handshake.serverCertificateVerified
    serverFinishedVerified := handshake.serverFinishedVerified, accepted := handshake.accepted }

end TlsMpc.TlsWorker
