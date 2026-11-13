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
  | providerSealOpen | providerRequest
  /- Contact state at rest, keyed by a u128 id. `contactKey` carries this party's
  private additive share of the contact's stored scalar after the public id;
  `exchange` sends this party's private bytes to the other party and returns
  theirs (for values that are safe to reveal, such as parity shares). -/
  | contactKey | contactOpen | contactSeal | exchange | contactEvict
  /- Notify path: one sealed-sender send to a contact id with a public text,
  and its request frame. -/
  | contactSend | contactRequest
  /- Public-receive profile: a range of an authenticated record at once. -/
  | revealRange
  /- Local-server testing: admit a contact from an export; open an
  unauthenticated chat socket (the upgrade request itself is public). -/
  | contactAdmit | publicUpgrade | accountAdmit | accountCredentials | envelopeTake | envelopeDrop
  /- A new contact's first message, from the held envelope: its public part (our prekey ids
  and the Kyber ciphertext), then the session, the text and the contact's record. -/
  | envelopeOpen | envelopeSession | contactAssign
  /- The account's own record at rest (identity key, credentials, certificate). -/
  | accountKey | accountSeal | accountOpen
  /- A contact with several devices (handshake_backend/EmpHybridWork/MULTI_DEVICE.md): the
  prekey fetch that names the contact; its response body, collected unopened; the opened
  punctuation shape; one step of one device's session establishment; a send with one
  envelope per device and its request frame; loading a stored device list. -/
  | bundleFetch | bundleTake | bundleDrop | bundleShape | bundleEstablish
  | devicesSend | devicesRequest | devicesOpen
  /- Several connections (one per Tor circuit): select the worker's connection by its public
  index; every operation that touches a connection acts on the selected one (0 by default). -/
  | useConnection
  /- Recovery (PRODUCT_TODO.md section 4). A refresh's new device list is scratch in the worker
  until the database nodes hold it: `scratchSeal` seals the scratch for storage, `scratchCommit`
  makes it the contact's state (`bundleDrop` discards it). `resetConnection` replaces the
  selected connection, after a poll reported it closed (`pollRecord` replies `[0]`), by a fresh
  one to connect and shake hands on again; the other connections are untouched. -/
  | scratchSeal | scratchCommit | resetConnection
  /- Several loaded contacts prepared for sending in one call (their per-session curve work, in
  the same field rounds). Payload: the contact ids; reply: one status byte per contact. -/
  | contactsPrepare
  /- The registration ceremony (CEREMONY.md, `TlsMpc/CeremonyKernels.lean`). `ceremonySecrets`:
  the account password and the recovery password are made in the engine from each party's own
  randomness; the reply is THIS party's XOR share of each (22 and 32 bytes), different for the
  two parties. `ceremonyRegister`: the registration request's frame, to be sealed with those
  two values inserted. Payload: payload start 2, credential slot 2, recovery slot 2, mask 4,
  the count (1) and bytes of the public tail of `NUMBER:`, the frame. Reply: handle 8. -/
  | ceremonySecrets | ceremonyRegister
  /- node_worker's own operations (REORGANIZATION_PLAN.md S8/S9): `closeConnection` (92) closes
  the selected connection's server socket (`ServerOp::Close`); `batch` (93) is one batch of the
  engine instruction set (`TlsMpc/Node/Engine.lean`: payload `encodeBatch`, reply
  `encodeReplies`), sent only by the script runner (`TlsMpc/Node/Flows/Runner.lean`). -/
  | closeConnection | batch
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

/-- A SOCKS5 proxy for the leader's TCP connection (a local Tor client; a numeric address). The
username and password choose the Tor circuit (Tor's `IsolateSOCKSAuth`). -/
structure Proxy where
  host : String
  port : Nat
  username : String
  password : String

/-- `connect`, through `proxy` when there is one: the server is asked for BY HOSTNAME, so no
node resolves it. The proxy part is in the agreed request, so both parties must have been
configured with the same proxy and credentials; only the leader opens anything. -/
def connectVia (rpc : Rpc) (hostname : String) (port : Nat) : Option Proxy → M Unit
  | none => connect rpc hostname port
  | some proxy => do
    let host := hostname.toUTF8.data.toList
    let via := proxy.host.toUTF8.data.toList
    let user := proxy.username.toUTF8.data.toList
    let pass := proxy.password.toUTF8.data.toList
    insist (!host.isEmpty && host.length ≤ 253 && 0 < port && port < 65536 && !via.isEmpty && via.length ≤ 253 &&
      0 < proxy.port && proxy.port < 65536 && 0 < user.length && user.length < 256 && 0 < pass.length && pass.length < 256)
      "invalid proxied TLS endpoint"
    emptyReply rpc .connect (uint 2 host.length ++ host ++ uint 2 port ++ uint 2 via.length ++ via ++ uint 2 proxy.port ++
      uint 1 user.length ++ user ++ uint 1 pass.length ++ pass)

/-- The same RPC, with every call made on the worker's connection `index`: the connection is
selected first whenever another one is active (`active` tracks it; all controllers select at
the same points, as every request is agreed). With one connection it never selects. -/
def onConnection (rpc : Rpc) (active : IO.Ref Nat) (index : Nat) : Rpc :=
  { rpc with call := fun operation input => do
      if (← liftM (active.get : IO Nat)) != index then
        insist (index < 64) "connection index"
        emptyReply rpc .useConnection [UInt8.ofNat index]
        liftM (active.set index : IO Unit)
      rpc.call operation input }

def transport (rpc : Rpc) : Transport where
  send wire := emptyReply rpc .sendRecord wire
  receive := rpc.call .receiveRecord []

-- The polling transports (`pollRecordLoop`, `applicationTransport`, `waitingTransport`,
-- `awaitRecord`) and `applicationSession` are in `TlsMpc/TlsWorkerPoll.lean` (stage S6): they
-- sleep and read the clock, and the controller's import closure must hold no I/O primitive
-- outside `TlsMpc/Node/Channels.lean` (its own copies are `Flow.Server.*`, `TlsMpc/Node/Flows/
-- TlsLegacy.lean`).

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

end TlsMpc.TlsWorker
