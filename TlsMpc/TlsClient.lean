import TlsMpc.TlsWire

/-! Initial TLS1.3 certificate-authenticated client handshake controller.
All private values have the opaque backend type S. The only public releases
are ClientHello metadata, gated server handshake/alert contents, authentication
decisions and encrypted output records. The backend MUST implement the supplied
Lean circuits, including all-zero ECDH rejection and the handshake-only release
gate. Every party validates public authentication metadata independently and
agrees the same transcript before releasing application traffic.

This initial full-handshake profile deliberately offers no resumption, 0-RTT,
client credential, certificate compression or post-handshake authentication.
An initial CertificateRequest is answered with an empty certificate list.
-/
namespace TlsMpc.TlsClient
open TlsWire
abbrev M := ExceptT String IO

structure HandshakeKeys (S : Type) where
  clientTraffic : S
  serverTraffic : S
  mainSecret : S
  clientKey : S
  clientIV : S
  serverKey : S
  serverIV : S

structure ApplicationKeys (S : Type) where
  clientTraffic : S
  serverTraffic : S
  clientKey : S
  clientIV : S
  serverKey : S
  serverIV : S

structure Backend (S : Type) where
  /-- Joint private scalar, public X25519 share, public fresh ClientHello random. -/
  begin : M (S × Bytes × Bytes)
  /-- Reject all-zero X25519; derive keys using the exact hello transcript hash. -/
  derive : S → Bytes → Bytes → M (HandshakeKeys S)
  /-- Apply TlsPublicHandshake's type gate BEFORE opening to this controller. -/
  openHandshake : HandshakeKeys S → Nat → Bytes → M (Nat × Bytes)
  /-- Chain + hostname + offered-scheme CertificateVerify, using this exact
  transcript hash. All parties must agree success for the same bound request. -/
  authenticate : String → List Bytes → Nat → Bytes → Bytes → M Bool
  verifyFinished : HandshakeKeys S → Bytes → Bytes → M Bool
  /-- Derive app keys from server-Finished hash; compute client Finished using
  the client-context hash, prepend optional empty Certificate, seal at seq0. -/
  finish : HandshakeKeys S → Bytes → Bytes → Bytes → M (ApplicationKeys S × Bytes)
  /-- Drop/erase ephemeral scalar and handshake key handles on success/failure. -/
  retire : S → Option (HandshakeKeys S) → M Unit
  /-- Idempotently erase ALL session handles, including partially allocated
  application keys. Must also work if begin/derive/finish fails partway. -/
  abort : M Unit

structure Transport where
  send : Bytes → M Unit
  /-- Return exactly one record. The native I/O layer handles arbitrary TCP
  fragmentation/coalescing and enforces the 16640-byte record-body bound. -/
  receive : M Bytes

def liftResult (value : Except String α) : M α := ExceptT.mk (pure value)
def insist (ok : Bool) (error : String) : M Unit := unless ok do throw error

/-- Catch both protocol errors and underlying I/O exceptions. Cleanup failures
are reported explicitly; returning an error never asserts successful erasure. -/
def cleanupOnError (action : M α) (cleanup : M Unit) : M α := ExceptT.mk do
  let outcome ← try action.run catch _ => pure (.error "TLS I/O failed")
  match outcome with
  | .ok value => return .ok value
  | .error message =>
      let erased ← try cleanup.run catch _ => pure (.error "cleanup I/O failed")
      return .error (match erased with
        | .ok _ => message
        | .error _ => message ++ "; backend erasure failed")

def receiveRecord (transport : Transport) : M Record := do
  let wire ← transport.receive
  let (records, pending) ← liftResult (TlsWire.records 2 wire)
  insist (records.length == 1 && pending.isEmpty) "transport did not return exactly one TLS record"
  let record := records.head!
  insist (record.version == 0x0303) "invalid server record version"
  return record

def validCCS (record : Record) : Bool := record.kind == 20 && record.body == [1]

/-- Read a fragmented plaintext ServerHello while permitting valid middlebox
CCS records. A key change cannot occur in the middle of a record. -/
def receiveHello (transport : Transport) (cfg : Config) : Nat → Bytes → M Message
  | 0, _ => throw "ServerHello record limit exceeded"
  | fuel + 1, pending => do
      let record ← receiveRecord transport
      if validCCS record then
        insist pending.isEmpty "CCS interleaved with fragmented ServerHello"
        receiveHello transport cfg fuel pending
      else
        insist (record.kind == 22 && record.body.length ≤ 16384 && !record.body.isEmpty) "expected plaintext ServerHello"
        let data := pending ++ record.body
        insist (data.length ≤ cfg.maxHandshakeBytes + 4) "ServerHello buffer limit exceeded"
        let (messages, rest) ← liftResult (TlsWire.messages cfg.maxHandshakeBytes 2 data)
        if messages.isEmpty then receiveHello transport cfg fuel rest else do
          insist (messages.length == 1 && rest.isEmpty) "ServerHello must end at record boundary"
          let message := messages.head!
          insist (message.kind == 2) "expected ServerHello handshake type"
          return message

inductive Phase where
  | extensions | certificateOrRequest | certificate | certificateVerify | finished | complete
  deriving DecidableEq, BEq, Repr

structure Flight where
  phase : Phase := .extensions
  transcript : Bytes
  chain : List Bytes := []
  requestClientCertificate : Bool := false
  certificateVerified : Bool := false
  finishedVerified : Bool := false
  alpn : Option String := none

def emptyCertificate : Bytes := handshake 11 (octets [0,0,0,0])

def processMessage (backend : Backend S) (keys : HandshakeKeys S) (cfg : Config)
    (state : Flight) (message : Message) : M Flight := do
  let appended := state.transcript ++ message.bytes
  insist (appended.length ≤ cfg.maxHandshakeBytes) "handshake transcript limit exceeded"
  match state.phase with
  | .extensions =>
      insist (message.kind == 8) "expected EncryptedExtensions"
      let alpn ← liftResult (encryptedExtensions cfg message.body)
      return { state with phase := .certificateOrRequest, transcript := appended, alpn }
  | .certificateOrRequest =>
      if message.kind == 13 then
        liftResult (certificateRequest message.body)
        return { state with phase := .certificate, transcript := appended, requestClientCertificate := true }
      else
        insist (message.kind == 11) "expected Certificate or CertificateRequest"
        let chain ← liftResult (certificates message.body)
        return { state with phase := .certificateVerify, transcript := appended, chain }
  | .certificate =>
      insist (message.kind == 11) "expected server Certificate"
      let chain ← liftResult (certificates message.body)
      return { state with phase := .certificateVerify, transcript := appended, chain }
  | .certificateVerify =>
      insist (message.kind == 15) "expected CertificateVerify"
      let (scheme, signature) ← liftResult (certificateVerify message.body)
      insist (cfg.profile == .legacy || libsignalSignatureSchemes.contains scheme) "unoffered CertificateVerify scheme"
      let valid ← backend.authenticate cfg.hostname state.chain scheme (hash state.transcript) signature
      insist valid "server certificate or CertificateVerify validation failed"
      return { state with phase := .finished, transcript := appended, certificateVerified := true }
  | .finished =>
      insist (state.certificateVerified && message.kind == 20 && message.body.length == 32) "expected authenticated server Finished"
      let valid ← backend.verifyFinished keys (hash state.transcript) message.bytes
      insist valid "server Finished validation failed"
      return { state with phase := .complete, transcript := appended, finishedVerified := true }
  | .complete => throw "handshake message after server Finished in old-key record"

def processMessages (backend : Backend S) (keys : HandshakeKeys S) (cfg : Config) :
    Flight → List Message → M Flight
  | state, [] => pure state
  | state, message :: rest => do
      let state ← processMessage backend keys cfg state message
      processMessages backend keys cfg state rest

def receiveFlight (backend : Backend S) (transport : Transport) (keys : HandshakeKeys S) (cfg : Config) :
    Nat → Nat → Flight → Bytes → M Flight
  | 0, _, _, _ => throw "server handshake record limit exceeded"
  | fuel + 1, sequence, state, pending => do
      let record ← receiveRecord transport
      if validCCS record then
        insist pending.isEmpty "CCS interleaved with fragmented handshake"
        receiveFlight backend transport keys cfg fuel sequence state pending
      else
        insist (record.kind == 23 && sequence < 2 ^ 64) "expected protected handshake record"
        let (kind, content) ← backend.openHandshake keys sequence record.bytes
        insist (kind == 22 && !content.isEmpty) "TLS handshake alert, invalid tag, or disallowed content type"
        let data := pending ++ content
        insist (data.length ≤ cfg.maxHandshakeBytes + 4) "handshake buffer limit exceeded"
        let (messages, rest) ← liftResult (TlsWire.messages cfg.maxHandshakeBytes cfg.maxHandshakeBytes data)
        let state ← processMessages backend keys cfg state messages
        if state.phase == .complete then
          insist rest.isEmpty "server Finished not aligned to record boundary"
          return state
        else receiveFlight backend transport keys cfg fuel (sequence + 1) state rest

structure Session (S : Type) where
  keys : ApplicationKeys S
  hostname : String
  alpn : Option String
  sendSequence : Nat := 0
  receiveSequence : Nat := 0
  serverCertificateVerified : Bool
  serverFinishedVerified : Bool
  accepted : serverCertificateVerified = true ∧ serverFinishedVerified = true

def runWithScalar (backend : Backend S) (transport : Transport) (cfg : Config)
    (scalar : S) (share random : Bytes) : M (Session S) := do
  -- `libsignal` profile: a 32-byte legacy session id as BoringSSL sends (middlebox
  -- compatibility), and the first record's version TLS 1.0 (BoringSSL's `tls_record_version`
  -- before the version is known). The client random and the session id are two hashes of the
  -- joint random value, so neither is a public function of the other.
  let libsignal := cfg.profile == .libsignal
  let sessionId := if libsignal then TlsWire.hash (random ++ octets [2]) else []
  let random := if libsignal then TlsWire.hash (random ++ octets [1]) else random
  let firstHello ← liftResult (clientHello cfg random share none cfg.initialKeyShare sessionId)
  transport.send (if libsignal then octets [22, 3, 1] ++ vector 2 firstHello else record 22 firstHello)
  let firstServer ← receiveHello transport cfg cfg.maxRecords []
  let hello ← liftResult (serverHello firstServer.body sessionId)
  let (hello, transcript) ← if hello.retry then do
      insist (!hello.requestedKey || !cfg.initialKeyShare) "retry requested an already offered key share"
      insist (cfg.initialKeyShare || hello.requestedKey) "retry did not request the missing key share"
      let secondHello ← liftResult (clientHello cfg random share hello.cookie true sessionId)
      transport.send (record 22 secondHello)
      let secondServer ← receiveHello transport cfg cfg.maxRecords []
      let second ← liftResult (serverHello secondServer.body sessionId)
      insist (!second.retry) "second HelloRetryRequest"
      pure (second, handshake 254 (hash firstHello) ++ firstServer.bytes ++ secondHello ++ secondServer.bytes)
    else do
      insist cfg.initialKeyShare "server selected a key share that was not offered"
      pure (hello, firstHello ++ firstServer.bytes)
  let keys ← backend.derive scalar hello.share (hash transcript)
  try
    let flight ← receiveFlight backend transport keys cfg cfg.maxRecords 0 { transcript } []
    if evidence : flight.certificateVerified = true ∧ flight.finishedVerified = true then
      let cert := if flight.requestClientCertificate then emptyCertificate else []
      let (application, finishedRecord) ← backend.finish keys (hash flight.transcript)
        (hash (flight.transcript ++ cert)) cert
      transport.send finishedRecord
      backend.retire scalar (some keys)
      return {
        keys := application
        hostname := cfg.hostname
        alpn := flight.alpn
        serverCertificateVerified := flight.certificateVerified
        serverFinishedVerified := flight.finishedVerified
        accepted := evidence }
    else throw "handshake authentication evidence missing"
  catch error =>
    throw error

def run (backend : Backend S) (transport : Transport) (cfg : Config) : M (Session S) :=
  cleanupOnError (do
    insist cfg.valid "invalid TLS client profile"
    let (scalar, share, random) ← backend.begin
    runWithScalar backend transport cfg scalar share random) backend.abort

theorem accepted_session_authenticated (session : Session S) :
    session.serverCertificateVerified = true ∧ session.serverFinishedVerified = true := session.accepted

end TlsMpc.TlsClient
