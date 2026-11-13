import TlsMpc.TlsWorker
import TlsMpc.Node.Types

/-!
# The reveal list (REORGANIZATION_PLAN.md section 4.3, stage S6)

**Everything a flow may open to this node or to the peer.** A value of type `Opened r α` exists
only if a function of this file made it: `Opened`'s constructor is private here. Each kind of
opening is a constructor of `RevealKind` (`TlsMpc/Node/Types.lean`, with its fixed code).

Until a flow moves to a Lean script (stages S9-S16), the functions below are **legacy wrappers**:
they turn a worker operation's reply into `Opened`, and are called only by the legacy flow
implementations (`TlsMpc/Node/Flows/*Legacy.lean`; `scripts/lint_node.py` check `flow-calls`).
Later they become the script openings; the list itself does not change.

| Kind (code) | Flow that produces it (worker op) | What it reveals | Bounding theorem (`TlsMpc/Security.lean`) |
|---|---|---|---|
| `handshakeShare` (1) | `Flow.Tls.handshake` (op 1) | the client's X25519 key share and hello random, both public in the ClientHello | none yet (SECURITY_MAP D) |
| `handshakeRecord` (2) | `Flow.Tls.handshake` (op 3) | a server handshake record's type and plaintext; only types 21 and 22 | `publicHandshake_gate_value`, `publicHandshake_application_not_released`, `tlsOpenHandshake_spec`, `tlsOpenHandshake_application_zero` |
| `finishedAccepted` (3) | `Flow.Tls.handshake` (op 5) | whether the server Finished verified (one bit) | `tlsVerifyFinished_spec` |
| `clientFinished` (4) | `Flow.Tls.handshake` (op 6) | the client Finished record, sealed (sent to the server) | `tlsFinish_spec` |
| `recordKindBit` (5) | declared | | `typedOpen_handshakeBit_cases` |
| `recordEvent` (6) | `Flow.Tls.application` (op 12) | an application record's event: a payload handle, a control event, or fatal; never content | `typedOpen_gated`, `tlsOpenApplication_event_private`, `postHandshake_reject_unauthenticated`, `postHandshake_reject_failed` |
| `sealedRecord` (7) | `Flow.Tls.application` (ops 13, 14) | a sealed record (header, ciphertext, tag), sent to the server | `tlsRecord_sealCore_compiled`, `tlsSealCtr_spec`, `gcmTag_spec` |
| `serverBytes` (8) | `Flow.Tls.recordLength`, `Flow.Tls.revealRange` (op 43) | bytes of an authenticated server record, and its length; the caller keeps to T1's budget (`PublicReceive.mayReveal`, `budget`) | `tlsRevealMasked_value`; T1: `receivePolicy_request_body_unrevealed`, `receivePolicy_response_body_unrevealed` (section 4f; T1 for all streams open, section 8) |
| `ghashMaskedPower` (9) | declared (S12) | | `ghash_share_hides` |
| `jointRandom` (20) | `Flow.Random.joint` (op 33) | 32 bytes of joint randomness (masks, nonces, request masks) | the S9 script: `prand_a_honest`, `prand_b_ideal`; the legacy op: none (SECURITY_MAP D) |
| `parity` (21) | declared: `Channels.exchange` (`PeerMsg.parity`) | the database read's parity shares (trusted, designed public) | none (SECURITY_MAP D) |
| `upgradeNonce` (22) | `Flow.Upgrade.anonymous` (op 45) | the unauthenticated upgrade's nonce (joint randomness) and its RFC 6455 accept value | the S9 script: `upgrade_honest`; `wsAccept_accept_spec` |
| `upgradeAccept` (23) | `Flow.Upgrade.authenticated` (op 32) | the authenticated upgrade's expected accept value (of a joint nonce); the request stays in the engines | `signalUpgradeShared_spec`, `signalUpgrade_spec` |
| `blobAccepted` (30) | `Flow.Contacts.load`, `Flow.Contacts.loadDevices` (ops 37, 63) | whether a stored blob opened under the contact's key (one bit) | `contactOpen_accepted_iff`, `contactOpen_rejected` |
| `sealedBlob` (31) | `Flow.Contacts.seal`, `Flow.Account.seal`, `Flow.Refresh.scratchSeal` (ops 38, 54, 64) | a sealed state: check value and ciphertext (stored on the database nodes) | `contactSeal_spec`, `contact_round_trip` |
| `assignStatus` (32) | `Flow.Contacts.assign` (op 52) | whether a provisional contact took its signup token's id (one bit) | none yet (SECURITY_MAP D) |
| `counterWidths` (40) | declared (inside op 41) | | `signalWidths_spec`, `signalWidths_value` |
| `sealedEnvelope` (41) | `Flow.Send.seal`, `Flow.Send.sealDevices` (ops 41, 61) | refused, or the timestamp and the sealed-sender envelope(s) (sent to the server) | `signalSealBuilt_spec`, `signalSeal_value`, `sealValue_accepted`, `chainSend_reject_preserves_state` |
| `ephemeralPublic` (42) | declared (inside ops 41, 61) | | none yet |
| `prepareStatus` (43) | `Flow.Curve.prepareContacts` (op 66) | per contact, one status byte: prepared or not | none yet (SECURITY_MAP D) |
| `certificateLength` (50) | declared (inside op 50) | | `receive_certificate_spec` |
| `contentShape` (51) | declared (inside op 50) | | `receive_contentShape_spec`, `receiveAccept_opened_contentShape` |
| `prekeyShape` (52) | declared (inside op 50) | | `receive_prekeyShape_spec`, `receiveAccept_opened_prekeyShape` |
| `prekeyIds` (53) | `Flow.Receive.openFirst` (op 50) | the prekey ids a first message names, whether it names a one-time prekey, its Kyber ciphertext | `receive_prekeyOpen_spec`, `receiveAccept_opened_prekeyOpen`, `receive_prekeyOpen_rejects` |
| `signalShape` (54) | declared (inside op 51) | | `receive_signalShape_spec`, `receiveAccept_opened_signalShape` |
| `sessionStatus` (55) | `Flow.Receive.openFirst`, `Flow.Receive.session` (ops 50, 51) | a refused message's status byte (which layer refused it) | `receiveAccept_session_status_iff`, `receiveAccept_session_status_cases` |
| `receivedText` (56) | `Flow.Receive.session` (op 51) | a new contact's first message text | `receive_text_spec`, `receiveAccept_text_zero_unless_accepted`, `receiveAccept_receiveText_gated` |
| `accessKeyStatus` (57) | declared (inside op 51) | | `receive_accessKey_spec`, `receiveAccessKey_withAccessKey_status` |
| `bundleShape` (60) | `Flow.Refresh.shape` (op 59) | which bytes of a prekey response are JSON punctuation | `bundleShape_spec`, `bundle_shape_length`, `bundle_structural_value` |
| `identityChanged` (61) | declared (part of `deviceStatus` today) | | none yet |
| `deviceStatus` (62) | `Flow.Refresh.establish` (op 60) | one status byte per establishment step (255 ok, 254 new identity key, else refused) | `establishVerified_spec`, `establish_rejects`, `bundle_rebind_rejects` |
| `maskedPassword` (70) | `Flow.Ceremony.secrets` (op 80) | to this party only: its XOR shares of the two passwords (`Secret`) | `ceremonySecrets_spec`, `ceremony_masked_hides` |
| `maskedBit` … `scalarBitChecks` (80-87) | declared (S10) | | section 6a |
| `maskedDenominator` … `linkChecks` (90-95) | declared (S11) | | section 6b |
| `commitment`, `commitOpening`, `ownPublicPoint` (100-102) | declared (S9-S11; inside op 33 and the curve ops today) | | the S9 script: `prand_commit_before_open`; section 6d |

"Declared": no flow releases this kind to the controller today (it is released and consumed
inside a worker operation); its function comes with the flow's Lean script.

No I/O; no emitter imports this module.
-/

namespace TlsMpc.Node
open TlsMpc.TlsWire

/-- A value that left the engines (or this party's secrets) through a function of this file;
`r` names the opening (SECURITY_MAP B). Public: `.val` is unrestricted. -/
structure Opened (r : RevealKind) (α : Type) where
  private mk ::
  val : α

/-- A received first message's public part (op 50): the prekey ids it names and its Kyber
ciphertext. -/
structure PrekeyIds where
  /-- Whether it names a one-time prekey (else `oneTime` is meaningless). -/
  usesOneTime : Bool
  oneTime : Nat
  signed : Nat
  kyber : Nat
  /-- The Kyber-1024 ciphertext (1568 bytes). -/
  kyberCiphertext : Bytes

namespace Reveal

/-! ## TLS -/

/-- **`handshakeShare`** (`Flow.Tls.handshake`, op 1): the client's X25519 key share (32) and
hello random (32), both sent in the ClientHello. Bound: none yet (SECURITY_MAP D). -/
def handshakeShare (share random : Bytes) : Opened .handshakeShare (Bytes × Bytes) := ⟨(share, random)⟩

/-- **`handshakeRecord`** (`Flow.Tls.handshake`, op 3): a server handshake record's type (21 or
22) and plaintext. Bound: `publicHandshake_gate_value`, `publicHandshake_application_not_released`,
`tlsOpenHandshake_spec`. -/
def handshakeRecord (kind : Nat) (plaintext : Bytes) : Opened .handshakeRecord (Nat × Bytes) := ⟨(kind, plaintext)⟩

/-- **`finishedAccepted`** (`Flow.Tls.handshake`, op 5): whether the server's Finished verified.
Bound: `tlsVerifyFinished_spec`. -/
def finishedAccepted (accepted : Bool) : Opened .finishedAccepted Bool := ⟨accepted⟩

/-- **`clientFinished`** (`Flow.Tls.handshake`, op 6): the client Finished record, sealed under
the client handshake key, for the server. Bound: `tlsFinish_spec`. -/
def clientFinished (wire : Bytes) : Opened .clientFinished Bytes := ⟨wire⟩

/-- **`recordEvent`** (`Flow.Tls.application`, op 12): an application record's event (payload
handle, control event or fatal), never its content. Bound: `typedOpen_gated`,
`tlsOpenApplication_event_private`, `postHandshake_reject_unauthenticated`. -/
def recordEvent (event : TlsApplication.Event TlsWorker.BufferHandle) :
    Opened .recordEvent (TlsApplication.Event TlsWorker.BufferHandle) := ⟨event⟩

/-- **`sealedRecord`** (`Flow.Tls.application`, ops 13, 14): a sealed TLS record (header,
ciphertext, tag) for the server. Bound: `tlsRecord_sealCore_compiled`, `tlsSealCtr_spec`,
`gcmTag_spec`. -/
def sealedRecord (wire : Bytes) : Opened .sealedRecord Bytes := ⟨wire⟩

/-- **`serverBytes`** (`Flow.Tls.revealRange`, op 43): the record's length and the bytes asked for
(none past the length). Precondition, kept by the caller: T1's budget (`PublicReceive.mayReveal`,
`PublicReceive.budget`). Bound: `tlsRevealMasked_value`; T1 (`receivePolicy_*`, section 4f). -/
def serverBytes (length : Nat) (bytes : Bytes) : Opened .serverBytes (Nat × Bytes) := ⟨(length, bytes)⟩

/-! ## Policy-public values and the upgrade -/

/-- **`jointRandom`** (`Flow.Random.joint`, op 33): 32 bytes of joint randomness (the XOR of both
parties' committed contributions). Bound: for the S9 script `prand_a_honest`, `prand_b_ideal`; the
legacy operation: none (SECURITY_MAP D). -/
def jointRandom (bytes : Bytes) : Opened .jointRandom Bytes := ⟨bytes⟩

/-- **`upgradeNonce`** (`Flow.Upgrade.anonymous`, op 45): the WebSocket nonce (16 bytes of joint
randomness) and its accept value (28). Bound: the S9 script `upgrade_honest`; `wsAccept_accept_spec`. -/
def upgradeNonce (nonce accept : Bytes) : Opened .upgradeNonce (Bytes × Bytes) := ⟨(nonce, accept)⟩

/-- **`upgradeAccept`** (`Flow.Upgrade.authenticated`, op 32): the accept value the server must
answer the authenticated upgrade with (28 bytes); the request itself stays in the engines. Bound:
`signalUpgradeShared_spec`, `signalUpgrade_spec`. -/
def upgradeAccept (accept : Bytes) : Opened .upgradeAccept Bytes := ⟨accept⟩

/-! ## Stored state -/

/-- **`blobAccepted`** (`Flow.Contacts.load`, `Flow.Contacts.loadDevices`, ops 37, 63): whether a
stored blob opened under the contact's key. Bound: `contactOpen_accepted_iff`,
`contactOpen_rejected`. -/
def blobAccepted (accepted : Bool) : Opened .blobAccepted Bool := ⟨accepted⟩

/-- **`sealedBlob`** (`Flow.Contacts.seal`, `Flow.Account.seal`, `Flow.Refresh.scratchSeal`; ops
38, 54, 64): check value and ciphertext of a state sealed under a fresh nonce. Bound:
`contactSeal_spec`, `contact_round_trip`. -/
def sealedBlob (sealed : Bytes) : Opened .sealedBlob Bytes := ⟨sealed⟩

/-- **`assignStatus`** (`Flow.Contacts.assign`, op 52): whether the provisional contact took the
id. Bound: none yet (SECURITY_MAP D). -/
def assignStatus (taken : Bool) : Opened .assignStatus Bool := ⟨taken⟩

/-! ## Send -/

/-- **`sealedEnvelope`** (`Flow.Send.seal`, `Flow.Send.sealDevices`; ops 41, 61): `none` when the
contact's state cannot produce a message, else the timestamp and the envelope per device, for the
server. Bound: `signalSealBuilt_spec`, `signalSeal_value`, `sealValue_accepted`. -/
def sealedEnvelope (sealed : Option (Nat × List Bytes)) : Opened .sealedEnvelope (Option (Nat × List Bytes)) := ⟨sealed⟩

/-- **`ephemeralPublic`** (inside ops 41, 61: the send's curve half, `Flows/JoinBackend.lean`
`sendCurve`, S11's offset step): a message's ephemeral X25519 public key u(K₀ + τ·B), 32 bytes,
public in the sealed-sender envelope. Bound: `Curve.ephemeralKey_spec` (`s11_ephemeralKey`: a
function of the public K₀ and the joint public offset τ only). Added when the stages were joined
(`scripts-stack`). -/
def ephemeralPublic (key : Bytes) : Opened .ephemeralPublic Bytes := ⟨key⟩

/-- **`prepareStatus`** (`Flow.Curve.prepareContacts`, op 66): one status byte per contact.
Bound: none yet (SECURITY_MAP D). -/
def prepareStatus (statuses : Bytes) : Opened .prepareStatus Bytes := ⟨statuses⟩

/-! ## Receive -/

/-- **`prekeyIds`** (`Flow.Receive.openFirst`, op 50): the prekey ids a first message names and
its Kyber ciphertext. Bound: `receive_prekeyOpen_spec`, `receiveAccept_opened_prekeyOpen`. -/
def prekeyIds (ids : PrekeyIds) : Opened .prekeyIds PrekeyIds := ⟨ids⟩

/-- **`sessionStatus`** (`Flow.Receive.openFirst`, `Flow.Receive.session`; ops 50, 51): the status
byte of a refused message. Bound: `receiveAccept_session_status_iff`,
`receiveAccept_session_status_cases`. -/
def sessionStatus (status : Nat) : Opened .sessionStatus Nat := ⟨status⟩

/-- **`receivedText`** (`Flow.Receive.session`, op 51): a new contact's first message text.
Bound: `receive_text_spec`, `receiveAccept_text_zero_unless_accepted`,
`receiveAccept_receiveText_gated`. -/
def receivedText (text : String) : Opened .receivedText String := ⟨text⟩

/-! ## Refresh -/

/-- **`bundleShape`** (`Flow.Refresh.shape`, op 59): per byte of the prekey response, whether it
is JSON punctuation. Bound: `bundleShape_spec`, `bundle_shape_length`. -/
def bundleShape (flags : List Bool) : Opened .bundleShape (List Bool) := ⟨flags⟩

/-- **`deviceStatus`** (`Flow.Refresh.establish`, op 60): one step's status byte (255 ok, 254 a
new identity key, else refused). Bound: `establishVerified_spec`, `establish_rejects`. -/
def deviceStatus (status : Bytes) : Opened .deviceStatus Bytes := ⟨status⟩

end Reveal
end TlsMpc.Node
