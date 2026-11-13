/-!
# Public and engine values in the types (REORGANIZATION_PLAN.md section 4.1, stages S4, S6)

With `Secret` (`TlsMpc/Node/Secret.lean`), the three kinds of value the controller holds:
- `Secret α`: this party's own; only its eliminators look inside;
- `Opened r α` (`TlsMpc/Node/Reveal.lean`): a value released from the engines (or from this
  party's secrets) by the opening `r`, one function per opening in `Reveal.lean`. Public: `.val`
  is unrestricted;
- `Handle e`: an engine value, which carries no bytes.

Everything else the controller holds is public by construction: configuration, the application's
request and text, opened values, and what is computed from those.

`RevealKind` (stage S6) lists every opening of plan section 4.3 (SECURITY_MAP B), each with a
fixed numeric `code`. `Opened`'s private constructor is in `Reveal.lean`, so the functions there
are the only way to make an opened value. Pure; no emitter imports this module.
-/

namespace TlsMpc.Node

/-- The openings (plan 4.3, SECURITY_MAP B): everything a flow may release to this node or to the
peer. A value of type `Opened r α` can only be made by `r`'s function in `Reveal.lean`, whose
docstring says which flow produces it, what it reveals, and the theorem that bounds it.

**Codes.** Each kind has a fixed numeric `code` (`RevealKind.code`, grouped by tens). The engine's
release labels are these codes: `TlsMpc/Node/Engine/Labels.lean` imports this file and
`Label.ofKind k = ⟨k.code⟩` is each kind's label (`Label.ofKind_inj`). Codes are never reused; a new
kind takes a new code. -/
inductive RevealKind where
  -- TLS (codes 1-19)
  /-- The client's X25519 key share and hello random (op 1, `begin`). -/
  | handshakeShare
  /-- A server handshake record's plaintext, alert or handshake type only (op 3). -/
  | handshakeRecord
  /-- Whether the server's Finished verified (op 5). -/
  | finishedAccepted
  /-- The client's Finished record, sealed (op 6). -/
  | clientFinished
  /-- The handshake-or-not bit of a typed record opening (`tls-open-typed`). Declared. -/
  | recordKindBit
  /-- The event of an application record's opening: payload handle, control event, fatal (op 12). -/
  | recordEvent
  /-- A sealed TLS record (header, ciphertext, tag) to send (ops 13, 14). -/
  | sealedRecord
  /-- Revealed bytes of an authenticated server record, within T1's budget (op 43). -/
  | serverBytes
  /-- A GHASH key power masked to party B (returns `Secret`). Declared (S12). -/
  | ghashMaskedPower
  -- Policy-public values and the WebSocket upgrade (codes 20-29)
  /-- Joint randomness: the XOR of both parties' committed contributions (op 33). -/
  | jointRandom
  /-- The database read's parity shares (trusted, designed public). Declared (they go through
  `Channels.exchange`, not a flow). -/
  | parity
  /-- The unauthenticated upgrade's nonce (joint randomness) and its accept value (op 45). -/
  | upgradeNonce
  /-- The authenticated upgrade's expected accept value (op 32). -/
  | upgradeAccept
  -- Stored state (codes 30-39)
  /-- Whether a stored blob opened under its key (ops 37, 63; op 55 aborts instead). -/
  | blobAccepted
  /-- A sealed blob: check value and ciphertext (ops 38, 54, 64). -/
  | sealedBlob
  /-- Whether a provisional contact took its signup token's id (op 52). -/
  | assignStatus
  -- Send (codes 40-49)
  /-- The digit widths of a send's counters. Declared (inside op 41 today). -/
  | counterWidths
  /-- A sealed-sender envelope: status, timestamp, envelope bytes (ops 41, 61). -/
  | sealedEnvelope
  /-- The ephemeral public key of a sealed-sender envelope. Declared (inside ops 41, 61). -/
  | ephemeralPublic
  /-- Per contact, whether its per-session curve preparation ran (op 66). -/
  | prepareStatus
  -- Receive (codes 50-59)
  /-- The sender certificate's length. Declared (inside op 50). -/
  | certificateLength
  /-- The decrypted content's shape. Declared (inside op 50). -/
  | contentShape
  /-- The PreKey message's shape. Declared (inside op 50). -/
  | prekeyShape
  /-- The prekey ids a first message names and its Kyber ciphertext (op 50). -/
  | prekeyIds
  /-- The Signal message's shape. Declared (inside op 51). -/
  | signalShape
  /-- A receive step's status byte: which layer refused a message (ops 50, 51). -/
  | sessionStatus
  /-- A received message's text (op 51). -/
  | receivedText
  /-- Whether the sender's access key matched. Declared (inside op 51). -/
  | accessKeyStatus
  -- Refresh (codes 60-69)
  /-- Which bytes of a prekey response are JSON punctuation (op 59). -/
  | bundleShape
  /-- A refreshed bundle's identity key is a new one (op 60's 254). Declared: today part of
  `deviceStatus`. -/
  | identityChanged
  /-- One establishment step's status byte (op 60). -/
  | deviceStatus
  -- Ceremony (codes 70-79)
  /-- The masked account and recovery passwords: this party's XOR shares (`Secret`; op 80). -/
  | maskedPassword
  -- Conversions (codes 80-89), all declared until S10
  | maskedBit
  | maskedWord
  | maskedFieldValue
  | cutCandidates
  | bucketSums
  | referenceFlags
  | bitBlockChecks
  | scalarBitChecks
  -- Curve (codes 90-99), all declared until S11
  | maskedDenominator
  | curveChecks
  | liftW
  | liftZ
  | pointValid
  | linkChecks
  -- Own-secret reveals (codes 100-109), declared until S9-S11
  /-- A commitment to this party's own value (joint randomness, offsets, challenges). -/
  | commitment
  /-- The opening of such a commitment. -/
  | commitOpening
  /-- A public point of this party's own scalar (split-ECDH share kA·B, the K₀ half). -/
  | ownPublicPoint
  deriving DecidableEq, Repr

namespace RevealKind

/-- The fixed numeric code of each kind (see the type's docstring: the engine's release labels
map to these). -/
def code : RevealKind → Nat
  | handshakeShare => 1 | handshakeRecord => 2 | finishedAccepted => 3 | clientFinished => 4
  | recordKindBit => 5 | recordEvent => 6 | sealedRecord => 7 | serverBytes => 8
  | ghashMaskedPower => 9
  | jointRandom => 20 | parity => 21 | upgradeNonce => 22 | upgradeAccept => 23
  | blobAccepted => 30 | sealedBlob => 31 | assignStatus => 32
  | counterWidths => 40 | sealedEnvelope => 41 | ephemeralPublic => 42 | prepareStatus => 43
  | certificateLength => 50 | contentShape => 51 | prekeyShape => 52 | prekeyIds => 53
  | signalShape => 54 | sessionStatus => 55 | receivedText => 56 | accessKeyStatus => 57
  | bundleShape => 60 | identityChanged => 61 | deviceStatus => 62
  | maskedPassword => 70
  | maskedBit => 80 | maskedWord => 81 | maskedFieldValue => 82 | cutCandidates => 83
  | bucketSums => 84 | referenceFlags => 85 | bitBlockChecks => 86 | scalarBitChecks => 87
  | maskedDenominator => 90 | curveChecks => 91 | liftW => 92 | liftZ => 93 | pointValid => 94
  | linkChecks => 95
  | commitment => 100 | commitOpening => 101 | ownPublicPoint => 102

/-- Every kind, once. -/
def all : List RevealKind :=
  [handshakeShare, handshakeRecord, finishedAccepted, clientFinished, recordKindBit, recordEvent,
   sealedRecord, serverBytes, ghashMaskedPower,
   jointRandom, parity, upgradeNonce, upgradeAccept,
   blobAccepted, sealedBlob, assignStatus,
   counterWidths, sealedEnvelope, ephemeralPublic, prepareStatus,
   certificateLength, contentShape, prekeyShape, prekeyIds, signalShape, sessionStatus,
   receivedText, accessKeyStatus,
   bundleShape, identityChanged, deviceStatus,
   maskedPassword,
   maskedBit, maskedWord, maskedFieldValue, cutCandidates, bucketSums, referenceFlags,
   bitBlockChecks, scalarBitChecks,
   maskedDenominator, curveChecks, liftW, liftZ, pointValid, linkChecks,
   commitment, commitOpening, ownPublicPoint]

/-- `all` lists every kind. -/
theorem mem_all (r : RevealKind) : r ∈ all := by cases r <;> decide

/-- **No two kinds share a code**, so a code names its kind. -/
theorem codes_distinct : (all.map code).Nodup := by decide

/-- Code 0 is no kind's (the engine's `check` refuses label 0). -/
theorem code_ne_zero (r : RevealKind) : r.code ≠ 0 := by cases r <;> decide

end RevealKind

/-- Which engine holds a value: the Boolean engine (wires) or the field engine (shares). -/
inductive EngineKind where
  | boolean
  | field
  deriving BEq, Repr, DecidableEq

/-- An engine value (Boolean wires or field shares); carries no bytes. Allocated by scripts
(plan section 5). -/
structure Handle (e : EngineKind) where
  id : UInt64
  deriving BEq, Repr

/-- A contact's id: the application's public u128 (`notify(ids, message)`). -/
abbrev ContactId := Nat

end TlsMpc.Node
