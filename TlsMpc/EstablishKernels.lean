import TlsMpc.HybridKernels
import TlsMpc.Signal.Establish
import TlsMpc.Signal.MlKem

/-!
Worker kernels for sender-side session establishment from a recipient's prekey
bundle (PQXDH), in the conventions of `TlsMpc/HybridKernels.lean`: named input
and output fields, and only outputs marked `opened` may be opened.

The bodies are the definitions of `TlsMpc/Signal/Establish.lean` (which also
lists the libsignal sources). The theorems are in `TlsMpc/EstablishProofs.lean`.

What stays private: every bundle field (identity key, prekeys, their ids and
signatures), the recipient UUID and access key, all agreements and keys, and
the validity of the signatures. What is opened: one status byte per
establishment (pass or fail, not the reason), and for a message the status,
the timestamp and the sealed-sender envelope, whose length depends only on the
public shape parameters.

## Order of operations for one establishment

X25519 runs in the field engine with the existing program (`x25519-fast`); the
XEdDSA point arithmetic runs there with the two programs of
`TlsMpc/EstablishField.lean`.

1. `establish-points` gives the recipient's keys as field elements.
2. Field: `xeddsa-recover` on `identityPoint` gives `identityValid`,
   `identityX`, `identityY`; convert each to bits.
3. `establish-challenges` gives, for each of the two signatures, `flip`, the
   challenge bits and the scalar bits.
4. Field: `xeddsa-check` once per signature gives `ecRx, ecRy` and
   `pqRx, pqRy`; convert each to bits.
5. `establish-verified` gives the private mask `verified`.
6. Field: the agreements (scalar · point, as X25519 with the usual clamping):

   * `dh1` = own identity private key · recipient signed prekey
   * `dh2` = base private key · recipient identity key
   * `dh3` = base private key · recipient signed prekey
   * `dh4` = base private key · recipient one-time prekey (if the bundle has one)
   * `ratchetAgreement` = first sending ratchet private key · recipient signed prekey
   * `basePublic` = base private key · 9, `ratchetPublic` = ratchet private key · 9,
     `senderPublic` = own identity private key · 9

   The base and ratchet private keys are fresh uniform scalars that neither
   party knows.
7. `establish-kem` (Kyber-1024 encapsulation to the recipient's Kyber prekey)
   gives `kemStatus`, `kemCiphertext`, `kemSecret`.
8. `establish-session` gives the opened `status` and the private records
   `conversation`, `pending` and `receiver`.
9. `establish-seal` sends a message. Every message until the recipient answers
   must use it (with the same `pending` record), because the recipient can only
   create its session from a PreKeySignalMessage.
-/
namespace TlsMpc.EstablishKernel
open Std.Tactic.BVDecide
open Signal
open HybridKernel (Kernel Shape Output lookup pub priv sl conversationBytes)

/-- Size of the `pending` record (`Establish.pending`). -/
def pendingBytes : Nat := 1616

/-- A private output handed to the field engine: its first `count` bits. -/
def bits (name : String) (count : Nat) (value : List (BVExpr 8)) : Output :=
  { name, bits := count, opened := false, value }

/-- The recipient's public keys as 255-bit words (top bit dropped, as X25519
and the XEdDSA decoding both do). No gates. -/
def establishPoints (withOneTime : Bool) : Kernel :=
  let inputs := [("identityKey", Shape.bytes 32), ("signedPrekey", .bytes 32)] ++
    (if withOneTime then [("oneTimePrekey", Shape.bytes 32)] else [])
  let get := lookup inputs
  { name := "establish-points", inputs, outputs :=
      [bits "identityPoint" 255 (get "identityKey"), bits "signedPrekeyPoint" 255 (get "signedPrekey")] ++
      (if withOneTime then [bits "oneTimePrekeyPoint" 255 (get "oneTimePrekey")] else []) }

def challengeInputs : List (String × Shape) :=
  [("identityX", Shape.word), ("identityY", .word), ("signedPrekey", .bytes 32),
    ("signedPrekeySignature", .bytes 64), ("kyberPrekey", .bytes 1568), ("kyberPrekeySignature", .bytes 64)]

/-- The XEdDSA challenges of the two bundle signatures: the signed prekey's
over `05 ‖ key` and the Kyber prekey's over `08 ‖ key`, both under the identity
key whose recovered Edwards coordinates are `identityX`, `identityY`. For each:
`flip` (whether `x` must be negated to match the signature's sign bit), the 256
bits of `h = SHA-512(R ‖ A ‖ message) mod ℓ`, and the 253 low bits of `s`.
All of them are inputs of the field program `xeddsa-check`. -/
def establishChallenges : Kernel :=
  let get := lookup challengeInputs
  let run := fun (tag : Nat) (signature key : String) =>
    Establish.challenge ByteAuth.symbolic XEdDsaSha512.symbolic XEdDsaScalar.symbolic tag
      (get signature) (get "identityX") (get "identityY") (get key)
  let ec := run 5 "signedPrekeySignature" "signedPrekey"
  let pq := run 8 "kyberPrekeySignature" "kyberPrekey"
  { name := "establish-challenges", inputs := challengeInputs, outputs := [
      bits "ecFlip" 1 (ec.take 1), priv "ecChallenge" (ec.drop 1),
      bits "ecScalar" 253 ((get "signedPrekeySignature").drop 32),
      bits "pqFlip" 1 (pq.take 1), priv "pqChallenge" (pq.drop 1),
      bits "pqScalar" 253 ((get "kyberPrekeySignature").drop 32)] }

def verifiedInputs : List (String × Shape) :=
  [("identityValid", Shape.word), ("ecRx", .word), ("ecRy", .word), ("pqRx", .word), ("pqRy", .word),
    ("signedPrekeySignature", .bytes 64), ("kyberPrekeySignature", .bytes 64)]

/-- The private validity mask of the bundle: 255 exactly when the identity key
is a curve point and both recomputed points match their signatures. -/
def establishVerified : Kernel :=
  let get := lookup verifiedInputs
  { name := "establish-verified", inputs := verifiedInputs, outputs := [
      priv "verified" [Establish.verified ByteAuth.symbolic (get "signedPrekeySignature")
        (get "kyberPrekeySignature") (get "identityValid") (get "ecRx") (get "ecRy") (get "pqRx") (get "pqRy")]] }

def sessionInputs (cert : Nat) (withOneTime : Bool) : List (String × Shape) :=
  [("verified", Shape.bytes 1), ("kemStatus", .bytes 1), ("dh1", .word), ("dh2", .word), ("dh3", .word)] ++
  (if withOneTime then [("dh4", Shape.word)] else []) ++
  [("ratchetAgreement", .word), ("kemSecret", .bytes 32), ("kemCiphertext", .bytes 1568),
    ("basePublic", .word), ("ratchetPublic", .word), ("senderPublic", .word),
    ("identityKey", .bytes 32), ("signedPrekey", .bytes 32), ("certificate", .bytes cert),
    ("uuid", .bytes 16), ("accessKey", .bytes 16), ("requestId", .bytes 8), ("deviceId", .bytes 1),
    ("registrationId", .bytes 4), ("localRegistrationId", .bytes 4)] ++
  (if withOneTime then [("oneTimePrekeyId", Shape.bytes 4)] else []) ++
  [("signedPrekeyId", .bytes 4), ("kyberPrekeyId", .bytes 4)]

/-- The session keys and records. `status` is 255 exactly when `verified` and
`kemStatus` are 255 and no agreement is all zero; otherwise every record is
zero (a zero conversation record is rejected by every send kernel).

* `conversation`: the record the send kernels consume
  (`HybridKernel.conversationBytes cert 80`), with counters zero, post-quantum
  epoch 1 and the request id as given.
* `pending` (1616): what `establish-seal` needs for the PreKeySignalMessage.
* `receiver` (192): root key, receiving chain key, the recipient's ratchet key,
  and the post-quantum keys, for a later receive path. -/
def establishSession (cert : Nat) (withOneTime : Bool) : Kernel :=
  let inputs := sessionInputs cert withOneTime
  let get := lookup inputs
  let out := Establish.establish Sha256Ripple.ops ByteAuth.symbolic 80 (get "verified" ++ get "kemStatus")
    (get "dh1") (get "dh2") (get "dh3") (get "dh4") (get "kemSecret") (get "ratchetAgreement")
    (get "basePublic") (get "ratchetPublic") (get "senderPublic") (get "identityKey") (get "signedPrekey")
    (get "certificate") (get "uuid") (get "accessKey") (get "requestId") (get "deviceId") (get "registrationId")
    (get "localRegistrationId") (if withOneTime then get "oneTimePrekeyId" else HybridKernel.zeros 4)
    (get "signedPrekeyId") (get "kyberPrekeyId") (get "kemCiphertext")
  { name := "establish-session", inputs, outputs := [
      pub "status" (out.getD 0 []), priv "conversation" (out.getD 1 []), priv "pending" (out.getD 2 []),
      priv "receiver" (out.getD 3 [])] }

def sealInputs (cert : Nat) : List (String × Shape) :=
  [("conversation", Shape.bytes (conversationBytes cert 80)), ("pending", .bytes pendingBytes),
    ("localAddress", .bytes 17), ("text", .bytes 59), ("ephemeralPublic", .word), ("senderPublic", .word),
    ("ephemeralAgreement", .word), ("staticAgreement", .word)]

/-- One sealed-sender text message on an unacknowledged session: the message
encryption of `HybridKernel.signalSealFixed` with the two addresses in the
SignalMessage, wrapped in a PreKeySignalMessage built from `pending`, sealed
with message type PREKEY_MESSAGE. `localAddress` is the client's own UUID (16)
and device id (1). The other inputs, the outputs and the selection of the next
record are as in `signalSealFixed`. -/
def establishSeal (cert : Nat) (withOneTime : Bool) (counterWidth previousWidth epochWidth indexWidth : Nat) : Kernel :=
  let inputs := sealInputs cert
  let get := lookup inputs
  let record := get "conversation"
  let certificate := sl record 0 cert
  let metadata := sl record (cert + 262) 57
  let text := PrivateTextNotification.build Sha256.symbolic Varint64.symbolic ByteAuth.symbolic (get "text")
  let out := Establish.sealMessage Aes.symbolic Varint64.symbolic Sha256Ripple.ops ByteAuth.symbolic withOneTime
    ⟨counterWidth, previousWidth, true⟩ ⟨epochWidth, indexWidth, 0, false⟩ 80 (sl record cert 262) metadata
    (get "pending") certificate (get "localAddress") text (get "ephemeralPublic") (get "senderPublic")
    (get "ephemeralAgreement") (get "staticAgreement")
  { name := "establish-seal", inputs, outputs := [
      pub "status" (out.getD 0 []), priv "conversation" (certificate ++ out.getD 1 [] ++ metadata),
      pub "timestamp" (sl text 82 8), pub "envelope" (out.getD 2 [])] }

def kemInputs : List (String × Shape) :=
  [("kyberPrekey", Shape.bytes 1568), ("entropyA", .bytes 32), ("entropyB", .bytes 32)]

/-- Kyber-1024 encapsulation (the variant libsignal uses for PQXDH, key type
8) to the recipient's private Kyber prekey, with the XOR of one private
entropy input from each party. Uses the existing `Signal.MlKem.encapsulate`
with rank 4, η = 2, compression 11 and 5 bits, and a budget of 448 candidates
per matrix entry; `kemStatus` is 0 if a matrix entry exhausted that budget.

This kernel is DEFINED but has not been lowered or run in this form: the
existing arithmetic (generic 32-bit multiply and remainder per coefficient
operation) makes it about 190 million AND gates. See the cost note in the
report that accompanies this file. -/
def establishKem : Kernel :=
  let a := ByteAuth.symbolic
  let get := lookup kemInputs
  let entropy := List.zipWith a.xor (get "entropyA") (get "entropyB")
  let result := MlKem.encapsulate MlKemArithmetic.symbolic MlKemEncoding.symbolic Sha256.symbolic a
    Word64.symbolic Keccak.symbolic 4 2 11 5 224 true (get "kyberPrekey") entropy
  { name := "establish-kem", inputs := kemInputs, outputs := [
      priv "kemStatus" [result.success],
      priv "kemCiphertext" (ByteAuth.release a result.success (result.bytes.take 1568)),
      priv "kemSecret" (ByteAuth.release a result.success (result.bytes.drop 1568))] }

def flag : String → Option Bool
  | "0" => some false
  | "1" => some true
  | _ => none

/-- Kernel named on the command line, with its public shape parameters:
`establish-points ONETIME`, `establish-challenges`, `establish-verified`,
`establish-kem`, `establish-session CERT ONETIME`,
`establish-seal CERT ONETIME COUNTER PREVIOUS EPOCH INDEX` (`ONETIME` is 0 or 1;
the last four are varint widths as in `signal-seal-fixed`). -/
def find : List String → Option Kernel
  | ["establish-challenges"] => some establishChallenges
  | ["establish-verified"] => some establishVerified
  | ["establish-kem"] => some establishKem
  | ["establish-points", oneTime] => (flag oneTime).map establishPoints
  | ["establish-session", cert, oneTime] =>
      match cert.toNat?, flag oneTime with
      | some cert, some oneTime => if cert ≤ 1024 then some (establishSession cert oneTime) else none
      | _, _ => none
  | ["establish-seal", cert, oneTime, counterWidth, previousWidth, epochWidth, indexWidth] =>
      match cert.toNat?, flag oneTime, counterWidth.toNat?, previousWidth.toNat?, epochWidth.toNat?, indexWidth.toNat? with
      | some cert, some oneTime, some cw, some pw, some ew, some iw =>
          if cert ≤ 1024 && 1 ≤ cw && cw ≤ 5 && 1 ≤ pw && pw ≤ 5 && 1 ≤ ew && ew ≤ 10 && 1 ≤ iw && iw ≤ 5 then
            some (establishSeal cert oneTime cw pw ew iw) else none
      | _, _, _, _, _, _ => none
  | _ => none

end TlsMpc.EstablishKernel
