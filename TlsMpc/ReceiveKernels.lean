import TlsMpc.EstablishKernels
import TlsMpc.Signal.ReceiveFirst

/-!
Worker kernels for RECEIVING a new contact's first message (a sealed-sender v1
envelope carrying a PreKeySignalMessage) as the PQXDH responder, in the
conventions of `TlsMpc/HybridKernels.lean`: named input and output fields, and
only outputs marked `opened` may be opened.

The bodies are the definitions of `TlsMpc/Signal/ReceiveFirst.lean` (which
lists the libsignal sources and what the public layouts reveal). The theorems
are in `TlsMpc/ReceiveProofs.lean`; the field program in
`TlsMpc/ReceiveField.lean`.

What stays private: the envelope and everything decrypted from it — the
sender's identity key, certificate, UUID, device id, registration id, base and
ratchet keys — every agreement and key, and the produced records. What is
opened: lengths and varint widths (the `shape` outputs and
`certificateLength`), our own prekey ids named in the message, the Kyber
ciphertext, one status byte, and — by `receive-text`, from a plaintext that is
zero unless the status is 255 — the message body with its length.

Our own keys: the identity private key is secret-shared; the signed prekey,
one-time prekeys and Kyber prekey private keys are known to both parties, as
are all our public keys and ids. `ourIdentity`, `localAddress`, `now`,
`signer`, `serverX`, `serverY`, `serverValid`, `kemSecret`, `certificate` (our
own sender certificate), `accessKey`-less constants are therefore public
values that both parties supply identically.

## Order of operations for one envelope of `SIZE` bytes

Field engine programs: `x25519-fast` (shared scalar) for agreements with our
identity key; the same ladder with public scalar bits for agreements with our
prekeys; `xeddsa-recover`, `xeddsa-check` (`TlsMpc/EstablishField.lean`);
`receive-torsion` (`TlsMpc/ReceiveField.lean`).

 1. `receive-envelope-point SIZE`: `ephemeralPoint`.
 2. Field: `agreement` = our IDENTITY private key (shared scalar) ·
    `ephemeralPoint`.
 3. `receive-unseal-static SIZE`: `staticValid`, `senderIdentity`,
    `senderPoint`, `chain`.
 4. Field: `agreement` = our IDENTITY private key (shared scalar) ·
    `senderPoint`.
 5. `receive-unseal-message SIZE`: `valid`, `content`; opens
    `certificateLength` (two bytes `C0 C1`, a varint).
 6. `receive-content-shape U C0 C1` (`U` = size of `content`): opens `shape` =
    plain, hinted, phone number present, phone number length. Exactly one of
    plain / hinted is 255 for a well-formed content: `HINT` = 0 or 1.
 7. `receive-content U C0 C1 HINT`: `valid`, `messageType`, `certificate`,
    `message` (all private).
 8. `receive-certificate C0 C1 PRESENT LENGTH` (the last two as opened in
    step 6) with the public `signer`, `now`, `serverX`, `serverY`:
    `certificateValid`, `uuid`, `deviceId`, `signature`, and the challenge
    `flip`, `challenge`, `scalar`.
 9. Field: `xeddsa-check` on (`serverX`, `serverY`, `flip`, `challenge`,
    `scalar`) gives `rx`, `ry`. (`serverX`, `serverY`, `serverValid` are
    `xeddsa-recover` of the public server key; they may be computed once.)
10. `receive-certificate-verified`: `verified`.
11. `receive-prekey-shape N` (`N` = size of `message`): opens 21 flags giving
    `P` (0 if no one-time prekey id, else its width), `R`, `S`, `K` (widths
    of the registration id, signed prekey id, Kyber prekey id; width = 1 +
    index of the set flag).
12. `receive-prekey-open N P R S K`: private `prekeyValid`, `basePoint`,
    `ratchetPoint`; opens `oneTimePrekeyId`, `signedPrekeyId`,
    `kyberPrekeyId`, `kyberCiphertext` (zero unless valid).
13. Outside the engines: `kemSecret` = Kyber-1024 decapsulation of
    `kyberCiphertext` under the named Kyber prekey (a key both parties hold).
14. Field: `xeddsa-recover` on `basePoint` gives `baseValid`, `baseX`,
    `baseY`; `receive-torsion` on (`baseX`, `baseY`) gives `torsionX`,
    `torsionY`. Agreements (X25519 with the usual clamping):

    * `dh1` = signed prekey (PUBLIC scalar) · `senderPoint`
    * `dh2` = IDENTITY key (SHARED scalar) · `basePoint`
    * `dh3` = signed prekey (PUBLIC scalar) · `basePoint`
    * `dh4` = one-time prekey (PUBLIC scalar) · `basePoint` (only if `P` > 0)
    * `receiveAgreement` = signed prekey (PUBLIC scalar) · `ratchetPoint`
    * `sendAgreement` = new ratchet private key (a fresh uniform scalar that
      neither party knows) · `ratchetPoint`
    * `ratchetPublic` = new ratchet private key · 9

    The signed prekey and one-time prekey used are the ones whose ids were
    opened in step 12.
15. `receive-signal-shape N P R S K` (input `valid` = `prekeyValid`): opens 13
    bytes giving `CW`, `PW` (widths of the counter and previous counter), the
    ciphertext length prefix `L0 L1`, and `ADDR` (0 or 1).
16. `receive-session CERT N P R S K CW PW L0 L1 ADDR JUMP`: opens `status`;
    private `conversation`, `receiver`, `plaintext`. `JUMP` is normally 0; a
    larger value accepts a message whose counter is up to `JUMP` (earlier
    messages of the chain lost).
17. `receive-text CIPHERTEXT CAPACITY`: opens `status`, `length`, `text`.

If a status is not 255 nothing else of that stage is released, and the
runtime learns only that the envelope was not accepted.
-/
namespace TlsMpc.ReceiveKernel
open Std.Tactic.BVDecide
open Signal
open HybridKernel (Kernel Shape Output lookup pub priv)
open EstablishKernel (bits)
open ReceiveFirst (decode2 bodyOf framed varintWidth messageAt)

/-- Size of the receiver record (`ReceiveFirst.session`). -/
def receiverBytes : Nat := 236

/-! ### Sealed sender -/

def envelopeInputs (size : Nat) : List (String × Shape) := [("envelope", Shape.bytes size)]

/-- The envelope's ephemeral key as a 255-bit word. No gates. -/
def envelopePoint (size : Nat) : Kernel :=
  { name := "receive-envelope-point", inputs := envelopeInputs size, outputs := [
      bits "ephemeralPoint" 255 (Establish.part (lookup (envelopeInputs size) "envelope") 4 32)] }

def staticInputs (size : Nat) : List (String × Shape) :=
  [("envelope", Shape.bytes size), ("ourIdentity", .bytes 32), ("agreement", .word)]

/-- First half of sealed sender: the sender's identity key (also as the word
for the second agreement) and the chain key. `agreement` is our identity
private key · `ephemeralPoint`. -/
def unsealStatic (size : Nat) : Kernel :=
  let get := lookup (staticInputs size)
  let out := ReceiveFirst.unsealStatic Aes.symbolic Sha256Ripple.ops ByteAuth.symbolic size (get "ourIdentity")
    (get "envelope") (get "agreement")
  { name := "receive-unseal-static", inputs := staticInputs size, outputs := [
      priv "staticValid" (out.getD 0 []), priv "senderIdentity" (out.getD 1 []),
      bits "senderPoint" 255 (out.getD 1 []), priv "chain" (out.getD 2 [])] }

def messageInputs (size : Nat) : List (String × Shape) :=
  [("envelope", Shape.bytes size), ("staticValid", .bytes 1), ("chain", .bytes 32), ("agreement", .word)]

/-- Size of the decrypted content of an envelope of `size` bytes. -/
def contentBytes (size : Nat) : Nat := size - messageAt size - 10

/-- Second half of sealed sender: the content. `agreement` is our identity
private key · `senderPoint`. Opens only the certificate's length prefix. -/
def unsealMessage (size : Nat) : Kernel :=
  let get := lookup (messageInputs size)
  let out := ReceiveFirst.unsealMessage Aes.symbolic Sha256Ripple.ops ByteAuth.symbolic size (get "envelope")
    (get "staticValid") (get "chain") (get "agreement")
  { name := "receive-unseal-message", inputs := messageInputs size, outputs := [
      priv "valid" (out.getD 0 []), priv "content" (out.getD 1 []), pub "certificateLength" (out.getD 2 [])] }

def contentInputs (size : Nat) : List (String × Shape) := [("content", Shape.bytes size), ("valid", .bytes 1)]

def contentShape (size cert : Nat) : Kernel :=
  let get := lookup (contentInputs size)
  let out := ReceiveFirst.contentShape ByteAuth.symbolic size cert (get "content") (get "valid")
  { name := "receive-content-shape", inputs := contentInputs size, outputs := [pub "shape" (out.getD 0 [])] }

/-- The content split into its parts. No cryptography. -/
def content (size cert : Nat) (hint : Bool) : Kernel :=
  let get := lookup (contentInputs size)
  let out := ReceiveFirst.contentParts ByteAuth.symbolic size cert hint (get "content") (get "valid")
  { name := "receive-content", inputs := contentInputs size, outputs := [
      priv "valid" (out.getD 0 []), priv "messageType" (out.getD 1 []), priv "certificate" (out.getD 2 []),
      priv "message" (out.getD 3 [])] }

/-! ### Sender certificate -/

def certificateInputs (cert : Nat) (c : ReceiveFirst.CertShape) : List (String × Shape) :=
  [("certificate", Shape.bytes cert), ("valid", .bytes 1), ("senderIdentity", .bytes 32),
    ("signer", .bytes c.signerSize), ("now", .bytes 8), ("serverX", .word), ("serverY", .word)]

/-- The sender's UUID and device id, the certificate's checks other than its
signature, and the signature's XEdDSA challenge (inputs of `xeddsa-check`). -/
def certificate (cert : Nat) (c : ReceiveFirst.CertShape) : Kernel :=
  let get := lookup (certificateInputs cert c)
  let out := ReceiveFirst.certificate ByteAuth.symbolic XEdDsaSha512.symbolic XEdDsaScalar.symbolic cert c
    (get "certificate") (get "valid") (get "senderIdentity") (get "signer") (get "now") (get "serverX") (get "serverY")
  { name := "receive-certificate", inputs := certificateInputs cert c, outputs := [
      priv "certificateValid" (out.getD 0 []), priv "uuid" (out.getD 1 []), priv "deviceId" (out.getD 2 []),
      priv "signature" (out.getD 3 []), bits "flip" 1 (out.getD 4 []), priv "challenge" (out.getD 5 []),
      bits "scalar" 253 ((out.getD 3 []).drop 32)] }

def verifiedInputs : List (String × Shape) :=
  [("certificateValid", Shape.bytes 1), ("signature", .bytes 64), ("serverValid", .word), ("rx", .word), ("ry", .word)]

def certificateVerified (_ : Unit := ()) : Kernel :=   -- a function: a constant kernel would be built at program start
  let get := lookup verifiedInputs
  let out := ReceiveFirst.certificateVerified ByteAuth.symbolic (get "certificateValid") (get "signature")
    (get "serverValid") (get "rx") (get "ry")
  { name := "receive-certificate-verified", inputs := verifiedInputs, outputs := [priv "verified" (out.getD 0 [])] }

/-! ### PreKeySignalMessage -/

def shapeInputs (size : Nat) : List (String × Shape) := [("message", Shape.bytes size), ("valid", .bytes 1)]

def prekeyShape (size : Nat) : Kernel :=
  let get := lookup (shapeInputs size)
  let out := ReceiveFirst.prekeyShape ByteAuth.symbolic size (get "message") (get "valid")
  { name := "receive-prekey-shape", inputs := shapeInputs size, outputs := [pub "shape" (out.getD 0 [])] }

def openInputs (size : Nat) : List (String × Shape) :=
  [("message", Shape.bytes size), ("valid", .bytes 1), ("messageType", .bytes 1), ("senderIdentity", .bytes 32)]

/-- The sender's base and ratchet keys as words for the field engine, and the
opened prekey ids and Kyber ciphertext. -/
def prekeyOpen (size : Nat) (p : ReceiveFirst.PreKeyShape) : Kernel :=
  let get := lookup (openInputs size)
  let out := ReceiveFirst.prekeyOpen ByteAuth.symbolic p size (get "message") (get "valid") (get "messageType")
    (get "senderIdentity")
  { name := "receive-prekey-open", inputs := openInputs size, outputs := [
      priv "prekeyValid" (out.getD 0 []), bits "basePoint" 255 (out.getD 1 []), bits "ratchetPoint" 255 (out.getD 2 []),
      pub "oneTimePrekeyId" (out.getD 3 []), pub "signedPrekeyId" (out.getD 4 []), pub "kyberPrekeyId" (out.getD 5 []),
      pub "kyberCiphertext" (out.getD 6 [])] }

def signalShape (size : Nat) (p : ReceiveFirst.PreKeyShape) : Kernel :=
  let get := lookup (shapeInputs size)
  let out := ReceiveFirst.signalShape ByteAuth.symbolic p size (get "message") (get "valid")
  { name := "receive-signal-shape", inputs := shapeInputs size, outputs := [pub "shape" (out.getD 0 [])] }

/-! ### Session -/

def sessionInputs (cert size : Nat) (withOneTime : Bool) : List (String × Shape) :=
  [("message", Shape.bytes size), ("prekeyValid", .bytes 1), ("verified", .bytes 1), ("senderIdentity", .bytes 32),
    ("ourIdentity", .bytes 32), ("localAddress", .bytes 17), ("uuid", .bytes 16), ("deviceId", .bytes 1),
    ("dh1", .word), ("dh2", .word), ("dh3", .word)] ++
  (if withOneTime then [("dh4", Shape.word)] else []) ++
  [("kemSecret", .bytes 32), ("receiveAgreement", .word), ("sendAgreement", .word), ("ratchetPublic", .word),
    ("baseValid", .word), ("torsionX", .word), ("torsionY", .word), ("certificate", .bytes cert),
    ("accessKey", .bytes 16), ("requestId", .bytes 8)]

/-- Key agreement, the first ratchet step, authentication and decryption of
the first message, and the contact's records. `status` is 255 exactly when
`prekeyValid` and `verified` are 255, no agreement is zero, the base key is a
torsion-free curve point, the message has the stated layout, its MAC verifies
and its padding is well formed.

* `conversation`: the record the send kernels consume
  (`HybridKernel.conversationBytes cert 80`): our first sending chain with
  counters zero and post-quantum epoch 1; `certificate` is OUR sender
  certificate, `accessKey` the contact's unidentified-access key (not in the
  message: it is derived from the contact's profile key and must be supplied),
  `requestId` the connection's request id.
* `receiver` (236): what later receives need (`ReceiveFirst.session`).
* `plaintext`: length (8) and padded content, input of `receive-text`. -/
def session (cert size : Nat) (p : ReceiveFirst.PreKeyShape) (q : ReceiveFirst.SignalShape) (jump : Nat) : Kernel :=
  let inputs := sessionInputs cert size (p.oneTime != 0)
  let get := lookup inputs
  let out := ReceiveFirst.session AesInverse.symbolic Sha256Ripple.ops ByteAuth.symbolic p q size jump (get "message")
    (get "prekeyValid" ++ get "verified") (get "senderIdentity") (get "ourIdentity") (get "localAddress") (get "uuid")
    (get "deviceId") (get "dh1") (get "dh2") (get "dh3") (get "dh4") (get "kemSecret") (get "receiveAgreement")
    (get "sendAgreement") (get "ratchetPublic") (get "baseValid") (get "torsionX") (get "torsionY") (get "certificate")
    (get "accessKey") (get "requestId")
  { name := "receive-session", inputs, outputs := [
      pub "status" (out.getD 0 []), priv "conversation" (out.getD 1 []), priv "receiver" (out.getD 2 []),
      priv "plaintext" (out.getD 3 [])] }

def textInputs (ciphertext : Nat) : List (String × Shape) := [("plaintext", Shape.bytes (8 + ciphertext))]

/-- The message body (the signup token), released from a plaintext that is
zero unless the session's status was 255. -/
def text (ciphertext capacity : Nat) : Kernel :=
  let out := ReceiveFirst.text ByteAuth.symbolic capacity (lookup (textInputs ciphertext) "plaintext")
  { name := "receive-text", inputs := textInputs ciphertext, outputs := [
      pub "status" (out.getD 0 []), pub "length" (out.getD 1 []), pub "text" (out.getD 2 []),
      pub "layout" (out.getD 3 [])] }

def accessKeyInputs (cert ciphertext : Nat) : List (String × Shape) :=
  [("conversation", Shape.bytes (HybridKernel.conversationBytes cert 80)), ("plaintext", .bytes (8 + ciphertext))]

/-- The contact's unidentified-access key, derived from the profile key in the
message and written into the conversation record (unchanged unless `status`
is 255). `offset` is where the profile-key field starts in the content: the
body's start (4, 5 or 6, the set flag of `receive-text`'s `layout`) plus the
body's length, when the body is the first field and the profile key the
next. -/
def accessKey (cert ciphertext offset : Nat) : Kernel :=
  let get := lookup (accessKeyInputs cert ciphertext)
  let out := ReceiveFirst.withAccessKey Aes.symbolic ByteAuth.symbolic cert offset (get "conversation") (get "plaintext")
  { name := "receive-access-key", inputs := accessKeyInputs cert ciphertext, outputs := [
      pub "status" (out.getD 0 []), priv "conversation" (out.getD 1 [])] }

/-! ### Lookup by name -/

def envelopeOk (size : Nat) : Bool := 120 ≤ size && size ≤ 16384 && framed (size - 81)

/-- The certificate length from its opened prefix, if it is a two-byte varint. -/
def certLength (low high : Nat) : Option Nat :=
  if 128 ≤ low && low < 256 && high < 128 && 0 < high then some (decode2 low high) else none

def contentOk (size cert : Nat) (hint : Bool) : Bool :=
  67 ≤ cert && framed (cert - 66) && cert + 10 ≤ size && framed (size - (5 + cert) - (if hint then 2 else 0))

def preKeyShape? (size : Nat) (widths : List Nat) : Option ReceiveFirst.PreKeyShape :=
  match widths with
  | [oneTime, registration, signed, kyber] =>
      let p : ReceiveFirst.PreKeyShape := ⟨oneTime, registration, signed, kyber⟩
      if oneTime ≤ 5 && 1 ≤ registration && registration ≤ 5 && 1 ≤ signed && signed ≤ 5 && 1 ≤ kyber && kyber ≤ 5 &&
          p.keysAt + 70 + p.tail + 60 ≤ size && size ≤ 16384 && framed (size - (p.keysAt + 70) - p.tail) then some p
      else none
  | _ => none

def signalShape? (signalSize : Nat) (values : List Nat) : Option ReceiveFirst.SignalShape :=
  match values with
  | [counter, previous, low, high, addresses] =>
      let ciphertext := if high = 0 then low else decode2 low high
      let q : ReceiveFirst.SignalShape := ⟨counter, previous, ciphertext, addresses == 1⟩
      if 1 ≤ counter && counter ≤ 5 && 1 ≤ previous && previous ≤ 5 && low < 256 && high < 128 &&
          (high == 0) == (low < 128) && addresses ≤ 1 && 16 ≤ ciphertext && ciphertext % 16 == 0 &&
          q.cipherAt + ciphertext + 8 + (if q.addresses then 38 else 0) + 5 ≤ signalSize &&
          framed (q.pqField signalSize) then some q
      else none
  | _ => none

/-- Kernel named on the command line, with its public shape parameters (see
the header for their meaning):

`receive-envelope-point SIZE`, `receive-unseal-static SIZE`,
`receive-unseal-message SIZE`, `receive-content-shape U C0 C1`,
`receive-content U C0 C1 HINT`, `receive-certificate C0 C1 PRESENT LENGTH`,
`receive-certificate-verified`, `receive-prekey-shape N`,
`receive-prekey-open N P R S K`, `receive-signal-shape N P R S K`,
`receive-session CERT N P R S K CW PW L0 L1 ADDR JUMP`,
`receive-text CIPHERTEXT CAPACITY`. -/
def find (arguments : List String) : Option Kernel :=
  match arguments with
  | [] => none
  | name :: rest =>
      match name, rest.mapM (·.toNat?) with
      | "receive-certificate-verified", some [] => some (certificateVerified ())
      | "receive-envelope-point", some [size] => if envelopeOk size then some (envelopePoint size) else none
      | "receive-unseal-static", some [size] => if envelopeOk size then some (unsealStatic size) else none
      | "receive-unseal-message", some [size] => if envelopeOk size then some (unsealMessage size) else none
      | "receive-content-shape", some [size, low, high] =>
          (certLength low high).bind (fun cert =>
            if contentOk size cert false && size ≤ 16384 then some (contentShape size cert) else none)
      | "receive-content", some [size, low, high, hint] =>
          (certLength low high).bind (fun cert =>
            if hint ≤ 1 && contentOk size cert (hint == 1) && size ≤ 16384 then some (content size cert (hint == 1))
            else none)
      | "receive-certificate", some [low, high, present, length] =>
          (certLength low high).bind (fun cert =>
            if (present == 0 && length == 0) || (present == 255 && 0 < length && length < 128) then
              (ReceiveFirst.certShape cert (if present == 255 then 2 + length else 0)).map (certificate cert)
            else none)
      | "receive-prekey-shape", some [size] =>
          if 1800 ≤ size + 80 && 1720 ≤ size && size ≤ 16384 then some (prekeyShape size) else none
      | "receive-prekey-open", some (size :: widths) => (preKeyShape? size widths).map (prekeyOpen size)
      | "receive-signal-shape", some (size :: widths) => (preKeyShape? size widths).map (signalShape size)
      | "receive-session", some [cert, size, oneTime, registration, signed, kyber, counter, previous, low, high,
          addresses, jump] =>
          (preKeyShape? size [oneTime, registration, signed, kyber]).bind (fun p =>
            (signalShape? (p.signalSize size) [counter, previous, low, high, addresses]).bind (fun q =>
              if cert ≤ 1024 && jump ≤ 16 then some (session cert size p q jump) else none))
      | "receive-text", some [ciphertext, capacity] =>
          if 16 ≤ ciphertext && ciphertext % 16 == 0 && ciphertext ≤ 16384 && 0 < capacity && capacity + 6 ≤ ciphertext then
            some (text ciphertext capacity)
          else none
      | "receive-access-key", some [cert, ciphertext, offset] =>
          if cert ≤ 1024 && 16 ≤ ciphertext && ciphertext % 16 == 0 && ciphertext ≤ 16384 && offset + 34 ≤ ciphertext then
            some (accessKey cert ciphertext offset)
          else none
      | _, _ => none

end TlsMpc.ReceiveKernel
