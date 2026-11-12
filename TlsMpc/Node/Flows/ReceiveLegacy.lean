import TlsMpc.Node.Flows.Legacy

/-!
# Flow `Receive`, legacy implementation (worker ops 48, 49, 50, 51)

Plan 6.2: `Receive.take/drop/openFirst/session` (the plan's `open`: a Lean keyword) move to Lean
scripts in S14. A delivered envelope's sealed content goes to the engines unopened (`take`); it is
then opened there as a new contact's first message.
-/

namespace TlsMpc.Node.Flow.Receive
open TlsMpc.TlsWire TlsMpc.TlsClient

/-- **Collect `count` bytes of an authenticated record from `offset` into the held envelope,
unopened** (op 48). -/
def take (w : Worker) (handle offset count : Nat) : M Unit := do
  let held ← Legacy.call w .envelopeTake (uint 8 handle ++ uint 2 offset ++ uint 2 count)
  insist (held.length == 4) "invalid envelope reply"

/-- **Discard the held envelope** (op 49). -/
def drop (w : Worker) : M Unit := Legacy.empty w .envelopeDrop []

/-- **Open the held envelope as a new contact's first message** (op 50), with our identity public
key, the agreed time `now` (the sender certificate's expiry), the server's key and certificate and
the signer's id (public): refused with a status byte, or the prekey ids it names and its Kyber
ciphertext. -/
def openFirst (w : Worker) (identityPublic : Bytes) (now : Nat) (serverKey serverCertificate signerId : Bytes) :
    M FirstMessage := do
  let opened ← Legacy.call w .envelopeOpen (identityPublic ++ uint 8 now ++ serverKey ++
    uint 2 serverCertificate.length ++ serverCertificate ++ uint 2 signerId.length ++ signerId)
  if opened.head? != some 255 then return .refused (Reveal.sessionStatus (opened.headD 0).toNat)
  insist (opened.length == 14 + 1568) "invalid opened prekey message"
  pure (.opened (Reveal.prekeyIds {
    usesOneTime := opened.getD 1 0 == 1
    oneTime := number ((opened.drop 2).take 4)
    signed := number ((opened.drop 6).take 4)
    kyber := number ((opened.drop 10).take 4)
    kyberCiphertext := opened.drop 14 }))

/-- **The new contact's session** (op 51) under the id `contact`, from our prekey private keys and
the KEM secret (OWN, `Secret`), our account's address and the request counter's start: refused
with a status byte, or the message's text. -/
def session (w : Worker) (contact : ContactId) (address : Bytes) (signed oneTime secret : Secret Bytes) :
    M Received := do
  let result ← Legacy.inputOwn w .envelopeSession
    (Secret.hide (uint 16 contact ++ address) ++ signed ++ oneTime ++ secret ++ Secret.hide (uint 8 (2 ^ 63)))
  if result.head? != some 255 then return .refused (Reveal.sessionStatus (result.headD 0).toNat)
  insist (result.length ≥ 3 && result.length == 3 + number ((result.drop 1).take 2)) "invalid received text"
  pure (.text (Reveal.receivedText ((String.fromUTF8? ⟨(result.drop 3).toArray⟩).getD "")))

end TlsMpc.Node.Flow.Receive
