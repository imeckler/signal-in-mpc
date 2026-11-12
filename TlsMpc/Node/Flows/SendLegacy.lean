import TlsMpc.Node.Flows.Legacy

/-!
# Flow `Send`, legacy implementation (worker ops 41, 42, 61, 62)

Plan 6.2: `Send.seal/request/sealDevices/requestDevices` move to Lean scripts in S13. The text is
public; the engines produce and open the sealed-sender envelope(s), the request frame is built in
the clear (`PublicRequest`), and the engines insert the contact's private fields (recipient, access
key, device and registration ids) into the frame's slots and return the request's buffer handle.
-/

namespace TlsMpc.Node.Flow.Send
open TlsMpc.TlsWire TlsMpc.TlsClient

/-- **One sealed-sender envelope to a contact** (op 41) for the built message `built` (public):
`none` when the contact's state cannot produce a message (nothing changed), else the message's
timestamp and its envelope (one). The contact's state has advanced. -/
def «seal» (w : Worker) (contact : ContactId) (built : Bytes) :
    M (Opened .sealedEnvelope (Option (Nat × List Bytes))) := do
  let sealed ← Legacy.call w .contactSend (uint 16 contact ++ built)
  if sealed == [0] then return Reveal.sealedEnvelope none
  insist (sealed.length ≥ 10) "invalid sealed envelope reply"
  let timestamp := number (sealed.take 8)
  let length := number ((sealed.drop 8).take 2)
  insist (0 < length && length ≤ sealed.length - 10) "invalid sealed envelope length"
  pure (Reveal.sealedEnvelope (some (timestamp, [(sealed.drop 10).take length])))

/-- **One envelope per device** of a contact with a device list (op 61), all for `built`;
`address` is our own account's (public). `none` when the contact's state cannot produce a
message; else the timestamp and the `devices` envelopes in order. -/
def sealDevices (w : Worker) (contact : ContactId) (address built : Bytes) (devices : Nat) :
    M (Opened .sealedEnvelope (Option (Nat × List Bytes))) := do
  let sealed ← Legacy.call w .devicesSend (uint 16 contact ++ address ++ built)
  if sealed == [0] then return Reveal.sealedEnvelope none
  insist (sealed.length ≥ 10) "invalid sealed envelopes reply"
  let timestamp := number (sealed.take 8)
  let mut rest := sealed.drop 8
  let mut envelopes : List Bytes := []
  for _ in [0:devices] do
    let length := number (rest.take 2)
    insist (0 < length && length + 2 ≤ rest.length) "invalid sealed envelope length"
    envelopes := envelopes ++ [(rest.drop 2).take length]
    rest := rest.drop (2 + length)
  insist rest.isEmpty "invalid sealed envelopes reply"
  pure (Reveal.sealedEnvelope (some (timestamp, envelopes)))

/-- **The send's request into the engines** (op 42): the frame built in the clear (`frame`, masked
with `mask`), its private slots at `offsets`; the contact's fields are inserted there. The reply is
the request's buffer handle, to seal and send. -/
def request (w : Worker) (contact : ContactId) (offsets : List Nat) (mask frame : Bytes) :
    M TlsWorker.BufferHandle := do
  Legacy.handle (← Legacy.call w .contactRequest (uint 16 contact ++ offsets.flatMap (uint 2) ++ mask ++ frame))
    "invalid request handle"

/-- **The request of a send to several devices** (op 62): as `request`, with the payload's start,
the slots' offsets (two for the contact, then per device) and the device count. -/
def requestDevices (w : Worker) (contact : ContactId) (payloadAt : Nat) (offsets : List Nat) (devices : Nat)
    (mask frame : Bytes) : M TlsWorker.BufferHandle := do
  Legacy.handle (← Legacy.call w .devicesRequest (uint 16 contact ++ uint 2 payloadAt ++ uint 2 (offsets.getD 0 0) ++
      uint 2 (offsets.getD 1 0) ++ [UInt8.ofNat devices] ++ (offsets.drop 2).flatMap (uint 2) ++ mask ++ frame))
    "invalid request handle"

end TlsMpc.Node.Flow.Send
