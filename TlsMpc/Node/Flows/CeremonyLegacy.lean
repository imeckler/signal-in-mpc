import TlsMpc.Node.Flows.Legacy

/-!
# Flow `Ceremony`, legacy implementation (worker ops 80, 81)

Plan 6.2: `Ceremony.secrets/register` move to Lean scripts in S16 (`Flows/Ceremony.lean`; selected
by the agreed group `ceremony`, `Flows/Select.lean`). Each function first consults its override.
-/

namespace TlsMpc.Node.Flow.Ceremony
open TlsMpc.TlsWire TlsMpc.TlsClient

/-- **The account password and the recovery password, made in the engines** from each party's
own randomness (op 80): THIS party's XOR share of each (22 and 32 bytes), different for the two
parties (`maskedPassword`: the XOR is never opened to either). Held as `Secret` (plan 4.2 row 4). -/
def secrets (w : Worker) : M (Secret Bytes) := do
  if let some f := w.overrides.ceremonySecrets then return ← f
  pure (Secret.hide (← Legacy.call w .ceremonySecrets []))

/-- **The registration request into the engines** (op 81): the frame built in the clear (masked
with `mask`), the two passwords inserted at its slots `offsets` (credential, recovery), with the
public tail of the Basic authorization's `NUMBER:`. The reply is the request's buffer handle. -/
def register (w : Worker) (payloadAt : Nat) (offsets : List Nat) (mask tail frame : Bytes) :
    M TlsWorker.BufferHandle := do
  if let some f := w.overrides.ceremonyRegister then return ← f payloadAt offsets mask tail frame
  Legacy.handle (← Legacy.call w .ceremonyRegister (uint 2 payloadAt ++ uint 2 (offsets.getD 0 0) ++
      uint 2 (offsets.getD 1 0) ++ mask ++ [UInt8.ofNat tail.length] ++ tail ++ frame))
    "invalid request handle"

end TlsMpc.Node.Flow.Ceremony
