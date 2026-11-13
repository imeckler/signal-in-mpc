import TlsMpc.Node.Flows.Legacy

/-!
# Flows `Contacts` and `Curve`, legacy implementations (worker ops 36, 37, 38, 40, 44, 52, 63, 66)

Plan 6.2: ops 36, 37, 38, 40, 52, 63 move to the Lean scripts of `TlsMpc/Node/Flows/Contacts*.lean`
in S9 (`Contacts.key/load/seal/evict/assign/loadDevices`: the plan's `open`/`openDevices`, `open`
being a Lean keyword); op 44 (TEST) in S16; op 66 (`Curve.prepareContacts`) in S11.

A contact is named by its public id; the engines hold its key and state (today in the worker's
table, after S9 in the Lean contact table of `Flows/ContactsTable.lean`), so no handle crosses
this API.
-/

namespace TlsMpc.Node.Flow
open TlsMpc.TlsWire TlsMpc.TlsClient

namespace Contacts

/-- **A contact's key into the engines** (op 36): this party's additive share (`Secret`), under
the contact's public id. -/
def key (w : Worker) (contact : ContactId) (share : Secret Bytes) : M Unit := do
  if let some f := w.overrides.contactsKey then return ← f contact share
  let _ ← Legacy.inputOwn w .contactKey (Secret.hide (uint 16 contact) ++ share)

/-- **Load a contact's state from its stored blob** `version ‖ check ‖ ciphertext` (op 37, one
established record): whether it opened under the contact's key (if not, the contact stays
unloaded). -/
def load (w : Worker) (contact : ContactId) (stored : Bytes) : M (Opened .blobAccepted Bool) := do
  if let some f := w.overrides.contactsLoad then return ← f contact stored
  let reply ← Legacy.call w .contactOpen (uint 16 contact ++ stored)
  pure (Reveal.blobAccepted (reply != [0]))

/-- **Load a contact with a device list** (op 63): `kinds` are its entries' kinds (public, stored
in the clear), `body` the blob without them. Whether it opened under the contact's key. -/
def loadDevices (w : Worker) (contact : ContactId) (kinds : List Nat) (body : Bytes) :
    M (Opened .blobAccepted Bool) := do
  if let some f := w.overrides.contactsLoadDevices then return ← f contact kinds body
  let reply ← Legacy.call w .devicesOpen (uint 16 contact ++ [UInt8.ofNat kinds.length] ++ kinds.map UInt8.ofNat ++ body)
  pure (Reveal.blobAccepted (reply != [0]))

/-- **Seal a contact's current state under the nonce `version`** (op 38): `check ‖ ciphertext`. -/
def «seal» (w : Worker) (contact : ContactId) (version : Bytes) : M (Opened .sealedBlob Bytes) := do
  if let some f := w.overrides.contactsSeal then return ← f contact version
  let stored ← Legacy.call w .contactSeal (uint 16 contact ++ version)
  insist (stored.length > 16) "invalid stored contact state"
  pure (Reveal.sealedBlob stored)

/-- **Remove a contact from the engines** (op 40; its entry is kept, so its id is not reused for a
session in this worker). -/
def evict (w : Worker) (contact : ContactId) : M Unit := do
  if let some f := w.overrides.contactsEvict then return ← f contact
  let _ ← Legacy.call w .contactEvict (uint 16 contact)

/-- **A provisional contact takes the id its signup token names** (op 52): whether it did. -/
def assign (w : Worker) (provisional contact : ContactId) : M (Opened .assignStatus Bool) := do
  if let some f := w.overrides.contactsAssign then return ← f provisional contact
  let reply ← Legacy.call w .contactAssign (uint 16 provisional ++ uint 16 contact)
  pure (Reveal.assignStatus (reply == [255]))

/-- TEST: **admit a contact from the export** (op 44): its record (`Secret`) under its id. -/
def admitTest (w : Worker) (contact : ContactId) (record : Secret Bytes) : M Unit := do
  let _ ← Legacy.inputOwn w .contactAdmit (Secret.hide (uint 16 contact) ++ record)

end Contacts

namespace Curve

/-- **Prepare loaded contacts for sending** (op 66): their per-session curve work, in the same
field rounds. One status byte per contact (255: prepared). -/
def prepareContacts (w : Worker) (contacts : List ContactId) : M (Opened .prepareStatus Bytes) := do
  if let some f := w.overrides.curvePrepareContacts then return ← f contacts
  pure (Reveal.prepareStatus (← Legacy.call w .contactsPrepare (contacts.flatMap (uint 16))))

end Curve
end TlsMpc.Node.Flow
