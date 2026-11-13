import TlsMpc.Node.Flows.Legacy

/-!
# Flow `Account`, legacy implementation (worker ops 46, 47, 53, 54, 55)

Plan 6.2: ops 53, 54 move to the Lean scripts of `TlsMpc/Node/Flows/Account.lean` in S9, 55 in
S10 (`Account.load`: the plan's `Account.open`, `open` being a Lean keyword), 47 and 46 (TEST) in
S16.
-/

namespace TlsMpc.Node.Flow.Account
open TlsMpc.TlsWire TlsMpc.TlsClient

/-- **The account's key into the engines** (op 53): this party's additive share (`Secret`). -/
def key (w : Worker) (share : Secret Bytes) : M Unit := do
  if let some f := w.overrides.accountKey then return ← f share
  let _ ← Legacy.inputOwn w .accountKey share

/-- **Load the account's record** (identity key, credentials, certificate) from its stored blob
(op 55). The worker refuses a blob that does not open (the session ends); nothing is opened. -/
def load (w : Worker) (stored : Bytes) : M Unit := do
  if let some f := w.overrides.accountLoad then return ← f stored
  let _ ← Legacy.call w .accountOpen stored

/-- **Seal the account's record under the nonce `version`** (op 54): `check ‖ ciphertext`. -/
def «seal» (w : Worker) (version : Bytes) : M (Opened .sealedBlob Bytes) := do
  if let some f := w.overrides.accountSeal then return ← f version
  let stored ← Legacy.call w .accountSeal version
  insist (stored.length > 16) "invalid stored account state"
  pure (Reveal.sealedBlob stored)

/-- **This party's XOR share of the account id and password into the engines** (op 47): neither
party can open the authenticated socket alone. -/
def credentials (w : Worker) (share : Secret Bytes) : M Unit := do
  let _ ← Legacy.inputOwn w .accountCredentials share

/-- TEST: **admit the account from the export** (op 46): its identity key (OWN, `Secret`) and its
sender certificate. -/
def admitTest (w : Worker) (identity : Secret Bytes) (certificate : Bytes) : M Unit := do
  let _ ← Legacy.inputOwn w .accountAdmit (identity ++ Secret.hide certificate)

end TlsMpc.Node.Flow.Account
