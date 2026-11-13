import TlsMpc.TlsWorker
import TlsMpc.TlsApplication
import TlsMpc.Signal.BundleResponse
import TlsMpc.Node.Secret
import TlsMpc.Node.Reveal

/-!
# The flow API's context and result types (REORGANIZATION_PLAN.md stage S6)

`Flow.Worker` is what every flow function takes first: this session's handle on the engines.
Today it wraps the worker pipe (`TlsWorker.Rpc`); the flows behind it are legacy worker
operations (`TlsMpc/Node/Flows/*Legacy.lean`). When a flow becomes a Lean script (stages S9-S16)
its implementation runs the script through this same value (the engine interpreter's state and
this party's randomness are added here), so no caller changes. The design is at the top of
`TlsMpc/Node/Flow.lean`.

THE SELECTION (`Flows/Select.lean`): `Worker.overrides` holds the script implementations of the
flow functions the session selected by the agreed setting `SIGNAL_SCRIPTS` (`Config.Agreed.scripts`);
each legacy flow function first consults its entry (`some`: the script implementation; `none`, the
default: the legacy operation). The entries close over the session's script runner
(`Flows/Runner.lean`), so the types here mention only the flow API's own types. A worker made by
`Worker.start` has none: every flow is legacy, as before.

Nothing here calls the worker; `TlsMpc/Node/Flows/Legacy.lean` does. No I/O primitive; no emitter
imports this module.
-/

namespace TlsMpc.Node.Flow
open TlsMpc.TlsWire

/-! ## Result types of the flows -/

/-- One poll of the selected connection (`Flow.Server.poll`, op 17): a record that arrived,
nothing yet, or the server or the proxy closed the connection. Server bytes, public. -/
inductive Polled where
  | record (wire : Bytes)
  | nothing
  | closed

/-- A delivered envelope opened as a new contact's first message (`Flow.Receive.openFirst`,
op 50): refused with a status byte, or its public part. -/
inductive FirstMessage where
  | refused (status : Opened .sessionStatus Nat)
  | opened (ids : Opened .prekeyIds PrekeyIds)

/-- A new contact's session from its first message (`Flow.Receive.session`, op 51): refused with a
status byte, or the message's text. -/
inductive Received where
  | refused (status : Opened .sessionStatus Nat)
  | text (text : Opened .receivedText String)

/-! ## The selected script implementations -/

/-- **The script implementations a session selected** (`Flows/Select.lean`): each `some` replaces
its flow function's legacy operation(s); `none` (the default) keeps them. A function of a
connection's view takes the view's connection index. Same argument and result types as the flow
functions (the selection changes no caller). -/
structure Overrides where
  randomJoint : Option (TlsClient.M (Opened .jointRandom Bytes)) := none
  upgradeAnonymous : Option (TlsClient.M (Opened .upgradeNonce (Bytes × Bytes))) := none
  tlsBackend : Option (Option Nat → TlsClient.Backend Unit) := none
  tlsApplicationBackend : Option (Option Nat → TlsApplication.Backend TlsWorker.BufferHandle) := none
  tlsPublicBuffer : Option (Option Nat → Bytes → TlsClient.M TlsWorker.BufferHandle) := none
  tlsRecordLength : Option (Option Nat → Nat → TlsClient.M (Opened .serverBytes (Nat × Bytes))) := none
  tlsRevealRange : Option (Option Nat → Nat → Nat → Nat → TlsClient.M (Opened .serverBytes (Nat × Bytes))) := none
  contactsKey : Option (ContactId → Secret Bytes → TlsClient.M Unit) := none
  contactsLoad : Option (ContactId → Bytes → TlsClient.M (Opened .blobAccepted Bool)) := none
  contactsLoadDevices : Option (ContactId → List Nat → Bytes → TlsClient.M (Opened .blobAccepted Bool)) := none
  contactsSeal : Option (ContactId → Bytes → TlsClient.M (Opened .sealedBlob Bytes)) := none
  contactsEvict : Option (ContactId → TlsClient.M Unit) := none
  contactsAssign : Option (ContactId → ContactId → TlsClient.M (Opened .assignStatus Bool)) := none
  /-- TEST: op 44 (`Contacts.admitTest`, J23). -/
  contactsAdmitTest : Option (ContactId → Secret Bytes → TlsClient.M Unit) := none
  /-- Op 91's script half (J22): the connection's script TLS state replaced by a fresh one, for the
  view's connection index; `Flow.Server.reset` sends the socket half. -/
  serverReset : Option (Option Nat → TlsClient.M Unit) := none
  accountKey : Option (Secret Bytes → TlsClient.M Unit) := none
  accountLoad : Option (Bytes → TlsClient.M Unit) := none
  accountSeal : Option (Bytes → TlsClient.M (Opened .sealedBlob Bytes)) := none
  accountCredentials : Option (Secret Bytes → TlsClient.M Unit) := none
  accountAdmitTest : Option (Secret Bytes → Bytes → TlsClient.M Unit) := none
  /-- Op 32 on a connection's view (the view's connection index) with the state argument. -/
  upgradeAuthenticated :
    Option (Option Nat → Nat → TlsClient.M (TlsWorker.BufferHandle × Nat × Opened .upgradeAccept Bytes)) := none
  curvePrepareContacts : Option (List ContactId → TlsClient.M (Opened .prepareStatus Bytes)) := none
  sendSeal : Option (ContactId → Bytes → TlsClient.M (Opened .sealedEnvelope (Option (Nat × List Bytes)))) := none
  sendSealDevices :
    Option (ContactId → Bytes → Bytes → Nat → TlsClient.M (Opened .sealedEnvelope (Option (Nat × List Bytes)))) := none
  sendRequest : Option (ContactId → List Nat → Bytes → Bytes → TlsClient.M TlsWorker.BufferHandle) := none
  sendRequestDevices :
    Option (ContactId → Nat → List Nat → Nat → Bytes → Bytes → TlsClient.M TlsWorker.BufferHandle) := none
  receiveTake : Option (Nat → Nat → Nat → TlsClient.M Unit) := none
  receiveDrop : Option (TlsClient.M Unit) := none
  receiveOpenFirst : Option (Bytes → Nat → Bytes → Bytes → Bytes → TlsClient.M FirstMessage) := none
  receiveSession :
    Option (ContactId → Bytes → Secret Bytes → Secret Bytes → Secret Bytes → TlsClient.M Received) := none
  refreshFetch : Option (ContactId → Nat → List Nat → Bytes → Bytes → TlsClient.M TlsWorker.BufferHandle) := none
  refreshTake : Option (Nat → Nat → Nat → TlsClient.M Unit) := none
  refreshDrop : Option (TlsClient.M Unit) := none
  refreshShape : Option (TlsClient.M (Option (Opened .bundleShape (List Bool)))) := none
  refreshEstablish : Option (ContactId → Nat → Nat → Nat → Nat → Nat → Bool →
    TlsMpc.Signal.BundleResponse.Widths → TlsClient.M (Opened .deviceStatus Bytes)) := none
  refreshScratchSeal : Option (ContactId → Bytes → TlsClient.M (Opened .sealedBlob Bytes)) := none
  refreshScratchCommit : Option (ContactId → TlsClient.M Unit) := none

/-! ## The context -/

/-- This session's handle on the engines (one per worker process).
- `pipe`: the worker pipe (`TlsWorkerProcess.spawn`), used only by `Flows/Legacy.lean`;
- `used`: the worker operations used so far, in first-use order (the final report's check);
- `active`: the worker's selected connection (operation 90), shared by every view;
- `connection`: `some i` for the view of connection `i` (`on`): its operations select `i` first
  when another one is selected; `none`: no selection (what is not tied to a connection);
- `random`: this party's own randomness (`Channels.random`, plan rule 5). Unused by the legacy
  operations (the worker draws its own); the scripts of S9 onward draw from it;
- `overrides`: the selected script implementations (`Flows/Select.lean`; none by default). -/
structure Worker where
  pipe : TlsWorker.Rpc
  used : IO.Ref (List Nat)
  active : IO.Ref Nat
  connection : Option Nat
  random : Nat → IO (Secret Bytes)
  overrides : Overrides := {}

namespace Worker

/-- The flow context of a freshly spawned worker; connection 0 is selected. -/
def start (pipe : TlsWorker.Rpc) (random : Nat → IO (Secret Bytes)) : IO Worker := do
  pure { pipe, used := ← IO.mkRef [], active := ← IO.mkRef 0, connection := none, random }

/-- The same worker, every operation made on connection `index` (selected first when another
connection is selected; all controllers select at the same points, as every request is agreed). -/
def on (w : Worker) (index : Nat) : Worker := { w with connection := some index }

/-- The worker operations used so far (codes, first use order): the final report's check that a
send session used the send operations. -/
def operations (w : Worker) : IO (List Nat) := w.used.get

end Worker

end TlsMpc.Node.Flow
