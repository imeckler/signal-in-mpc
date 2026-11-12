import TlsMpc.TlsWorker
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

Nothing here calls the worker; `TlsMpc/Node/Flows/Legacy.lean` does. No I/O primitive; no emitter
imports this module.
-/

namespace TlsMpc.Node.Flow
open TlsMpc.TlsWire

/-- This session's handle on the engines (one per worker process).
- `pipe`: the worker pipe (`TlsWorkerProcess.spawn`), used only by `Flows/Legacy.lean`;
- `used`: the worker operations used so far, in first-use order (the final report's check);
- `active`: the worker's selected connection (operation 90), shared by every view;
- `connection`: `some i` for the view of connection `i` (`on`): its operations select `i` first
  when another one is selected; `none`: no selection (what is not tied to a connection);
- `random`: this party's own randomness (`Channels.random`, plan rule 5). Unused by the legacy
  operations (the worker draws its own); the scripts of S9 onward draw from it. -/
structure Worker where
  pipe : TlsWorker.Rpc
  used : IO.Ref (List Nat)
  active : IO.Ref Nat
  connection : Option Nat
  random : Nat → IO (Secret Bytes)

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

end TlsMpc.Node.Flow
