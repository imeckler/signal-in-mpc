import TlsMpc.TlsWorkerPipe
import TlsMpc.Node.Flows.Context

/-!
# `Legacy.call`: a worker operation, for the legacy flow implementations (stage S6)

The one way the flow implementations of `TlsMpc/Node/Flows/*Legacy.lean` reach the worker: an
operation code and its payload on the pipe. Each call records the operation (`Worker.operations`)
and, on a connection's view (`Worker.on`), first selects that connection (operation 90) when
another one is selected, exactly as the controller's `TlsWorker.onConnection` did.

`scripts/lint_node.py` (check `flow-calls`) allows `.call` on the pipe, `Secret.inputOwn` and the
`Reveal.*` wrappers only in this file, the `*Legacy.lean` flow files, and their definitions
(`Secret.lean`, `Reveal.lean`; `Channels.lean` for operation 39, the peer channel). Deleted with
the last legacy flow (stage S16). No I/O primitive; no emitter imports this module.
-/

namespace TlsMpc.Node.Flow
open TlsMpc.TlsWire TlsMpc.TlsClient

/-- The pipe with every call recorded in `used` (first use order), as the controller recorded it. -/
def Worker.recording (w : Worker) : TlsWorker.Rpc :=
  { w.pipe with call := fun op input => do
      let code := TlsWorkerPipe.code op
      liftM (w.used.modify (fun codes => if codes.contains code then codes else codes ++ [code]) : IO Unit)
      w.pipe.call op input }

/-- The worker's exchange (operation 39), for `Channels.exchange` (the peer channel) until the
control link moves to Rust (S8). No connection is selected for it. -/
def Worker.link (w : Worker) : TlsWorker.Rpc := w.recording

namespace Legacy

/-- **A worker operation**: on a connection's view, its connection is selected first (operation
90, an empty reply) when another one is selected. -/
def call (w : Worker) (op : TlsWorker.Operation) (input : Bytes) : M Bytes := do
  if let some index := w.connection then
    if (← liftM (w.active.get : IO Nat)) != index then
      insist (index < 64) "connection index"
      let output ← w.recording.call .useConnection [UInt8.ofNat index]
      insist output.isEmpty "unexpected worker response payload"
      liftM (w.active.set index : IO Unit)
  w.recording.call op input

/-- **A flow operation performed by a selected script** (`Flows/Select.lean`): recorded among the
operations used under the legacy operation's code, as if the pipe had carried it, so the final
report's check (`Main.session`: the send operations were used) counts the operations a session
performed, however they ran. The script's own pipe traffic is recorded too (op 93). -/
def note (w : Worker) (code : Nat) : M Unit :=
  liftM (w.used.modify (fun codes => if codes.contains code then codes else codes ++ [code]) : IO Unit)

/-- An operation whose reply must be empty (`TlsWorker.emptyReply`). -/
def empty (w : Worker) (op : TlsWorker.Operation) (input : Bytes) : M Unit := do
  let output ← call w op input
  insist output.isEmpty "unexpected worker response payload"

/-- An operation that takes this party's own private input (`Secret.inputOwn`, plan 4.1): the
value goes into the engines and stays there. Not tied to a connection. -/
def inputOwn (w : Worker) (op : Secret.OwnInput) (input : Secret Bytes) : M Bytes :=
  Secret.inputOwn w.recording op input

/-- A worker buffer handle in a reply (8 bytes, nonzero): a request or payload to seal and send. -/
def handle (reply : Bytes) (error : String) : M TlsWorker.BufferHandle := do
  insist (reply.length == 8 && number reply != 0) error
  pure ⟨number reply⟩

end Legacy
end TlsMpc.Node.Flow
