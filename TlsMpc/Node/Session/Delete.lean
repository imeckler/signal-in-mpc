import TlsMpc.Node.Channels

/-!
# The application's delete request (REORGANIZATION_PLAN.md stage S7)

The subcommand `db-delete PARTY REQUEST`: the application's signed delete request, which this party
submits to the database nodes; they act once both parties have. Repeated until all but one node has
confirmed. Not a two-party session (no worker): it runs before a session's channels exist, on
`Channels.Real` directly.

Moved from the controller's `main` (stage S7), unchanged. No I/O primitive.
-/

namespace TlsMpc.Node.Session.Delete
open TlsMpc TlsMpc.TlsClient TlsMpc.Node

/-- **Submit the delete request** (`test`: the controller was started with `--test`). -/
def run (test : Bool) (party request : String) : IO Unit := do
  let config ← Config.read test
  Channels.Real.runIO (do
    for _ in [0:40] do
      let run ← Channels.Real.db config party (.delete request) (context := "")
      unless run.ok do throw s!"database client delete: {run.stderr}"
      if ← Channels.Real.deleteAcknowledged config then
        liftM (Channels.Real.report .deleted : IO Unit)
        return
      liftM (Channels.Real.sleep 500 : IO Unit)
    throw "the database nodes did not confirm the delete")

end TlsMpc.Node.Session.Delete
