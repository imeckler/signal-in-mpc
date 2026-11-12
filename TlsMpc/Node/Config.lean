/-!
# The controller's configuration (stub)

REORGANIZATION_PLAN.md stage S2 moved `officialProfile` here unchanged from the controller
(`handshake_backend/EmpHybridWork/PublicServiceController.lean`, which opens this namespace and
uses the same name); its `IO.getEnv` moved with it (`scripts/lint_node_baseline.json`). Stage S4
fills this module: every environment variable read through one `Config.read`. No emitter imports
this module.
-/

namespace TlsMpc.Node.Config

/-- `SIGNAL_CLIENT_PROFILE` (the same on both nodes, and for circuit production):
`libsignal` makes what the server sees follow the official clients (CLIENT_FINGERPRINT.md):
libsignal's ClientHello layout, upgrade requests, request JSON, WebSocket pings instead of
keepalive requests, no client-initiated KeyUpdate, each message's timestamp taken when it is
sent; `legacy` (the default until the local harness has passed with `libsignal`) keeps the
original behaviour. -/
def officialProfile : IO Bool := do
  match ← IO.getEnv "SIGNAL_CLIENT_PROFILE" with
  | none => pure false
  | some "legacy" => pure false
  | some "libsignal" => pure true
  | some other => throw (IO.userError s!"SIGNAL_CLIENT_PROFILE must be libsignal or legacy, not {other}")

end TlsMpc.Node.Config
