import TlsMpc.Node.Flows.Legacy

/-!
# Flow `Random`, legacy implementation (worker op 33)

Plan 6.2: `Random.joint` moves to the Lean script of `TlsMpc/Node/Flows/Random.lean` in S9
(`Flows.Random.joint`, with P-RAND); until then the worker's `joint_random` (commit, open, XOR).
Selectable (`SIGNAL_SCRIPTS=random`, `Flows/Select.lean`): the function then runs the script.
-/

namespace TlsMpc.Node.Flow.Random
open TlsMpc.TlsWire TlsMpc.TlsClient

/-- **32 bytes of joint randomness** (op 33): both parties get the same bytes, which neither
chose alone. Used, in the clear, for WebSocket masks, request masks, seal nonces and dealing ids. -/
def joint (w : Worker) : M (Opened .jointRandom Bytes) := do
  if let some f := w.overrides.randomJoint then return ← f
  let random ← Legacy.call w .publicRandom []
  insist (random.length == 32) "invalid joint randomness"
  pure (Reveal.jointRandom random)

end TlsMpc.Node.Flow.Random
