import TlsMpc.Node.Flows.Legacy

/-!
# Flow `Upgrade`, legacy implementation (worker ops 45, 32; the fixture's op 19)

Plan 6.2: op 45 `Upgrade.anonymous` (the plan's `Upgrade.public`; `public` is a Lean keyword)
moves to the Lean script of `TlsMpc/Node/Flows/Upgrade.lean` in S9; op 32
`Upgrade.authenticated` in S16. Op 19 belongs to the TEST fixture session, removed in S7.
-/

namespace TlsMpc.Node.Flow
open TlsMpc.TlsWire TlsMpc.TlsClient

namespace Upgrade

/-- **The unauthenticated WebSocket upgrade** (op 45): a nonce of joint randomness (16 bytes) and
its RFC 6455 accept value (28). The upgrade request is built from the nonce in the clear. -/
def anonymous (w : Worker) : M (Opened .upgradeNonce (Bytes × Bytes)) := do
  if let some f := w.overrides.upgradeAnonymous then return ← f
  let upgrade ← Legacy.call w .publicUpgrade []
  insist (upgrade.length == 44) "invalid public upgrade receipt"
  pure (Reveal.upgradeNonce (upgrade.take 16) (upgrade.drop 16))

/-- **The authenticated WebSocket upgrade** (op 32), with the credentials already in the engines
(`Account.credentials`): the request's buffer handle and size (to seal and send) and the accept
value the server must answer with. `state`: 1, or the TEST fixture's catalogue state. -/
def authenticated (w : Worker) (state : Nat) :
    M (TlsWorker.BufferHandle × Nat × Opened .upgradeAccept Bytes) := do
  let upgrade ← Legacy.call w .providerUpgradeOpen (uint 8 state)
  insist (upgrade.length == 38) "invalid upgrade receipt"
  pure (⟨number (upgrade.take 8)⟩, number ((upgrade.drop 8).take 2), Reveal.upgradeAccept (upgrade.drop 10))

end Upgrade

namespace Fixture

/-- TEST fixture session only (no export; removed in S7): the fixture provider's catalogue state
(op 19), public. -/
def catalogue (w : Worker) : M Nat := do
  let catalogue ← Legacy.call w .providerCatalogue []
  insist (catalogue.length ≥ 10) "invalid provider catalogue"
  let state := number (catalogue.take 8)
  let count := number ((catalogue.drop 8).take 2)
  insist (state != 0 && count == 4 && catalogue.length == 10+8*count) "fixture catalogue changed"
  pure state

end Fixture
end TlsMpc.Node.Flow
