import TlsMpc.Node.Session.DeliverProofs

/-!
# P4: a device refresh (`refreshContact`, `refreshSoft`) and ORD-2 inside it

`Session/Send.lean` defines `Send.refreshContactG` (the path without recovery) and
`Send.refreshSoftG` (the recovery path) over any monad, their effects the fields of
`Send.RefreshOps`; the deployed `refreshContact`, `refreshSoft` are these definitions at `SessionM`
and `Send.refreshReal`. Both reach the scratch's commit only through the operation
`commitScratch`. Their properties are proved where the loops that call them are
(`LoopProofs.lean`): with `commitScratch` the model of the deployed one with its ORD-2 proof
(`commitScratchCommits`, from `commitScratch_agreed`) or with its proof that it hands no request to
the worker (`commitScratchKeeps`, from `commitScratch_keeps`), and every other operation any
computation that keeps the property (`refreshWith`), both refreshes are `Guarded CommitsAgreed`,
`Guarded SendsAgreed`, `Guarded SendsAcked` values by their type, whatever their `for` loops do: a
refresh commits only through `commitScratch` and never sends a message (its prekey fetch is not a
message request).

(Until 2026-11-12 this file held twins of the two functions, proved equal to the deployed ones by
`rfl`; the definitions are now the deployed functions themselves.)

No I/O primitive; no emitter imports this module.
-/
