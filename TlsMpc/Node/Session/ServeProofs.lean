import TlsMpc.Node.Session.Serve
import TlsMpc.Node.Session.LoopProofs

/-!
# P4 over the long-lived send session: ORD-1 and ORD-2 for every run of `serve`

About `Session/Serve.lean`'s `Serve.serveG`, whose instance at `SessionM` and `Serve.serveReal` IS
the deployed `serve`. In the guarded models, with its `deliverJob` the definition of `deliverJob`
(with the deployed `sendSoft`, `refreshSoft`, `commitScratch`: `deliverSends`, `deliverCommits`) and
every other operation any computation that keeps the property (`loadJob`, `notify`, the ticks, the
idle polls, pings and keepalives hand no message request to the worker and commit no scratch):

- `serve_sendsAgreed`: every run of `serve` keeps `SendsAgreed` (ORD-1, both parties);
- `serve_commitsAgreed`: every run keeps `CommitsAgreed` (ORD-2).

T11 for `serve`'s job lines is not a separate theorem: the job's `Report.results` is reset to `[]`
before the job (`Serve.lean`, the `modify` before `loadJob`), set only by `deliverJob`'s tail
(`deliverJob_results`, `resultsTail_spec`), and read into `DaemonLine.jobResult` after
`deliverJob` returned; in between, only `jobRequest` is changed and the clocks are read. A
mechanised version needs the job branch as a function of its own (see the P4 report).

No I/O primitive; no emitter imports this module.
-/

namespace TlsMpc.Node.Session.Events
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.Signal TlsMpc.Node TlsMpc.Node.Bytes TlsMpc.Node.Session

open TlsMpc.Node.Session.Serve (ServeOps serveReal serveG)
open TlsMpc.Node.Session.Send (DeliverOps RefreshOps deliverJobG)

/-- ORD-1's model of `serve`: its `deliverJob` is `deliverSends` (the deployed texts); every other
operation is `rest`'s. -/
def serveSends (E : SendEnv) (rest : ServeOps (Guarded SendsAgreed)) (D : DeliverOps (Guarded SendsAgreed))
    (R : RefreshOps (Guarded SendsAgreed)) : ServeOps (Guarded SendsAgreed) :=
  { rest with deliverJob := deliverJobG (deliverSends E D R) }

/-- **ORD-1 over every run of `serve`.** With the database nodes, every run of the deployed text of
`serve` (each job through the deployed `deliverJob`) keeps `SendsAgreed`. -/
theorem serve_sendsAgreed (E : SendEnv) (rest : ServeOps (Guarded SendsAgreed)) (D : DeliverOps (Guarded SendsAgreed))
    (R : RefreshOps (Guarded SendsAgreed)) (directory : String) (accept : Bytes) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) (hw : SendsAgreed w.log) :
    SendsAgreed ((serveG (serveSends E rest D R) directory accept).1 c st w).2.2.log :=
  (serveG (serveSends E rest D R) directory accept).2 c st w hdb hw

/-- ORD-2's model of `serve`. -/
def serveCommits (E : SendEnv) (rest : ServeOps (Guarded CommitsAgreed)) (D : DeliverOps (Guarded CommitsAgreed))
    (R : RefreshOps (Guarded CommitsAgreed)) : ServeOps (Guarded CommitsAgreed) :=
  { rest with deliverJob := deliverJobG (deliverCommits E D R) }

/-- **ORD-2 over every run of `serve`.** -/
theorem serve_commitsAgreed (E : SendEnv) (rest : ServeOps (Guarded CommitsAgreed)) (D : DeliverOps (Guarded CommitsAgreed))
    (R : RefreshOps (Guarded CommitsAgreed)) (directory : String) (accept : Bytes) (c : Context) (st : State) (w : World)
    (hdb : c.dbClient.isSome) (hw : CommitsAgreed w.log) :
    CommitsAgreed ((serveG (serveCommits E rest D R) directory accept).1 c st w).2.2.log :=
  (serveG (serveCommits E rest D R) directory accept).2 c st w hdb hw

end TlsMpc.Node.Session.Events
