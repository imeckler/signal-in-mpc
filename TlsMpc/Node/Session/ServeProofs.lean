import TlsMpc.Node.Session.Serve
import TlsMpc.Node.Session.LoopProofs

/-!
# P4 over the long-lived send session: ORD-1 and ORD-2 for every run of `serve`

A twin of `Session/Serve.lean`'s `serve`, proved equal to the deployed definition by `rfl`
(`serve_deployed`). In the guarded models, with its `deliverJob` the deployed text of `deliverJob`
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

/-- Every effect of `serve` besides `State` and `Context`. -/
structure ServeOps (m : Type → Type) where
  liftResult : {α : Type} → Except String α → m α
  openAll : Bytes → m PublicReceive.State
  report : Channels → DaemonLine → m Unit
  agreedClock : m Nat
  nextJob : Channels → String → m (Option Channels.Real.Job)
  stopAsked : Channels → String → m Bool
  clock : Channels → m Nat
  peer : PeerMsg → m PeerMsg
  monotonic : Channels → m Nat
  readMessage : Channels → String → m String
  loadJob : String → String → m (List Nat)
  notify : List Nat → String → Nat → m (List (Nat × Bytes))
  agreedNow : m Nat
  deliverJob : List (Nat × Bytes) → List Nat → Option String → Option String → PublicReceive.State → m Nat
  poll : Flow.Worker → m Flow.Polled
  reconnect : m Unit
  setSlot : Connection → Option Bytes → m Unit
  drainOne : PublicReceive.State → m (PublicReceive.State × Bool)
  saveState : PublicReceive.State → m Unit
  joint : Flow.Worker → m (Opened .jointRandom Bytes)
  sendPublic : Bytes → m Unit
  nextId : m Nat
  awaitSoft : Nat → PublicReceive.State → m (PublicReceive.State × Bool)
  sleep : Channels → Nat → m Unit
  log : Channels → LogLine → m Unit

/-- The deployed operations. -/
def serveReal : ServeOps SessionM where
  liftResult x := liftResult x
  openAll := openAll
  report ch line := ch.report line
  agreedClock := agreedClock
  nextJob ch d := ch.nextJob d
  stopAsked ch d := ch.stopAsked d
  clock ch := ch.clock
  peer := peer
  monotonic ch := ch.monotonic
  readMessage ch path := ch.readMessage path
  loadJob := Serve.loadJob
  notify := Send.notify
  agreedNow := agreedNow
  deliverJob := Send.deliverJob
  poll w := Flow.Server.poll w
  reconnect := reconnect
  setSlot conn v := io (conn.slot.set v)
  drainOne := drainOne
  saveState := saveState
  joint w := Flow.Random.joint w
  sendPublic := sendPublic
  nextId := nextId
  awaitSoft := awaitSoft
  sleep ch ms := ch.sleep ms
  log ch line := ch.log line

section Twins
variable {m : Type → Type} [Monad m] [MonadExceptOf String m] [MonadStateOf State m] [MonadReaderOf Context m]

def serveG (o : ServeOps m) (directory : String) (accept : Bytes) : m Nat := do
  let c ← read
  let first ← o.openAll accept
  let count := max c.sendCircuits 1
  modifyReportG fun r => { r with recoveryUsed := true }
  o.report c.ch (.ready count)
  let opened ← o.agreedClock
  let mut lastUsed : Array Nat := Array.replicate count opened
  let mut lastJob := opened
  let mut finishedJobs : List String := []
  let mut served := 0
  let mut jobsDone := 0
  let mut pings := 0
  let mut running := true
  while running do
    -- The job this party's daemon handed over, if any (one already served is ignored until the
    -- daemon removes its file).
    let job := (← o.nextJob c.ch directory).filter (fun job => !finishedJobs.contains job.name)
    let stopping ← o.stopAsked c.ch directory
    let clock ← o.clock c.ch
    let named := job.map (fun job => TlsWire.hash job.name.toUTF8.data.toList)
    let (theirJob, theirStop, theirClock) ← match ← o.peer (.serveTick named stopping clock) with
      | .serveTick theirJob theirStop theirClock => pure (theirJob, theirStop, theirClock)
      | _ => throw "invalid serve tick"
    let now ← o.liftResult (Node.Policy.Clock.agree clock theirClock)
    if named.isSome && theirJob == named then
      let (jobName, requestPath, messagePath, journalPath) :=
        match job with | some j => (j.name, j.request, j.message, j.journal) | none => ("", "", "", "")
      let begun ← o.monotonic c.ch
      let text ← o.readMessage c.ch messagePath
      modify fun st => { st with
        jobRequest := some requestPath, bodies := [], stamped := []
        report := { st.report with results := [], recoveryLog := [], circuitSends := [] } }
      let contactsOfJob ← o.loadJob requestPath text
      let jobInputs ← o.notify contactsOfJob text (← o.agreedNow)
      let delivered ← if jobInputs.isEmpty then pure 0
        else o.deliverJob jobInputs contactsOfJob (some jobName) (some journalPath) first
      modify fun st => { st with jobRequest := none }
      served := served + jobInputs.length
      jobsDone := jobsDone + 1
      finishedJobs := (jobName :: finishedJobs).take 64
      let after ← o.agreedClock
      lastUsed := Array.replicate count after
      lastJob := after
      let report := (← get).report
      let ended ← o.monotonic c.ch
      let jobResult : JobResult := {
        job := jobName
        results := report.results
        unknown := (report.absent.filter (fun entry => !entry.2)).map (·.1)
        notYetReadable := (report.absent.filter (·.2)).map (·.1)
        recovery := report.recoveryLog
        messages := jobInputs.length
        delivered := delivered
        milliseconds := ended - begun
        sessionMessages := served
        sessionJobs := jobsDone }
      o.report c.ch (.jobResult jobResult)
    else if stopping || theirStop then
      running := false
    else
      for index in [0:count] do
        modifyPoolG fun p => { p with current := index }
        let mut s := (← get).pool.states.getD index first
        -- Closed by the server or the proxy while idle: replaced now, not at the next send.
        let polled ← o.poll (c.w.on index)
        if let .closed := polled then
          o.reconnect
          lastUsed := lastUsed.set! index now
          continue
        if let .record wire := polled then
          o.setSlot ((← get).pool.connection index) (some wire)
          let (next, alive) ← o.drainOne s
          if !alive then
            o.reconnect
            lastUsed := lastUsed.set! index now
            continue
          s := next
          o.saveState s
        if now ≥ lastUsed.getD index 0 + 25000 then
          let random := (← o.joint c.w).val
          if c.official then
            pings := pings + 1
            o.sendPublic (toBytes (PublicReceive.ping (pings % 256) (toBits (random.take 4))))
          else
            let id ← o.nextId
            o.sendPublic (toBytes (← o.liftResult (PublicReceive.keepalive id (toBits (random.take 4)))))
            let (next, alive) ← o.awaitSoft 64 (PublicReceive.expect s id)
            if alive then o.saveState next else o.reconnect
          lastUsed := lastUsed.set! index now
      -- A quarter of a second between ticks; a second after a minute without a job.
      o.sleep c.ch (if now > lastJob + 60000 then 1000 else 250)
  o.log c.ch (.serveEnded jobsDone served)
  pure served

end Twins

theorem serve_deployed : @Serve.serve = serveG (m := SessionM) serveReal := rfl

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
