import TlsMpc.Node.Session.Send

/-!
# The long-lived send session (SIGNAL_SERVE_DIR = DIR; node_daemon/README.md; plan stage S7)

The connections are opened once and kept; the daemon hands over one job at a time (one signed
notify: DIR/job.json, `{"job", "request", "message", "journal"}`, written whole) and reads one result
line per job on standard output (`DaemonLine.jobResult`: the same per-id results the one-notify
session reports, agreed the same way). Between jobs the session ticks: the two controllers exchange
which job each was handed (its name's hash), whether its daemon asks the session to end (DIR/stop),
and their clocks. A job runs when both were handed the same one; the session ends cleanly, between
jobs, when either daemon asks. While idle, each connection is polled (a closed one is replaced at
once; a record that arrived is read and answered) and kept alive after 25 s without traffic
(WebSocket ping under the libsignal profile, as libsignal; otherwise a keepalive request, awaited).
A job's failure is the session's (as for the one-notify session); the daemon then starts a new
session, which resumes from the journals. What is kept from job to job: the open connections and
their request counters, the contacts' loaded state and preparation (`loadJob`), the account, the
circuits.

Moved from the controller's `main` (stage S7), same operations and order. No I/O primitive.
-/

namespace TlsMpc.Node.Session.Serve
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.Node TlsMpc.Node.Bytes TlsMpc.Node.Session

/-- One job's contacts. As the daemon's one-notify session does at its start, for the ids of the
job's signed request: read them from the database nodes under that request (which also authorises
the write-backs), compare with the other party what the nodes do not hold or do not serve yet (that
id's result, `Report.absent`), and load the rest. A contact the engines still hold from an earlier
job is kept, with its per-session preparation, when the nodes' version of its state is the version
this session holds (`Contacts.versions`): the engines then hold what was stored under that version,
or are at most one unacknowledged store ahead of it (a counter gap, never a key used twice).
Otherwise (another version, or not held) it is evicted and loaded from the nodes' blob. Returns the
job's contacts in the request's order. -/
def loadJob (requestPath text : String) : SessionM (List Nat) := do
  let c ← read
  let w := c.w
  let request ← liftResult (← c.ch.readRequest requestPath)
  let ids := request.ids
  insist (!ids.isEmpty) "the notify request lists no ids"
  let signedFor ← liftResult (fromHex request.messageHash)
  insist (signedFor == TlsWire.hash text.toUTF8.data.toList) "the message is not the one the notify request was signed for"
  -- TEST: an id of the export that the database nodes do not hold yet is created from it.
  let records ← match c.exportPath with
    | some path => do pure (← liftResult (← c.ch.readExport path)).2.2
    | none => pure []
  let wanted := ids.map (fun id => (id, (records.find? (·.1 == id)).map (·.2)))
  let (readJson, sharesJson) ← dbRead (.request requestPath) "contacts"
  let waiting := readJson.notYetReadable
  let gone := wanted.filterMap (fun (contact, record) =>
    if waiting.contains (toString contact) then some (contact, true)
    else if record.isNone && ((dbShare sharesJson contact).isNone || (dbBlob readJson contact).isNone) then some (contact, false)
    else none)
  insist (← absentAgreed gone) "the two parties' database reads differ"
  modifyReport fun r => { r with absent := gone }
  modifyContacts fun k => { k with unreadable := [] }
  let mut loaded : List Nat := []
  for (contact, record) in wanted do
    if let some (_, later) := gone.find? (·.1 == contact) then
      -- Not on the nodes (deleted, or never signed up): nothing of it stays in the engines.
      -- Not served yet: it is not touched.
      if !later then forget contact
      continue
    match dbShare sharesJson contact, dbBlob readJson contact with
    | some share, some (version, blob) =>
      let held := (← get).contacts.resident.contains contact
      unless held && (← versionOf contact) == version do
        forget contact
        Flow.Contacts.key w contact share
        openState contact (← liftResult (fromHex blob))
        setVersion contact version
        -- (A blob that does not open leaves the contact unloaded: `unreadable`, its result.)
        unless (← get).contacts.unreadable.contains contact do
          modifyContacts fun k => { k with resident := k.resident ++ [contact] }
    | _, _ =>
      let some record := record | throw "contact is not in the database"
      forget contact
      let some share ← dbDeal contact s!"{← dbEnv "SIGNAL_DB_TOKENS"}/{contact}.json" | throw "dealing a contact key failed"
      Flow.Contacts.admitTest w contact record
      Flow.Contacts.key w contact share
      setVersion contact 0
      modifyContacts fun k => { k with resident := k.resident ++ [contact] }
    loaded := loaded ++ [contact]
  pure loaded

/-- **The long-lived send session** (DIR: SIGNAL_SERVE_DIR; `accept`: connection 0's expected
accept value). Returns the messages served. -/
def serve (directory : String) (accept : Bytes) : SessionM Nat := do
  let c ← read
  let first ← openAll accept
  let count := max c.sendCircuits 1
  modifyReport fun r => { r with recoveryUsed := true }
  c.ch.report (.ready count)
  let opened ← agreedClock
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
    let job := (← c.ch.nextJob directory).filter (fun job => !finishedJobs.contains job.name)
    let stopping ← c.ch.stopAsked directory
    let clock ← c.ch.clock
    let named := job.map (fun job => TlsWire.hash job.name.toUTF8.data.toList)
    let (theirJob, theirStop, theirClock) ← match ← peer (.serveTick named stopping clock) with
      | .serveTick theirJob theirStop theirClock => pure (theirJob, theirStop, theirClock)
      | _ => throw "invalid serve tick"
    let now ← liftResult (Node.Policy.Clock.agree clock theirClock)
    if named.isSome && theirJob == named then
      let (jobName, requestPath, messagePath, journalPath) :=
        match job with | some j => (j.name, j.request, j.message, j.journal) | none => ("", "", "", "")
      let begun ← c.ch.monotonic
      let text ← c.ch.readMessage messagePath
      modify fun st => { st with
        jobRequest := some requestPath, bodies := [], stamped := []
        report := { st.report with results := [], recoveryLog := [], circuitSends := [] } }
      let contactsOfJob ← loadJob requestPath text
      let jobInputs ← Send.notify contactsOfJob text (← agreedNow)
      let delivered ← if jobInputs.isEmpty then pure 0
        else Send.deliverJob jobInputs contactsOfJob (some jobName) (some journalPath) first
      modify fun st => { st with jobRequest := none }
      served := served + jobInputs.length
      jobsDone := jobsDone + 1
      finishedJobs := (jobName :: finishedJobs).take 64
      let after ← agreedClock
      lastUsed := Array.replicate count after
      lastJob := after
      let report := (← get).report
      let ended ← c.ch.monotonic
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
      c.ch.report (.jobResult jobResult)
    else if stopping || theirStop then
      running := false
    else
      for index in [0:count] do
        modifyPool fun p => { p with current := index }
        let mut s := (← get).pool.states.getD index first
        -- Closed by the server or the proxy while idle: replaced now, not at the next send.
        let polled ← Flow.Server.poll (c.w.on index)
        if let .closed := polled then
          reconnect
          lastUsed := lastUsed.set! index now
          continue
        if let .record wire := polled then
          let slot := ((← get).pool.connection index).slot
          io (slot.set (some wire))
          let (next, alive) ← drainOne s
          if !alive then
            reconnect
            lastUsed := lastUsed.set! index now
            continue
          s := next
          saveState s
        if now ≥ lastUsed.getD index 0 + 25000 then
          let random := (← Flow.Random.joint c.w).val
          if c.official then
            pings := pings + 1
            sendPublic (toBytes (PublicReceive.ping (pings % 256) (toBits (random.take 4))))
          else
            let id ← nextId
            sendPublic (toBytes (← liftResult (PublicReceive.keepalive id (toBits (random.take 4)))))
            let (next, alive) ← awaitSoft 64 (PublicReceive.expect s id)
            if alive then saveState next else reconnect
          lastUsed := lastUsed.set! index now
      -- A quarter of a second between ticks; a second after a minute without a job.
      c.ch.sleep (if now > lastJob + 60000 then 1000 else 250)
  c.ch.log (.serveEnded jobsDone served)
  pure served

end TlsMpc.Node.Session.Serve
