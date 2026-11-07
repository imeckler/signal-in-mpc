import TlsMpc.TlsApplication

/-! Public mock handles only. Exercises controller ordering, failure/cleanup,
key-update limits and duplex scheduling; does not execute MPC or cryptography. -/
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient
namespace ApplicationFixture

def check (ok : Bool) (name : String) : IO Unit :=
  unless ok do throw (IO.userError name)

def success (action : M α) : IO α := do
  match ← action.run with
  | .ok value => return value
  | .error message => throw (IO.userError message)

def rejected (action : M α) : IO Unit := do
  match ← action.run with
  | .ok _ => throw (IO.userError "expected rejection")
  | .error _ => pure ()

def io (action : IO α) : M α := liftM action

def handshake (send receive : Nat := 0) : TlsClient.Session Nat := {
  keys := ⟨0,0,0,0,0,0⟩, hostname := "public.fixture", alpn := none
  sendSequence := send, receiveSequence := receive
  serverCertificateVerified := true, serverFinishedVerified := true
  accepted := ⟨rfl,rfl⟩ }

structure Fixture where
  session : TlsApplication.Session Nat
  log : IO.Ref (List String)
  events : IO.Ref (List (TlsApplication.Event Nat))
  failure : IO.Ref String

def wire (bytes : Nat := 0) : Bytes := record 23 (List.replicate (bytes+17) 0)

def makeFixture (send receive : Nat := 0)
    (readWire : Option (IO Bytes) := none) : IO Fixture := do
  let log ← IO.mkRef []
  let events ← IO.mkRef []
  let failure ← IO.mkRef ""
  let emit (s : String) : M Unit := io (log.modify (· ++ [s]))
  let failAt (s : String) : M Unit := do
    let mode ← io failure.get
    if mode == s then throw "injected protocol error"
    if mode == s ++ "-io" then io (throw (IO.userError "injected I/O error"))
  let backend : TlsApplication.Backend Nat := {
    sealApplication := fun keys seq payload bytes padding => do
      emit s!"seal:{keys.clientKey}:{seq}:{payload}"
      failAt "seal"
      return wire (bytes+padding)
    sealControl := fun keys seq kind content => do
      emit s!"control:{keys.clientKey}:{seq}:{kind}:{content}"
      failAt "control"
      return wire content.length
    openRecord := fun keys seq _ => do
      emit s!"open:{keys.serverKey}:{seq}"
      failAt "open"
      let todo ← io events.get
      match todo with
      | [] => throw "no mock event"
      | e :: rest => io (events.set rest); return e
    rotateSend := fun keys => do
      emit "rotate-send"
      failAt "rotate"
      return { keys with clientKey := keys.clientKey+1 }
    rotateReceive := fun keys => do
      emit "rotate-receive"
      failAt "rotate"
      return { keys with serverKey := keys.serverKey+1 }
    abort := do
      emit "abort"
      failAt "cleanup" }
  let transport : Transport := {
    send := fun _ => emit "send" *> failAt "send"
    receive := do
      emit "receive"
      failAt "receive"
      match readWire with
      | none => return wire
      | some action => io action }
  return ⟨← TlsApplication.make backend transport (handshake send receive),log,events,failure⟩

def policyChecks : IO Nat := do
  let limit := TlsApplicationPolicy.recordLimit
  let maxEpoch := TlsApplicationPolicy.maxSendEpoch
  let mut checked := 0
  for epoch in [0,1,maxEpoch-1,maxEpoch] do
    for seq in [0,1,limit-2,limit-1,limit,2^64] do
      for closed in [false,true] do
        for aborted in [false,true] do
          let state : TlsApplicationPolicy.State := {
            sendEpoch := epoch, sendNext := seq, sendClosed := closed, aborted }
          let available := !closed && !aborted
          check ((TlsApplicationPolicy.reserveApplication state).isSome ==
            (available && seq < limit-1)) "application budget"
          check ((TlsApplicationPolicy.reserveUpdate state false).isSome ==
            (available && seq < limit && epoch < maxEpoch)) "update budget"
          check ((TlsApplicationPolicy.reserveClose state).isSome ==
            (available && seq < limit)) "close budget"
          checked := checked+3
  for epoch in [0,maxEpoch,maxEpoch+1,2^64] do
    for seq in [0,limit,2^64-1,2^64] do
      let state : TlsApplicationPolicy.State := { receiveEpoch := epoch, receiveNext := seq }
      check ((TlsApplicationPolicy.reserveReceive state).isSome == (seq < 2^64)) "receive budget"
      checked := checked+1
  let ceiling : TlsApplicationPolicy.State := { sendEpoch := maxEpoch }
  check (!(TlsApplicationPolicy.receiveUpdate ceiling true).responseDue) "ignore request at epoch ceiling"
  return checked+1

def controllerChecks : IO Unit := do
  let f ← makeFixture
  success (TlsApplication.send f.session 42 3)
  success (TlsApplication.send f.session 43 3)
  success (TlsApplication.keyUpdate f.session true)
  success (TlsApplication.send f.session 44 3)
  check ((← f.log.get) == ["seal:0:0:42","send","seal:0:1:43","send",
    "control:0:2:22:[24, 0, 0, 1, 1]","send","rotate-send","seal:1:0:44","send"])
    "old-key update before new-key send"
  f.events.set [.keyUpdate true,.application 99,.closeNotify]
  let _ ← success (TlsApplication.receive f.session)
  success (TlsApplication.send f.session 45 3)
  let received ← success (TlsApplication.receive f.session)
  check (match received with | .application n => n == 99 | _ => false) "opaque receive handle"
  check ((← f.log.get).drop 9 == ["receive","open:0:0","rotate-receive",
    "control:1:1:22:[24, 0, 0, 1, 0]","send","rotate-send","seal:2:0:45","send",
    "receive","open:1:0"]) "crossed requested updates and receive sequence reset"
  let _ ← success (TlsApplication.receive f.session)
  let before ← f.log.get
  let _ ← success (TlsApplication.receive f.session)
  check ((← f.log.get) == before) "receive half-close avoids further reads"
  success (TlsApplication.send f.session 46 0)
  success (TlsApplication.close f.session)
  check ((← f.log.get).getLast? == some "abort") "both closed directions retire session"
  rejected (TlsApplication.send f.session 47 0)

  let f ← makeFixture
  success (TlsApplication.close f.session)
  check ((← f.log.get).getLast? == some "send") "local half-close retains receive direction"
  f.events.set [.application 77,.closeNotify]
  let r ← success (TlsApplication.receive f.session)
  check (match r with | .application n => n == 77 | _ => false) "receive after local half-close"
  let _ ← success (TlsApplication.receive f.session)
  check ((← f.log.get).getLast? == some "abort") "peer closes final direction"

  let f ← makeFixture (TlsApplicationPolicy.recordLimit-1) 7
  success (TlsApplication.send f.session 50 0)
  check ((← f.log.get) == [s!"control:0:{TlsApplicationPolicy.recordLimit-1}:22:[24, 0, 0, 1, 0]",
    "send","rotate-send","seal:1:0:50","send"]) "automatic budget update"
  f.events.set [.application 0]
  let _ ← success (TlsApplication.receive f.session)
  check ((← f.log.get).getLast? == some "open:0:7") "preserve handshake receive counter"

  let f ← makeFixture
  success (TlsApplication.keyUpdate f.session true)
  rejected (TlsApplication.keyUpdate f.session true)
  check ((← f.log.get).getLast? == some "abort") "duplicate outstanding request rejected"
  let f ← makeFixture
  f.events.set [.keyUpdate true]
  let _ ← success (TlsApplication.receive f.session)
  rejected (TlsApplication.keyUpdate f.session true)
  check ((← f.log.get).getLast? == some "abort") "requested update cannot substitute for required unrequested response"

  for mode in ["seal","seal-io","send","send-io"] do
    let f ← makeFixture
    f.failure.set mode
    rejected (TlsApplication.send f.session 60 1)
    f.failure.set ""
    let before ← f.log.get
    rejected (TlsApplication.send f.session 61 1)
    check ((← f.log.get) == before ++ ["abort"]) "failed send is terminal"
  for mode in ["control","control-io","rotate","rotate-io"] do
    let f ← makeFixture
    f.failure.set mode
    rejected (TlsApplication.keyUpdate f.session)
    f.failure.set ""
    let before ← f.log.get
    rejected (TlsApplication.send f.session 62 1)
    check ((← f.log.get) == before ++ ["abort"]) "failed update is terminal"
  for mode in ["receive","receive-io","open","open-io"] do
    let f ← makeFixture
    f.failure.set mode
    rejected (TlsApplication.receive f.session)
    f.failure.set ""
    let before ← f.log.get
    rejected (TlsApplication.send f.session 63 1)
    check ((← f.log.get) == before ++ ["abort"]) "failed receive is terminal"
  for mode in ["cleanup","cleanup-io"] do
    let f ← makeFixture
    f.failure.set mode
    let result ← (TlsApplication.send f.session 0 16385).run
    check (match result with | .error e => e.endsWith "; backend erasure failed" | _ => false)
      "cleanup failure is explicit"

def duplexCheck : IO Unit := do
  let entered ← IO.Promise.new
  let release ← IO.Promise.new
  let f ← makeFixture 0 0 (some (do
    entered.resolve ()
    let _ ← IO.wait release.result!
    return wire))
  f.events.set [.application 7]
  let receiving ← IO.asTask (success (TlsApplication.receive f.session))
  let _ ← IO.wait entered.result!
  -- A send must complete while the receive is still waiting for wire bytes.
  success (TlsApplication.send f.session 70 0)
  release.resolve ()
  let result ← IO.wait receiving
  match result with
  | .error e => throw e
  | .ok value => check (match value with | .application n => n == 7 | _ => false) "duplex handle"

def cleanupChecks : IO Unit := do
  for ioError in [false,true] do
    let count ← IO.mkRef 0
    let action : M Unit := if ioError then io (throw (IO.userError "injected")) else throw "injected"
    rejected (cleanupOnError action (io (count.modify (·+1))))
    check ((← count.get) == 1) "handshake cleanup catches both error channels"
  let count ← IO.mkRef 0
  success (cleanupOnError (pure ()) (io (count.modify (·+1))))
  check ((← count.get) == 0) "successful action does not abort"
  for failBegin in [false,true] do
    let count ← IO.mkRef 0
    let backend : TlsClient.Backend Unit := {
      begin := if failBegin then io (throw (IO.userError "begin failed"))
        else pure ((),List.replicate 32 9,List.replicate 32 0)
      derive := fun _ _ _ => throw "unreachable derive"
      openHandshake := fun _ _ _ => throw "unreachable open"
      authenticate := fun _ _ _ _ _ => throw "unreachable auth"
      verifyFinished := fun _ _ _ => throw "unreachable verify"
      finish := fun _ _ _ _ => throw "unreachable finish"
      retire := fun _ _ => throw "unreachable retire"
      abort := io (count.modify (·+1)) }
    let transport : Transport := {
      send := fun _ => io (throw (IO.userError "send failed"))
      receive := throw "unreachable receive" }
    rejected (TlsClient.run backend transport { hostname := "public.fixture" })
    check ((← count.get) == 1) "actual handshake run catches I/O exceptions"

def concurrencyChecks : IO Unit := do
  let f ← makeFixture
  let tasks ← (List.range 32).mapM fun i => IO.asTask (success (TlsApplication.send f.session i 0))
  for task in tasks do
    match ← IO.wait task with
    | .error e => throw e
    | .ok _ => pure ()
  let log ← f.log.get
  check (log.length == 64) "concurrent send event count"
  for i in List.range 32 do
    check ((log[2*i]?.getD "").startsWith s!"seal:0:{i}:") "concurrent sends reserve distinct sequences"
    check (log[2*i+1]? == some "send") "concurrent sends serialize seal/send"

def incomingChecks : IO Unit := do
  for bad in [[],(wire).drop 1,wire ++ wire,record 22 (List.replicate 17 0),
      [23,3,1,0,17] ++ List.replicate 17 0,List.replicate 16407 0] do
    let f ← makeFixture 0 0 (some (pure bad))
    rejected (TlsApplication.receive f.session)
    check ((← f.log.get) == ["receive","abort"]) "malformed public frame rejected before private open"
  let f ← makeFixture
  f.events.set [.fatal]
  rejected (TlsApplication.receive f.session)
  let before ← f.log.get
  rejected (TlsApplication.send f.session 0 0)
  check ((← f.log.get) == before ++ ["abort"]) "authenticated rejection is terminal"

end ApplicationFixture

def main : IO Unit := do
  let count ← ApplicationFixture.policyChecks
  ApplicationFixture.controllerChecks
  ApplicationFixture.duplexCheck
  ApplicationFixture.cleanupChecks
  ApplicationFixture.concurrencyChecks
  ApplicationFixture.incomingChecks
  IO.println s!"PASS: {count} policy boundary checks; controller sequencing, key updates, half-close, terminal failures, duplex receive and cleanup"
