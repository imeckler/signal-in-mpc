import Lean
import TlsMpc.TlsWorkerProcess
import TlsMpc.TlsWorkerPoll
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient
open Lean (toJson)

private def natural (s : String) : IO Nat :=
  match s.toNat? with | some n => pure n | none => throw (IO.userError "invalid fixture integer")
private def sessionBytes (text : String) : IO Bytes := do
  unless text.length == 64 do throw (IO.userError "invalid fixture session ID")
  let chars := text.toList.toArray
  (List.range 32).mapM fun i => do
    let digit (c : Char) : IO Nat :=
      if '0' ≤ c && c ≤ '9' then pure (c.toNat-'0'.toNat)
      else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat-'a'.toNat+10)
      else throw (IO.userError "invalid fixture hex")
    return UInt8.ofNat (16*(← digit chars[2*i]!) + (← digit chars[2*i+1]!))

private structure Conversation where
  owner : Nat
  inputs : List Nat
  outboxes : List Nat
  pending : Bool := false
private def catalogueRows (fuel offset : Nat) (raw : Bytes) : M (List Conversation × Nat) := do
  match fuel with
  | 0 => return ([],offset)
  | fuel+1 =>
    insist (offset+10 ≤ raw.length) "truncated mux catalogue"
    let owner := number ((raw.drop offset).take 8)
    let count := number ((raw.drop (offset+8)).take 2)
    insist (owner != 0 && count ≤ 64 && offset+10+8*count ≤ raw.length) "invalid mux catalogue entry"
    let inputs := (List.range count).map (fun i => number ((raw.drop (offset+10+8*i)).take 8))
    let outboxOffset := offset+10+8*count
    insist (outboxOffset < raw.length) "truncated restored outbox catalogue"
    let outboxCount := (raw[outboxOffset]?.getD 0).toNat
    insist (outboxCount ≤ 1 && outboxOffset+1+8*outboxCount ≤ raw.length) "invalid restored outbox catalogue"
    let outboxes := (List.range outboxCount).map (fun i => number ((raw.drop (outboxOffset+1+8*i)).take 8))
    insist (outboxes.all (· != 0)) "invalid restored outbox handle"
    let (tail,ending) ← catalogueRows fuel (outboxOffset+1+8*outboxCount) raw
    insist (!(tail.any (fun row => row.owner == owner))) "duplicate mux conversation"
    return (⟨owner,inputs,outboxes,false⟩::tail,ending)

def main (args : List String) : IO Unit := do
  let batchMode ← match args.drop 13 with
    | [] | ["sequential"] => pure false
    | ["batch"] => pure true
    | _ => throw (IO.userError "unknown mux execution mode")
  let [worker,directory,party,hosts,basePort,manifest,session,endpoint,port,hostname,auth,trust,_payloadBytes] := args.take 13 |
    throw (IO.userError "WORKER DIRECTORY PARTY HOSTS PORT MANIFEST SESSION ENDPOINT PORT HOSTNAME AUTH TRUST BYTES")
  let certificate ← IO.mkRef false
  let operations ← IO.mkRef ([] : List Nat)
  let running ← TlsWorkerProcess.spawn {
    executable := worker, workingDirectory := directory,party := ← natural party,
    hostsFile := hosts,port := ← natural basePort,manifestFile := manifest,sessionId := ← sessionBytes session }
    (fun name chain scheme hash signature => do
      let result ← liftM (IO.Process.output {
        cmd := auth

        args := #[name,trust,toString scheme,TlsWorkerProcess.hex hash,TlsWorkerProcess.hex signature] ++
          (chain.map TlsWorkerProcess.hex).toArray })
      let valid := result.exitCode == 0 && result.stdout.trimAscii.toString == "authenticated"
      liftM (certificate.set valid : IO Unit);return valid)
  try
    let rpc : TlsWorker.Rpc := {running.rpc with call := fun op input => do
      let stderr ← liftM (IO.getStderr : IO IO.FS.Stream)
      liftM (stderr.putStrLn s!"native app operation {TlsWorkerPipe.code op}, public bytes {input.length}" : IO Unit)
      liftM (operations.modify (· ++ [TlsWorkerPipe.code op]) : IO Unit)
      running.rpc.call op input}
    let action : M Unit := do
      TlsWorker.connect rpc endpoint (← liftM (natural port))
      let handshake ← TlsClient.run (TlsWorker.backend rpc) (TlsWorker.transport rpc) {hostname,alpn := ["http/1.1"]}
      insist (handshake.serverCertificateVerified && handshake.serverFinishedVerified) "handshake not accepted after retirement"
      let app ← liftM (TlsWorker.applicationSession rpc handshake)
      let catalogue ← rpc.call .muxCatalogue []
      insist (catalogue.length ≥ 2 && catalogue[0]?.getD 0 == 2) "invalid mux catalogue version"
      let count := (catalogue[1]?.getD 0).toNat
      insist (count > 0 && count ≤ 4) "no admitted mux conversations"
      let (rows,ending) ← catalogueRows count 2 catalogue
      insist (ending == catalogue.length) "trailing mux catalogue data"
      let sendReceipt (receipt : Bytes) : M Unit := do
        insist (receipt.length == 10) "invalid private provider receipt"
        let handle := number (receipt.take 8)
        let capacity := number (receipt.drop 8)
        insist (handle != 0 && capacity ≤ 16384) "invalid private provider handle/capacity"
        TlsApplication.send app ⟨handle⟩ capacity
      sendReceipt (← rpc.call .muxUpgrade [])
      let rec responses (fuel : Nat) (rows : List Conversation) (completed : Nat) : M Unit := do
        match fuel with
        | 0 => throw "WebSocket mux receive budget exhausted"
        | fuel+1 =>
          match ← TlsApplication.receive app with
          | .application handle =>
            let receipt ← rpc.call .muxProcess (uint 8 handle.id)
            insist (receipt.length ≥ 3) "truncated mux receipt"
            let upgraded := receipt[0]?.getD 0
            let count := (receipt[1]?.getD 0).toNat
            insist (upgraded ≤ 1 && count ≤ 4 && 3+8*count ≤ receipt.length) "invalid mux completion metadata"
            let owners := (List.range count).map (fun i => number ((receipt.drop (2+8*i)).take 8))
            let mut next := rows
            let mut seen : List Nat := []
            for owner in owners do
              insist (!(seen.contains owner) && next.any (fun row => row.owner == owner && row.pending)) "unknown/replayed mux completion"
              seen := owner::seen
              next := next.map (fun row => if row.owner == owner then {row with pending := false} else row)
            let controlOffset := 2+8*count
            let controls := (receipt[controlOffset]?.getD 0).toNat
            insist (controls ≤ 4 && receipt.length == controlOffset+1+11*controls) "invalid mux controls"
            let entries := (List.range controls).map (fun i => (receipt.drop (controlOffset+1+11*i)).take 11)
            let closing := entries.any (fun entry => entry[0]?.getD 0 == 8)
            for entry in entries do
              let kind := entry[0]?.getD 0
              insist (kind == 8 || kind == 10) "invalid mux control kind"
              if !closing || kind == 8 then
                TlsApplication.send app ⟨number ((entry.drop 1).take 8)⟩ (number (entry.drop 9))
            insist (!closing) "WebSocket closed before mux completion"
            let finished := completed+count
            if completed < 2 && finished ≥ 2 then TlsApplication.keyUpdate app false
            -- Existing immutable outboxes precede new ratchet evaluations.
            -- The worker privately checks authorized resumability and remasks;
            -- the controller never receives the old request ID or message.
            if upgraded == 1 then
              for row in next do
                if !row.pending then
                  match row.outboxes with
                  | handle::tail =>
                    sendReceipt (← rpc.call .muxResumeOutbox (uint 8 row.owner ++ uint 8 handle))
                    next := next.map (fun entry => if entry.owner == row.owner then
                      {entry with outboxes := tail,pending := true} else entry)
                  | [] => pure ()
            let ready := next.filter (fun row => upgraded == 1 && !row.pending && !row.inputs.isEmpty)
            let selected := ready.take 2
            let mut sent := next
            if batchMode && selected.length == 2 then
              let payload := [UInt8.ofNat selected.length] ++ selected.flatMap (fun row => uint 8 row.owner ++ uint 8 (row.inputs.headD 0))
              let result ← rpc.call .muxProduceBatch payload
              insist (result.length == 2+10*selected.length && result[0]?.getD 0 == 1 && (result[1]?.getD 0).toNat == selected.length) "invalid private batch receipt"
              -- TLS records remain ordered through the existing unique sequence
              -- allocator; multiple Machine calls never run concurrently.
              for i in List.range selected.length do sendReceipt ((result.drop (2+10*i)).take 10)
              sent := next.map (fun row => if selected.any (fun chosen => chosen.owner == row.owner) then
                {row with inputs := row.inputs.drop 1,pending := true} else row)
            else if !batchMode || !(next.any (fun row => row.pending)) then
              sent := []
              for row in next do
                match row.inputs with
                | input::tail =>
                  if upgraded == 1 && !row.pending then
                    sendReceipt (← rpc.call .muxProduce (uint 8 row.owner ++ uint 8 input))
                    sent := sent ++ [{row with inputs := tail,pending := true}]
                  else sent := sent ++ [row]
                | [] => sent := sent ++ [row]
            if sent.all (fun row => row.inputs.isEmpty && row.outboxes.isEmpty && !row.pending) then
              insist (finished > 0) "mux supplied no requests"
            else responses fuel sent finished
          | .control => responses fuel rows completed
          | .closed => throw "TLS closed before private mux responses"
      responses 512 rows 0
      TlsApplication.abort app
      let terminal ← liftM (m := IO) (n := M) (TlsApplication.send app ⟨1⟩ 345).run
      insist (!terminal.isOk) "application send survived terminal abort"
    let outcome ← action.run
    if !outcome.isOk then
      let _ ← (TlsWorker.emptyReply running.rpc .abort []).run
      pure ()
    let verified ← certificate.get
    let codes ← operations.get
    let passed := verified && outcome.isOk && codes.contains 25 && codes.contains 27 && codes.contains 8
    IO.println (Lean.Json.mkObj [("passed",toJson passed),("certificate_verified",toJson verified),
      ("authenticated_server_responses",toJson outcome.isOk),("recipient_delivery_claimed",toJson false),("outbox_resume",toJson (codes.contains 27)),("send_update",toJson (codes.contains 15)),
      ("error",toJson (match outcome with | .ok _ => "" | .error e => e))]).compress
    unless passed do throw (IO.userError "private lifecycle WebSocket mux failed")
  finally running.stop
