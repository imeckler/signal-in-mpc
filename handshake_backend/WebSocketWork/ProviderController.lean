import Lean
import TlsMpc.TlsWorkerProcess
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

private def expectApplication (app : TlsApplication.Session TlsWorker.BufferHandle) : M Unit := do
  match ← TlsApplication.receive app with
  | .application handle => insist (handle.id != 0) "zero private buffer handle"
  | _ => throw "expected private application payload"

def main (args : List String) : IO Unit := do
  let [worker,directory,party,hosts,basePort,manifest,session,endpoint,port,hostname,auth,trust,_payloadBytes] := args |
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
      let catalogue ← rpc.call .providerCatalogue []
      insist (catalogue.length ≥ 10) "invalid provider catalogue"
      let state := number (catalogue.take 8)
      let count := number ((catalogue.drop 8).take 2)
      insist (state != 0 && count > 0 && count ≤ 64 && catalogue.length == 10+8*count)
        "no admitted private provider/inputs"
      let inputs := (List.range count).map (fun i => number ((catalogue.drop (10+8*i)).take 8))
      let sendReceipt (receipt : Bytes) : M Unit := do
        insist (receipt.length == 10) "invalid private provider receipt"
        let handle := number (receipt.take 8)
        let capacity := number (receipt.drop 8)
        insist (handle != 0 && capacity ≤ 16384) "invalid private provider handle/capacity"
        TlsApplication.send app ⟨handle⟩ capacity
      sendReceipt (← rpc.call .providerUpgrade (uint 8 state))
      let rec responses (fuel : Nat) (waiting : Bool) (inputs : List Nat) (completed : Nat) : M Unit := do
        match fuel with
        | 0 => throw "WebSocket receive budget exhausted"
        | fuel+1 =>
          match ← TlsApplication.receive app with
          | .application handle =>
            let receipt ← rpc.call .processWebSocket (uint 8 handle.id)
            insist (receipt.length ≥ 3) "truncated WebSocket receipt"
            let upgraded := receipt[0]?.getD 0
            let complete := receipt[1]?.getD 0
            let count := (receipt[2]?.getD 0).toNat
            insist (upgraded ≤ 1 && complete ≤ 1 && count ≤ 4 && receipt.length == 3+11*count)
              "invalid WebSocket receipt metadata"
            let entries := (List.range count).map (fun i => (receipt.drop (3+11*i)).take 11)
            let closing := entries.any (fun entry => entry[0]?.getD 0 == 8)
            for entry in entries do
              let kind := entry[0]?.getD 0
              insist (kind == 8 || kind == 10) "invalid WebSocket control kind"
              if !closing || kind == 8 then
                TlsApplication.send app ⟨number ((entry.drop 1).take 8)⟩ (number (entry.drop 9))
            insist (!closing) "WebSocket peer closed before completion"
            insist (complete == 0 || waiting) "unsolicited service response"
            let finished := completed + (if complete == 1 then 1 else 0)
            let pending := waiting && complete == 0
            if complete == 1 && finished == 1 then TlsApplication.keyUpdate app false
            if upgraded == 1 && !pending then
              match inputs with
              | [] => insist (finished > 0) "private provider supplied no requests"
              | input::tail =>
                sendReceipt (← rpc.call .providerProduce (uint 8 state ++ uint 8 input))
                responses fuel true tail finished
            else responses fuel pending inputs finished
          | .control => responses fuel waiting inputs completed
          | .closed => throw "TLS closed before private responses"
      responses 256 false inputs 0
      TlsApplication.abort app
      let terminal ← liftM (m := IO) (n := M) (TlsApplication.send app ⟨1⟩ 345).run
      insist (!terminal.isOk) "application send survived terminal abort"
    let outcome ← action.run
    if !outcome.isOk then
      let _ ← (TlsWorker.emptyReply running.rpc .abort []).run
      pure ()
    let verified ← certificate.get
    let codes ← operations.get
    let passed := verified && outcome.isOk && codes.contains 15 && codes.contains 18 && codes.contains 21 && codes.contains 8
    IO.println (Lean.Json.mkObj [("passed",toJson passed),("certificate_verified",toJson verified),
      ("private_provider_responses",toJson outcome.isOk),("send_update",toJson (codes.contains 15)),
      ("error",toJson (match outcome with | .ok _ => "" | .error e => e))]).compress
    unless passed do throw (IO.userError "private lifecycle WebSocket session failed")
  finally running.stop
