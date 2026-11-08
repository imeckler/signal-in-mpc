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
      TlsApplication.send app ⟨1⟩ 345
      let rec responses (fuel remaining : Nat) : M Unit := do
        match fuel with
        | 0 => throw "WebSocket fixture receive budget exhausted"
        | fuel+1 =>
          match ← TlsApplication.receive app with
          | .application handle =>
            let receipt ← rpc.call .processWebSocket (uint 8 handle.id)
            insist (receipt.length ≥ 13) "truncated WebSocket receipt"
            let upgraded := receipt[0]?.getD 0
            let complete := receipt[1]?.getD 0
            let count := (receipt[2]?.getD 0).toNat
            insist (upgraded ≤ 1 && complete ≤ 1 && count ≤ 4 && receipt.length == 13+11*count)
              "invalid WebSocket receipt metadata"
            for i in List.range count do
              let entry := (receipt.drop (3+11*i)).take 11
              insist (entry[0]?.getD 0 == 10) "unexpected fixture close"
              TlsApplication.send app ⟨number ((entry.drop 1).take 8)⟩ (number (entry.drop 9))
            let producer := receipt.drop (3+11*count)
            let next := number (producer.take 8)
            if complete == 1 && remaining == 2 then TlsApplication.keyUpdate app false
            if next != 0 then TlsApplication.send app ⟨next⟩ (number (producer.drop 8))
            let left := remaining - (if complete == 1 then 1 else 0)
            if left == 0 then pure () else responses fuel left
          | .control => responses fuel remaining
          | .closed => throw "WebSocket fixture closed before responses"
      responses 256 2
      TlsApplication.abort app
      let terminal ← liftM (m := IO) (n := M) (TlsApplication.send app ⟨1⟩ 345).run
      insist (!terminal.isOk) "application send survived terminal abort"
    let outcome ← action.run
    let verified ← certificate.get
    let codes ← operations.get
    let passed := verified && outcome.isOk && codes.contains 15 && codes.contains 18 && codes.contains 8
    IO.println (Lean.Json.mkObj [("passed",toJson passed),("certificate_verified",toJson verified),
      ("two_private_service_responses",toJson outcome.isOk),("send_update",toJson (codes.contains 15)),
      ("error",toJson (match outcome with | .ok _ => "" | .error e => e))]).compress
    unless passed do throw (IO.userError "native WebSocket service fixture failed")
  finally running.stop
