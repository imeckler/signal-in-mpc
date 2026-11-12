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
      insist (catalogue == List.replicate 10 0) "default worker admitted a provider"
      let upgrade ← liftM (m := IO) (n := M) (rpc.call .providerUpgrade (uint 8 1)).run
      insist (!upgrade.isOk) "absent provider produced an upgrade"
      TlsApplication.abort app
      TlsApplication.abort app
      let late ← liftM (m := IO) (n := M) (rpc.call .providerCatalogue []).run
      insist (!late.isOk) "provider operation survived terminal abort"
    let outcome ← action.run
    if !outcome.isOk then
      let _ ← (TlsWorker.emptyReply running.rpc .abort []).run
      pure ()
    let verified ← certificate.get
    let codes ← operations.get
    let noApplication := !(codes.contains 13) && !(codes.contains 14) && !(codes.contains 21)
    let passed := verified && outcome.isOk && noApplication && codes.contains 19 && codes.contains 20 && codes.contains 8
    IO.println (Lean.Json.mkObj [("passed",toJson passed),("certificate_verified",toJson verified),
      ("absent_provider_rejected",toJson outcome.isOk),("no_application_seal_or_produce",toJson noApplication),
      ("error",toJson (match outcome with | .ok _ => "" | .error e => e))]).compress
    unless passed do throw (IO.userError "absent provider check failed")
  finally running.stop
