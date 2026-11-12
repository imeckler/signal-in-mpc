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
  let [worker,directory,party,hosts,basePort,manifest,session,endpoint,port,hostname,auth,trust,payloadBytes] := args |
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
      let handshake ← TlsClient.run (TlsWorker.backend rpc) (TlsWorker.transport rpc) {hostname,alpn := ["h2"]}
      insist (handshake.serverCertificateVerified && handshake.serverFinishedVerified) "handshake not accepted after retirement"
      let app ← liftM (TlsWorker.applicationSession rpc handshake)
      let size ← liftM (natural payloadBytes)
      -- These are known handles issued internally by this fixture's private
      -- producer hook, never public plaintext import or reconstructed bytes.
      TlsApplication.send app ⟨1⟩ size
      expectApplication app -- initial server message
      expectApplication app -- first private request echoed by OpenSSL
      TlsApplication.keyUpdate app false
      TlsApplication.send app ⟨2⟩ size
      match ← TlsApplication.receive app with
      | .control => pure () -- server-requested update, renew receive state
      | _ => throw "expected server KeyUpdate"
      expectApplication app -- second echo under updated server traffic keys
      -- The third producer output was generated after the send-key epoch
      -- transition. Its handle skips the received private-buffer handles.
      TlsApplication.send app ⟨5⟩ size
      expectApplication app -- third echo after automatic requested response
      let replay ← liftM (m := IO) (n := M) (TlsApplication.receive app).run
      insist (!replay.isOk) "replayed authenticated ciphertext was accepted"
      TlsApplication.abort app -- idempotent receipt after automatic abort
      let terminal ← liftM (m := IO) (n := M) (TlsApplication.send app ⟨1⟩ size).run
      insist (!terminal.isOk) "application send survived terminal abort"
    let outcome ← action.run
    let verified ← certificate.get
    let codes ← operations.get
    let passed := verified && outcome.isOk && codes.contains 15 && codes.contains 16 && codes.contains 8
    IO.println (Lean.Json.mkObj [("passed",toJson passed),("certificate_verified",toJson verified),
      ("three_private_records",toJson outcome.isOk),("send_update",toJson (codes.contains 15)),
      ("receive_update",toJson (codes.contains 16)),("replay_rejected_and_abort_terminal",toJson outcome.isOk),
      ("error",toJson (match outcome with | .ok _ => "" | .error e => e))]).compress
    unless passed do throw (IO.userError "native application lifecycle fixture failed")
  finally running.stop
