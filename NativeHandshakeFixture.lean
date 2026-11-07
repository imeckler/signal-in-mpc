import Lean
import TlsMpc.TlsWorkerProcess

/-! Integration fixture: the actual Lean controller drives one native party.
Five instances must run with the same public configuration. No private TLS
value enters this process. The current worker must reject retirement; observing
that rejection does not turn the handshake into an accepted application session.
-/
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient
open Lean (toJson)

private def natural (s : String) : IO Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw (IO.userError "invalid fixture integer")

private def sessionBytes (text : String) : IO Bytes := do
  unless text.length == 64 do throw (IO.userError "invalid fixture session ID")
  let chars := text.toList.toArray
  (List.range 32).mapM fun i => do
    let digit (c : Char) : IO Nat :=
      if '0' ≤ c && c ≤ '9' then pure (c.toNat - '0'.toNat)
      else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
      else throw (IO.userError "invalid fixture session ID")
    return UInt8.ofNat (16 * (← digit chars[2*i]!) + (← digit chars[2*i+1]!))

private structure Evidence where
  certificate : Bool := false
  serverFinished : Bool := false
  finishedProduced : Bool := false
  finishedSent : Bool := false
  retirementRequested : Bool := false
  retirementSucceeded : Bool := false
  records : List Nat := []

def main (args : List String) : IO Unit := do
  let [worker, directory, party, hosts, basePort, manifest, session,
       endpoint, port, hostname, auth, trust] := args |
    throw (IO.userError "WORKER DIRECTORY PARTY HOSTS BASE_PORT MANIFEST SESSION ENDPOINT PORT HOSTNAME AUTH TRUST")
  let evidence ← IO.mkRef ({} : Evidence)
  let running ← TlsWorkerProcess.spawn {
    executable := worker, workingDirectory := directory, party := ← natural party
    hostsFile := hosts, port := ← natural basePort, manifestFile := manifest
    sessionId := ← sessionBytes session }
    (fun name chain scheme hash signature => do
      let checked ← liftM (IO.Process.output {
        cmd := auth
        args := #[name, trust, toString scheme, TlsWorkerProcess.hex hash,
          TlsWorkerProcess.hex signature] ++ (chain.map TlsWorkerProcess.hex).toArray })
      let valid := checked.exitCode == 0 && checked.stdout.trimAscii.toString == "authenticated"
      liftM (evidence.modify (fun e => { e with certificate := valid }) : IO Unit)
      return valid)
  try
    let stderr ← IO.getStderr
    let rpc : TlsWorker.Rpc := { running.rpc with
      call := fun operation input => do
        if operation == .retire then
          liftM (evidence.modify (fun e => { e with retirementRequested := true }) : IO Unit)
        liftM (stderr.putStrLn s!"native fixture operation {TlsWorkerPipe.code operation}, public bytes {input.length}")
        let result ← running.rpc.call operation input
        liftM (evidence.modify (fun e => match operation with
          | .verifyFinished => { e with serverFinished := result == [255] }
          | .finish => { e with finishedProduced := true }
          | .sendRecord => { e with finishedSent := e.finishedSent || e.finishedProduced }
          | .retire => { e with retirementSucceeded := true }
          | .openHandshake => { e with records := e.records ++ [input.length-8] }
          | _ => e) : IO Unit)
        return result }
    let serverPort ← natural port
    let action : M (Session Unit) := do
      TlsWorker.connect rpc endpoint serverPort
      TlsClient.run (TlsWorker.backend rpc) (TlsWorker.transport rpc) {
        hostname, alpn := ["h2"] }
    let result ← action.run
    let e ← evidence.get
    let accepted := match result with | .ok _ => true | .error _ => false
    let error := match result with | .ok _ => "" | .error message => message
    let passed := e.certificate && e.serverFinished && e.finishedProduced &&
      e.finishedSent && e.retirementRequested && !e.retirementSucceeded && !accepted
    IO.println (Lean.Json.mkObj [
      ("passed", toJson passed), ("application_session_accepted", toJson accepted),
      ("certificate_verified", toJson e.certificate),
      ("server_finished_verified", toJson e.serverFinished),
      ("client_finished_sent", toJson e.finishedSent),
      ("retirement_requested", toJson e.retirementRequested),
      ("retirement_succeeded", toJson e.retirementSucceeded),
      ("opened_record_sizes", toJson e.records), ("error", toJson error)]).compress
    unless passed do throw (IO.userError "native handshake fixture did not reach expected retirement boundary")
  finally running.stop
