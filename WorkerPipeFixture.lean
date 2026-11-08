import TlsMpc.TlsWorkerPipe
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.TlsWorker

def main (args : List String) : IO Unit := do
  let [path, mode] := args | throw (IO.userError "pipe_fixture MODE")
  let child ← IO.Process.spawn {cmd := path, args := #[mode], stdin := .piped, stdout := .piped, stderr := .inherit}
  let rpc ← TlsWorkerPipe.make (IO.FS.Stream.ofHandle child.stdout) (IO.FS.Stream.ofHandle child.stdin) (fun _ _ _ _ _ => pure true)
  if mode == "reject-cleanup" then
    let rejected ← (rpc.call .begin []).run
    unless !rejected.isOk do throw (IO.userError "rejection fixture accepted")
    let blocked ← (rpc.call .begin []).run
    unless !blocked.isOk do throw (IO.userError "private retry survived rejection")
    for _ in [0,1] do
      match ← (rpc.call .abort []).run with
      | .ok bytes => unless bytes.isEmpty do throw (IO.userError "cleanup receipt payload")
      | .error message => throw (IO.userError message)
    let blockedAgain ← (rpc.call .sendRecord []).run
    unless !blockedAgain.isOk do throw (IO.userError "cleanup reopened private pipe")
    unless (← child.wait) == 0 do throw (IO.userError "cleanup pipe fixture failed")
    IO.println "pipe rejection: cleanup receipts allowed, private work terminal"
    return
  if mode == "concurrent" then
    let jobs ← (List.range 32).mapM fun index => IO.asTask (do
      let expected := uint 8 index
      let result ← (rpc.call .sendRecord expected).run
      match result with
      | .ok bytes => unless bytes == expected do throw (IO.userError "concurrent response mismatch")
      | .error message => throw (IO.userError message))
    for job in jobs do
      match ← IO.wait job with
      | .ok _ => pure ()
      | .error error => throw error
    unless (← child.wait) == 0 do throw (IO.userError "concurrent pipe fixture failed")
    IO.println "pipe framing concurrent: 32 serialized exchanges passed"
    return
  if mode == "duplex" then
    let transport := applicationTransport rpc
    let expected := record 23 (List.replicate 18 7)
    let incoming ← IO.asTask transport.receive.run
    IO.sleep 20
    let sent ← (transport.send expected).run
    match sent with
    | .ok _ => pure ()
    | .error message => throw (IO.userError message)
    match ← IO.wait incoming with
    | .ok (.ok bytes) => unless bytes == expected do throw (IO.userError "duplex receive mismatch")
    | .ok (.error message) => throw (IO.userError message)
    | .error error => throw error
    unless (← child.wait) == 0 do throw (IO.userError "duplex pipe fixture failed")
    IO.println "pipe framing duplex: receive pending while send completes"
    return
  let operations : List Operation := if mode == "valid" then
    [.begin,.derive,.openHandshake,.authenticate,.verifyFinished,.finish,.retire,.abort,.connect,.sendRecord,.receiveRecord,.openApplication,.sealApplication,.sealControl,.rotateSend,.rotateReceive,.pollRecord] else [.begin]
  let result ← (do
    for operation in operations do
      let payload := if operation == .authenticate then
        authRequest "server.example" [[1,2,3],[4,5]] 0x0807 (List.replicate 32 7) [9,8,7] true
        else (List.range (codeSize operation)).map (fun i => UInt8.ofNat (i % 256))
      let response ← rpc.call operation payload
      insist (response == payload) "pipe payload changed" : M Unit).run
  let exit ← child.wait
  unless exit == 0 do throw (IO.userError "pipe fixture failed")
  match result with
  | .ok _ => unless mode == "valid" do throw (IO.userError "malformed pipe response accepted")
  | .error _ =>
      unless mode != "valid" do throw (IO.userError "valid pipe request rejected")
      match ← (rpc.call .begin []).run with
      | .error message => unless message == "worker pipe is terminal after failure" do
          throw (IO.userError "pipe failure was not sticky")
      | .ok _ => throw (IO.userError "failed pipe accepted another operation")
      if mode != "rejected" then
        match ← (rpc.call .abort []).run with
        | .error message => unless message == "worker pipe is terminal after failure" do
            throw (IO.userError "broken framing attempted a cleanup exchange")
        | .ok _ => throw (IO.userError "broken framing allowed cleanup receipt")
  IO.println s!"pipe framing {mode}: passed"
where
  codeSize : Operation → Nat
    | .begin => 0 | .derive => 64 | .openHandshake => 16653 | .authenticate => 0
    | .verifyFinished => 68 | .finish => 72 | .retire => 0 | .abort => 0
    | .connect => 19 | .sendRecord => 16645 | .receiveRecord => 0
    | .openApplication => 16414 | .sealApplication => 20 | .sealControl => 14
    | .rotateSend => 0 | .rotateReceive => 0 | .pollRecord => 0
