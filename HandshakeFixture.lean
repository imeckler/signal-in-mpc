import Lean
import TlsMpc.TlsClient
import TlsMpc.TlsWorker
import TlsMpc.TlsPublicHandshake
import TlsMpc.TlsKdfPrepared
import TlsMpc.X25519
import TlsMpc.TlsApplication
import TlsMpc.TlsApplicationRoute

/-! TEST ONLY: clear execution of the Lean handshake using a public deterministic
client scalar and an OpenSSL memory-BIO fixture server. This is neither an MPC
execution nor a production backend. No application account or live secret is
accepted. Production adapters must keep opaque handles and use shared circuits.
-/
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient

def hex (bytes : Bytes) : String := String.ofList (bytes.flatMap fun b =>
  let digits := "0123456789abcdef".toList.toArray
  [digits[b.toNat / 16]!,digits[b.toNat % 16]!])

def unhex (text : String) : Except String Bytes := do
  if text == "-" then return []
  if text.length % 2 != 0 then throw "odd fixture hex"
  let chars := text.toList.toArray
  (List.range (text.length / 2)).mapM fun i => do
    let digit (c : Char) : Except String Nat :=
      if '0' ≤ c && c ≤ '9' then .ok (c.toNat - '0'.toNat)
      else if 'a' ≤ c && c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
      else .error "invalid fixture hex"
    return UInt8.ofNat (16 * (← digit chars[2*i]!) + (← digit chars[2*i+1]!))

def values (bytes : Bytes) : List (BitVec 8) := bytes.map (fun b => BitVec.ofNat 8 b.toNat)
def bytes (values : List (BitVec 8)) : Bytes := values.map (fun b => UInt8.ofNat b.toNat)
def fixtureKey : Bytes := (unhex "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a").toOption.getD []
def corrupt (value : Bytes) : Bytes :=
  match value.reverse with | [] => [] | b :: rest => ((b ^^^ 1) :: rest).reverse

def keyIV (secret : Bytes) : Bytes × Bytes :=
  let pair := TlsKdf.trafficKeysFast Sha256.concrete (values secret)
  (bytes pair.1, bytes pair.2)

def clearFixtureBackend (auth trust mode : String) : Backend Bytes where
  begin := do
    let pubkey := X25519.encode (X25519.compute X25519.concrete
      (X25519.bitValue ∘ X25519.decodeScalar fixtureKey) (FieldDag.ofNat 9))
    pure (fixtureKey, pubkey, TlsWire.hash "public TLS handshake test fixture".toUTF8.data.toList)
  derive scalar peer helloHash := do
    let shared := X25519.compute X25519.concrete (X25519.bitValue ∘ X25519.decodeScalar scalar) (X25519.decodeU peer)
    insist (shared.val != 0) "all-zero X25519 shared secret"
    let hs := TlsKdf.handshakeSecretsFast Sha256.concrete (values (X25519.encode shared)) (values helloHash)
    let client := bytes hs.client
    let server := bytes hs.server
    let ck := keyIV client
    let sk := keyIV server
    return ⟨client,server,bytes hs.main,ck.1,ck.2,sk.1,sk.2⟩
  openHandshake keys sequence wire := do
    let wire := if mode == "bad-tag" then corrupt wire else wire
    let parsed := bytes (TlsPublicHandshake.openCore Gcm.concrete ByteAuth.concrete (values keys.serverKey)
      (values keys.serverIV) (values (uint 8 sequence)) (values wire))
    insist (parsed[0]?.getD 0 == 255) "handshake record rejected"
    let size := number ((parsed.drop 2).take 2)
    return ((parsed[1]?.getD 0).toNat, (parsed.drop 4).take size)
  authenticate hostname chain scheme transcript signature := do
    let hostname := if mode == "bad-host" then "wrong.example" else hostname
    let signature := if mode == "bad-signature" then corrupt signature else signature
    let result ← liftM (IO.Process.output {
      cmd := auth
      args := #[hostname,trust,toString scheme,hex transcript,hex signature] ++ (chain.map hex).toArray })
    return result.exitCode == 0 && result.stdout.trimAscii.toString == "authenticated"
  verifyFinished keys transcript received := do
    let received := if mode == "bad-finished" then corrupt received else received
    return TlsHandshake.verifyHash Sha256.concrete ByteAuth.concrete
      (values keys.serverTraffic) (values transcript) (values received) == 255
  finish keys serverHash clientHash certificate := do
    let secrets := TlsKdf.applicationSecretsFast Sha256.concrete (values keys.mainSecret) (values serverHash)
    let client := bytes secrets.1
    let server := bytes secrets.2
    let ck := keyIV client
    let sk := keyIV server
    let finished := TlsHandshake.finishedMessage Sha256.concrete (values keys.clientTraffic) (values clientHash)
    let wire := TlsRecord.sealCore Gcm.concrete (values keys.clientKey) (values keys.clientIV)
      (values (uint 8 0)) (values certificate ++ finished) 22 0
    return (⟨client,server,ck.1,ck.2,sk.1,sk.2⟩,bytes wire)
  abort := pure ()
  retire _ _ := pure () -- Only the fixed PUBLIC fixture scalar and public-test keys exist here.

/-- TEST ONLY: run the public RPC binding against the clear fixture worker. -/
def rpcFixture (auth trust mode : String) : IO (Backend Unit × IO.Ref (Option (ApplicationKeys Bytes))) := do
  let clear := clearFixtureBackend auth trust mode
  let keys ← IO.mkRef (none : Option (HandshakeKeys Bytes))
  let application ← IO.mkRef (none : Option (ApplicationKeys Bytes))
  let expectedAuth ← IO.mkRef ([] : Bytes)
  let rpc : TlsWorker.Rpc := {
    authenticate := fun host chain scheme hash signature => do
      let valid ← clear.authenticate host chain scheme hash signature
      liftM (expectedAuth.set (TlsWorker.authRequest host chain scheme hash signature valid) : IO Unit)
      return valid
    call := fun operation input => do
      match operation with
      | .begin =>
          let (_, pubkey, random) ← clear.begin
          return pubkey ++ random
      | .derive =>
          let result ← clear.derive fixtureKey (input.take 32) (input.drop 32)
          liftM (keys.set (some result) : IO Unit)
          return []
      | .authenticate =>
          let expected ← (liftM (expectedAuth.get : IO Bytes) : M Bytes)
          insist (input == expected) "public authentication request binding failed"
          return []
      | .retire =>
          liftM (keys.set none : IO Unit)
          return []
      | .abort =>
          liftM (keys.set none : IO Unit)
          liftM (application.set none : IO Unit)
          return []
      | operation =>
          let value ← (liftM (keys.get : IO (Option (HandshakeKeys Bytes))) : M (Option (HandshakeKeys Bytes)))
          let some value := value | throw "missing clear fixture worker keys"
          match operation with
          | .openHandshake =>
              let (kind, content) ← clear.openHandshake value (number (input.take 8)) (input.drop 8)
              return [255, UInt8.ofNat kind] ++ uint 2 content.length ++ content
          | .verifyFinished =>
              let valid ← clear.verifyFinished value (input.take 32) (input.drop 32)
              return [if valid then 255 else 0]
          | .finish =>
              let (result, wire) ← clear.finish value (input.take 32) ((input.drop 32).take 32) (input.drop 64)
              liftM (application.set (some result) : IO Unit)
              return wire
          | _ => throw "unexpected fixture operation" }
  return (TlsWorker.backend rpc, application)

/-- TEST ONLY: controller + actual Lean crypto/parser over PUBLIC fixture keys.
The production implementation must use shared handles for every value here. -/
def checkPostHandshake (handshake : TlsClient.Session Unit) (keys : ApplicationKeys Bytes)
    (transport : Transport) (command : String → M Unit) (mode : String) : M Lean.Json := do
  let parser ← liftM (m := IO) (n := M) (IO.mkRef (List.replicate 11 (0 : BitVec 8)))
  let events ← liftM (m := IO) (n := M) (IO.mkRef ([] : List Nat))
  let sends ← liftM (m := IO) (n := M) (IO.mkRef (0 : Nat))
  let receives ← liftM (m := IO) (n := M) (IO.mkRef (0 : Nat))
  let cleanups ← liftM (m := IO) (n := M) (IO.mkRef (0 : Nat))
  let backend : TlsApplication.Backend Bytes := {
    sealApplication := fun keys seq payload size padding => do
      insist (payload.length == size) "fixture application size mismatch"
      return bytes (TlsRecord.sealCore Gcm.concrete (values keys.clientKey) (values keys.clientIV)
        (values (uint 8 seq)) (values payload) 23 padding)
    sealControl := fun keys seq kind content => pure (bytes (TlsRecord.sealCore Gcm.concrete
      (values keys.clientKey) (values keys.clientIV) (values (uint 8 seq)) (values content) kind 0))
    openRecord := fun keys seq wire => do
      let before ← liftM (m := IO) (n := M) parser.get
      let opened := TlsReceive.openCore Gcm.concrete ByteAuth.concrete
        (values keys.serverKey) (values keys.serverIV) (values (uint 8 seq)) (values wire)
      let routed := TlsApplicationRoute.core Signal.Word64.concrete ByteAuth.concrete before opened
      let result := if (routed[0]?.getD 0).toNat == 5 then
          TlsPostHandshake.core Signal.Word64.concrete ByteAuth.concrete before opened else routed
      liftM (m := IO) (n := M) (parser.set ((result.drop 2).take 11))
      let result := bytes result
      let event := (result[0]?.getD 0).toNat
      liftM (m := IO) (n := M) (events.modify (· ++ [event]))
      match event with
      | 1 => return .application ((result.drop 15).take (number ((result.drop 13).take 2)))
      | 2 => return .skippedControl
      | 3 => return .keyUpdate (result[1]?.getD 0 == 1)
      | 4 => return .closeNotify
      | _ => return .fatal
    rotateSend := fun keys => do
      let secret := bytes (TlsKdf.updateTraffic Sha256.concrete (values keys.clientTraffic))
      let (key,iv) := keyIV secret
      liftM (m := IO) (n := M) (sends.modify (· + 1))
      return { keys with clientTraffic := secret,clientKey := key,clientIV := iv }
    rotateReceive := fun keys => do
      let secret := bytes (TlsKdf.updateTraffic Sha256.concrete (values keys.serverTraffic))
      let (key,iv) := keyIV secret
      liftM (m := IO) (n := M) (receives.modify (· + 1))
      return { keys with serverTraffic := secret,serverKey := key,serverIV := iv }
    abort := liftM (m := IO) (n := M) (cleanups.modify (· + 1)) }
  let app ← liftM (m := IO) (n := M) (TlsApplication.make backend transport {
    keys,hostname := handshake.hostname,alpn := handshake.alpn
    sendSequence := handshake.sendSequence,receiveSequence := handshake.receiveSequence
    serverCertificateVerified := handshake.serverCertificateVerified
    serverFinishedVerified := handshake.serverFinishedVerified,accepted := handshake.accepted })
  let receiveData (expected : Bytes) : M Unit := do
    let mut collected : Bytes := []
    for _ in [0:64] do
      match ← TlsApplication.receive app with
      | .application data => collected := collected ++ data
      | .control => pure ()
      | .closed => throw "closed while expecting application fixture"
      insist (collected.length ≤ expected.length && expected.take collected.length == collected)
        "OpenSSL application plaintext mismatch"
      if collected == expected then return
    throw "too many records in application fixture"
  let control : M Unit := do
    match ← TlsApplication.receive app with
    | .control => pure ()
    | _ => throw "expected authenticated KeyUpdate event"
  let closed : M Unit := do
    match ← TlsApplication.receive app with
    | .closed => pure ()
    | _ => throw "expected authenticated close_notify"
  let echo (payload : Bytes) : M Unit := do
    TlsApplication.send app payload payload.length 3
    receiveData ("echo:".toUTF8.data.toList ++ payload)
  receiveData "server application fixture".toUTF8.data.toList
  command "update-request"
  control
  echo "client answers server update".toUTF8.data.toList
  TlsApplication.keyUpdate app true
  command "emit"
  control
  receiveData "server application fixture".toUTF8.data.toList
  -- Crossed requests are sent before either controller consumes the peer's
  -- update. The following application write discharges both response duties.
  command "update-request"
  TlsApplication.keyUpdate app true
  control
  echo (List.replicate 1200 97)
  let sent ← liftM (m := IO) (n := M) sends.get
  let received ← liftM (m := IO) (n := M) receives.get
  insist (sent == 4 && received == 4) "unexpected traffic-key rotation counts"
  let rejected := mode == "post-corrupt" || mode == "post-replay"
  if rejected then
    command (if mode == "post-corrupt" then "emit-corrupt" else "replay")
    let result ← liftM (m := IO) (n := M) (TlsApplication.receive app).run
    match result with
    | .ok _ => throw "tampered/replayed record accepted"
    | .error _ => pure ()
  else if mode == "post-client-close" then
    TlsApplication.close app
    command "close"
    closed
  else
    command "close"
    closed
    TlsApplication.close app
  let cleanupCount ← liftM (m := IO) (n := M) cleanups.get
  insist (cleanupCount == 1) "application cleanup count mismatch"
  let eventLog ← liftM (m := IO) (n := M) events.get
  return Lean.Json.mkObj [
    ("send_key_rotations",Lean.toJson sent),("receive_key_rotations",Lean.toJson received),
    ("events",Lean.toJson eventLog),("cleanup_count",Lean.toJson cleanupCount),
    ("tampered_or_replayed_record_rejected",Lean.toJson rejected)]

def main (args : List String) : IO Unit := do
  let [server, auth, cert, key, trust, fragment, request, retry, mode] := args
    | throw (IO.userError "fixture_server auth_helper CERT KEY TRUST FRAGMENT REQUEST_CERT RETRY MODE")
  let process ← IO.Process.spawn {
    cmd := server
    args := #[cert,key,fragment,request,if mode == "post-h2" then "h2" else "http/1.1"]
    stdin := .piped, stdout := .piped, stderr := .inherit }
  let queue ← IO.mkRef ([] : List Record)
  let ready ← IO.mkRef false
  let count ← IO.mkRef (0 : Nat)
  let aborted ← IO.mkRef (0 : Nat)
  let retired ← IO.mkRef (0 : Nat)
  let exchange (line : String) : M Unit := do
      liftM (process.stdin.putStrLn line)
      liftM process.stdin.flush
      let response ← liftM process.stdout.getLine
      let fields := response.trimAscii.toString.splitOn " "
      let [state, encoded] := fields | throw "bad memory-BIO server response"
      liftM (ready.set (state == "ready") : IO Unit)
      let raw ← liftResult (unhex encoded)
      let (records,pending) ← liftResult (TlsWire.records 4096 raw)
      insist pending.isEmpty "fixture returned incomplete record"
      liftM (queue.modify (· ++ records) : IO Unit)
  let transport : Transport := {
    send := fun wire => do
      insist (!(mode == "fail-client-finished" && wire.head? == some 23)) "fixture send failed after application-key allocation"
      exchange (hex wire)
    receive := do
      let records ← (liftM (queue.get : IO (List Record)) : M (List Record))
      let first :: rest := records | throw "fixture has no pending server record"
      liftM (queue.set rest : IO Unit)
      liftM (count.modify (· + 1) : IO Unit)
      return first.bytes }
  let (base, applicationKeys) ← rpcFixture auth trust mode
  let backend : Backend Unit := { base with
    abort := do
      base.abort
      liftM (aborted.modify (· + 1) : IO Unit)
    retire := fun scalar keys => do
      base.retire scalar keys
      liftM (retired.modify (· + 1) : IO Unit) }
  let result ← (TlsClient.run backend transport
    { hostname := "server.example", initialKeyShare := retry != "yes",
      alpn := [if mode == "post-h2" then "h2" else "http/1.1"] }).run
  match result with
  | .error error =>
      unless (← aborted.get) == 1 && (← retired.get) == 0 do
        throw (IO.userError "failure cleanup contract violated")
      process.kill
      let _ ← process.wait
      (← IO.getStdout).putStrLn ((Lean.Json.mkObj [("accepted",Lean.toJson false),("error",Lean.toJson error)]).compress)
  | .ok session =>
      unless (← aborted.get) == 0 && (← retired.get) == 1 do
        throw (IO.userError "success cleanup contract violated")
      unless (← ready.get) do throw (IO.userError "OpenSSL did not accept client Finished")
      let pending ← queue.get
      let application := pending.find? (fun record => record.kind == 23)
      let some application := application | throw (IO.userError "missing server application fixture")
      let some appKeys ← applicationKeys.get | throw (IO.userError "missing fixture application keys")
      let post ← if mode.startsWith "post-" then do
          match ← (checkPostHandshake session appKeys transport exchange mode).run with
          | .ok result => pure result
          | .error error =>
              process.kill
              let _ ← process.wait
              throw (IO.userError error)
        else pure Lean.Json.null
      let opened := bytes (TlsReceive.openCore Gcm.concrete ByteAuth.concrete
        (values appKeys.serverKey) (values appKeys.serverIV) (values (uint 8 0)) (values application.bytes))
      let expected := "server application fixture".toUTF8.data.toList
      unless opened[0]?.getD 0 == 255 && opened[1]?.getD 0 == 23 &&
          (opened.drop 4).take (number ((opened.drop 2).take 2)) == expected do
        throw (IO.userError "application traffic keys do not interoperate")
      process.stdin.putStrLn "quit"
      process.stdin.flush
      let exit ← process.wait
      unless exit == 0 do throw (IO.userError "fixture server exited unsuccessfully")
      (← IO.getStdout).putStrLn ((Lean.Json.mkObj [("accepted",Lean.toJson true),
        ("server_accepted_client_finished",Lean.toJson true),("application_record_matched",Lean.toJson true),
        ("records",Lean.toJson (← count.get)),("alpn",Lean.toJson session.alpn),
        ("post_handshake",post),
        ("native_mpc_executed",Lean.toJson false)]).compress)
