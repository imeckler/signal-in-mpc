import Lean
import TlsMpc.TlsWorkerProcess
import TlsMpc.TlsWebSocketUpgrade
import TlsMpc.TlsWebSocketFrame
import TlsMpc.TlsWebSocketIdle
import TlsMpc.TlsWebSocketControl
import TlsMpc.TlsChatResponse
import TlsMpc.Signal.RelayEncoding

/-!
Service controller for the public-receive profile.

Secret from the two parties: the contact list and the client's own keys.
Everything the server sends back is handled in the clear: each record is still
decrypted and authenticated inside the engines under the shared TLS keys, then
its bytes are revealed one at a time and parsed HERE, by the same Lean parsers
the private profile compiles to circuits, run on concrete bytes
(`ByteAuth.concrete`). Each party runs this controller; the workers act only on
requests both controllers issue identically.

One restriction keeps contacts hidden: a server-initiated WebSocket message
(for example an incoming envelope, whose unsealed form names its sender) is
never revealed beyond its first two bytes. Those two bytes distinguish a
response (`08 02`) from anything else; anything else aborts the session,
because receiving messages is not supported on this path yet.

Public here: record lengths and contents of responses and control frames,
request ids, the WebSocket nonce and masks. Private: credentials, every
request the client sends, all session and identity state.
-/
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.Signal
open Lean (toJson)

namespace PublicReceive

abbrev Byte := BitVec 8
def capacity : Nat := 4096
def on : Byte := 255

structure State where
  upgrade : List Byte
  frame : List Byte
  control : List Byte
  response : List Byte := []
  accept : List Byte
  upgraded : Bool := false
  pending : Bool := false
  /-- First payload bytes of the binary message in progress (at most two). -/
  message : List Byte := []

def start (accept : List Byte) : State :=
  { upgrade := TlsWebSocketUpgrade.stateBytes (TlsWebSocketUpgrade.start ByteAuth.concrete)
    frame := TlsWebSocketFrame.stateBytes (TlsWebSocketFrame.start ByteAuth.concrete capacity)
    control := TlsWebSocketControl.stateBytes (TlsWebSocketControl.initial ByteAuth.concrete)
    accept }

/-- Expect the response to the request with this id. -/
def expect (s : State) (id : Nat) : State :=
  { s with pending := true
           response := TlsChatResponse.stateBytes Word64.concrete
             (TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity (BitVec.ofNat 64 id)) }

def get (bytes : List Byte) (index : Nat) : Byte := bytes.getD index 0

/-- Whether another byte of the current record may be revealed: never a third
payload byte of a message that did not start as a response. -/
def mayReveal (s : State) : Bool := s.message.length < 2 || s.message == [8, 2]

/-- Consume one revealed byte. Returns the new state and whether a successful
response to the pending request completed at this byte. -/
def step (s : State) (byte : Byte) : Except String (State × Bool) := do
  let (activity, s) ← if s.upgraded then pure (on, s) else do
    let out := TlsWebSocketUpgrade.runByte ByteAuth.concrete (s.upgrade ++ s.accept ++ [on, byte])
    unless get out 0 == on do throw "WebSocket upgrade response rejected"
    pure (get out 2, { s with upgrade := out.drop 3, upgraded := get out 1 == on })
  let frame := if s.pending then TlsWebSocketFrame.runByte ByteAuth.concrete capacity (s.frame ++ [activity, byte])
    else TlsWebSocketIdle.run ByteAuth.concrete capacity (s.frame ++ [activity, byte])
  unless get frame 0 == on do throw "WebSocket frame rejected"
  let control := TlsWebSocketControl.run ByteAuth.concrete (s.control ++ [get frame 2, get frame 6, get frame 7, byte])
  let message := if get frame 1 == on && s.message.length < 2 then s.message ++ [byte] else s.message
  unless message.length < 2 || message == [8, 2] do
    throw "server-initiated message: not revealed and not handled on this path"
  let mut s := { s with frame := frame.drop 8, control, message := if get frame 5 == on then [] else message }
  let mut complete := false
  if s.pending then
    let out := TlsChatResponse.runByte VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete capacity
      (s.response ++ [get frame 1, get frame 3, get frame 5, byte])
    unless get out 0 == on do throw "service response rejected or not correlated"
    s := { s with response := out.drop 6 }
    if get out 1 == on then
      unless get out 2 == on do throw "service response was not a success"
      complete := true
      s := { s with pending := false, response := [] }
  return (s, complete)

/-- Queued control replies as (kind, masked frame bytes); the queue is cleared. -/
def replies (s : State) (mask : List Byte) : Except String (State × List (Nat × List Byte)) := do
  unless get s.control 0 == on do throw "control queue rejected"
  let count := (get s.control 127).toNat
  unless count ≤ 4 do throw "control queue count"
  let frames ← (List.range count).mapM fun i => do
    let kind := get s.control (128 + i)
    unless kind == 8 || kind == 10 do throw "control kind"
    let out := TlsWebSocketControl.encode ByteAuth.concrete
      ([get s.control 0, 0, get s.control (132 + i), kind] ++ mask ++ (s.control.drop (136 + 125 * i)).take 125)
    unless get out 0 == on && get out 1 == 0 do throw "control reply rejected"
    pure (kind.toNat, (out.drop 3).take (get out 2).toNat)
  return ({ s with control := s.control.take 127 ++ List.replicate 509 0 }, frames)

end PublicReceive

/-! The relay request around an opened sealed-sender envelope, assembled in the
clear. Four fixed-width slots are left as zero bytes for the engines to fill:
recipient UUID text (36), access key in base64 (24), device id (3, space
padded) and registration id (10, space padded). Everything else, including the
request id, timestamp and WebSocket mask, is public. -/
namespace PublicRequest
abbrev Byte := BitVec 8

inductive Piece where
  | bytes (value : List Byte)
  | slot (index width : Nat)

def Piece.width : Piece → Nat
  | .bytes value => value.length
  | .slot _ width => width

def total (pieces : List Piece) : Nat := (pieces.map Piece.width).foldl (· + ·) 0
def text (s : String) : List Byte := s.toUTF8.data.toList.map (fun b => BitVec.ofNat 8 b.toNat)

def varint (n : Nat) : List Byte :=
  (List.range 10).filterMap fun i =>
    let rest := n / 128 ^ i
    if i > 0 && rest == 0 then none
    else some (BitVec.ofNat 8 (rest % 128 + (if rest / 128 == 0 then 0 else 128)))

def field (tag : Nat) (pieces : List Piece) : List Piece :=
  .bytes (BitVec.ofNat 8 tag :: varint (total pieces)) :: pieces

/-- The masked WebSocket frame with zeroed slots, and the frame offsets of the
UUID, access-key, device and registration slots. -/
def build (envelope : List Byte) (timestamp id : Nat) (mask : List Byte) : Except String (List Byte × List Nat) := do
  let json : List Piece := [
    .bytes (text "{\"messages\":[{\"content\":\"" ++ RelayEncoding.base64 ByteAuth.concrete envelope ++
      text "\",\"destinationDeviceId\":"), .slot 2 3,
    .bytes (text ",\"destinationRegistrationId\":"), .slot 3 10,
    .bytes (text (",\"type\":6}],\"online\":false,\"timestamp\":" ++ toString timestamp ++ ",\"urgent\":true}"))]
  let request := field 10 [.bytes (text "PUT")] ++
    field 18 [.bytes (text "/v1/messages/"), .slot 0 36, .bytes (text "?story=false")] ++
    field 26 json ++ [.bytes (32 :: varint id)] ++
    field 42 [.bytes (text "content-type: application/json")] ++
    field 42 [.bytes (text "unidentified-access-key: "), .slot 1 24]
  let message := Piece.bytes [8, 1] :: field 18 request
  let size := total message
  unless 126 ≤ size && size < 65536 && mask.length == 4 do throw "request size"
  let header : List Byte := [130, 254, BitVec.ofNat 8 (size / 256), BitVec.ofNat 8 size] ++ mask
  let mut frame := header
  let mut offsets := #[0, 0, 0, 0]
  for piece in message do
    match piece with
    | .bytes value =>
      for byte in value do
        frame := frame ++ [byte ^^^ mask.getD ((frame.length - 8) % 4) 0]
    | .slot index width =>
      offsets := offsets.set! index frame.length
      frame := frame ++ List.replicate width 0
  return (frame, offsets.toList)

end PublicRequest

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

private def toBits (bytes : Bytes) : List (BitVec 8) := bytes.map (fun b => BitVec.ofNat 8 b.toNat)
private def toBytes (bits : List (BitVec 8)) : Bytes := bits.map (fun b => UInt8.ofNat b.toNat)

def main (args : List String) : IO Unit := do
  let [worker,directory,party,hosts,basePort,manifest,session,endpoint,port,hostname,auth,trust,_unused] := args |
    throw (IO.userError "WORKER DIRECTORY PARTY HOSTS PORT MANIFEST SESSION ENDPOINT PORT HOSTNAME AUTH TRUST UNUSED")
  let certificate ← IO.mkRef false
  let operations ← IO.mkRef ([] : List Nat)
  let revealed ← IO.mkRef 0
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
      liftM (operations.modify (fun codes => if codes.contains (TlsWorkerPipe.code op) then codes else codes ++ [TlsWorkerPipe.code op]) : IO Unit)
      running.rpc.call op input}
    let action : M Nat := do
      TlsWorker.connect rpc endpoint (← liftM (natural port))
      let handshake ← TlsClient.run (TlsWorker.backend rpc) (TlsWorker.transport rpc) {hostname,alpn := ["http/1.1"]}
      insist (handshake.serverCertificateVerified && handshake.serverFinishedVerified) "handshake not accepted after retirement"
      let app ← liftM (TlsWorker.applicationSession rpc handshake)
      let catalogue ← rpc.call .providerCatalogue []
      insist (catalogue.length ≥ 10) "invalid provider catalogue"
      let state := number (catalogue.take 8)
      let count := number ((catalogue.drop 8).take 2)
      insist (state != 0 && count > 0 && count ≤ 64 && catalogue.length == 10+8*count) "no admitted private provider/inputs"
      let inputs := (List.range count).map (fun i => number ((catalogue.drop (10+8*i)).take 8))
      -- Private upgrade request; the expected accept value is public.
      let upgrade ← rpc.call .providerUpgradeOpen (uint 8 state)
      insist (upgrade.length == 38) "invalid upgrade receipt"
      TlsApplication.send app ⟨number (upgrade.take 8)⟩ (number ((upgrade.drop 8).take 2))
      let sendPublic (bytes : Bytes) : M Unit := do
        let handle ← rpc.call .publicBuffer bytes
        insist (handle.length == 8 && number handle != 0) "invalid public buffer handle"
        TlsApplication.send app ⟨number handle⟩ bytes.length
      -- Reveal and parse one authenticated record, byte by byte.
      let record (handle : Nat) (start : PublicReceive.State) : M (PublicReceive.State × Bool) := do
        let mut s := start
        let mut complete := false
        let mut offset := 0
        let mut length := 1
        while offset < length do
          insist (PublicReceive.mayReveal s) "refusing to reveal a server-initiated message"
          let out ← rpc.call .revealApplication (uint 8 handle ++ uint 2 offset)
          insist (out.length == 2 || out.length == 3) "invalid reveal reply"
          length := number (out.take 2)
          if offset < length then
            insist (out.length == 3) "missing revealed byte"
            liftM (revealed.modify (· + 1) : IO Unit)
            let (next, done) ← liftResult (PublicReceive.step s (BitVec.ofNat 8 (out[2]?.getD 0).toNat))
            s := next
            complete := complete || done
          offset := offset + 1
        return (s, complete)
      -- One send: the engines produce and open the sealed-sender envelope; the request
      -- is assembled here; the engines insert the contact's fields and seal the record.
      let sendMessage (input id : Nat) : M Unit := do
        let sealed ← rpc.call .providerSealOpen (uint 8 state ++ uint 8 input)
        insist (sealed.length ≥ 10) "invalid sealed envelope reply"
        let timestamp := number (sealed.take 8)
        let length := number ((sealed.drop 8).take 2)
        insist (0 < length && length ≤ sealed.length - 10) "invalid sealed envelope length"
        let random ← rpc.call .publicRandom []
        insist (random.length == 32) "invalid joint randomness"
        let (frame, offsets) ← liftResult (PublicRequest.build (toBits ((sealed.drop 10).take length)) timestamp id (toBits (random.take 4)))
        let handle ← rpc.call .providerRequest (uint 8 input ++ offsets.flatMap (uint 2) ++ random.take 4 ++ toBytes frame)
        insist (handle.length == 8 && number handle != 0) "invalid request handle"
        TlsApplication.send app ⟨number handle⟩ frame.length
      let rec loop (fuel : Nat) (s : PublicReceive.State) (inputs : List Nat) (completed : Nat) : M Nat := do
        match fuel with
        | 0 => throw "receive budget exhausted"
        | fuel+1 =>
          match ← TlsApplication.receive app with
          | .application handle =>
            let wasPending := s.pending
            let (s, complete) ← record handle.id s
            -- The mask is public but must be the same for both controllers: joint randomness.
            let mask ← if (PublicReceive.get s.control 127) == 0 then pure [0, 0, 0, 0] else do
              let random ← rpc.call .publicRandom []
              insist (random.length == 32) "invalid joint randomness"
              pure (random.take 4)
            let (s, frames) ← liftResult (PublicReceive.replies s (toBits mask))
            for (kind, frame) in frames do
              sendPublic (toBytes frame)
              insist (kind != 8) "WebSocket peer closed before completion"
            insist (!complete || wasPending) "unsolicited service response"
            let finished := completed + (if complete then 1 else 0)
            if complete && finished == 1 then TlsApplication.keyUpdate app false
            if s.upgraded && !s.pending then
              match inputs with
              | [] => insist (finished > 0) "private provider supplied no requests"; return finished
              | input::tail =>
                -- Request ids are public: a counter from 2^63, as the service expects.
                let id := 2 ^ 63 + finished
                sendMessage input id
                loop fuel (PublicReceive.expect s id) tail finished
            else loop fuel s inputs finished
          | .control => loop fuel s inputs completed
          | .closed => throw "TLS closed before private responses"
      let finished ← loop 256 (PublicReceive.start (toBits (upgrade.drop 10))) inputs 0
      TlsApplication.abort app
      return finished
    let outcome ← action.run
    if !outcome.isOk then
      let _ ← (TlsWorker.emptyReply running.rpc .abort []).run
      pure ()
    let verified ← certificate.get
    let codes ← operations.get
    let passed := verified && outcome.isOk && codes.contains 15 && codes.contains 29 && codes.contains 34 && codes.contains 35 && !codes.contains 18
    IO.println (Lean.Json.mkObj [("passed",toJson passed),("certificate_verified",toJson verified),
      ("responses_completed",toJson (match outcome with | .ok n => n | .error _ => 0)),
      ("bytes_revealed",toJson (← revealed.get)),("private_receive_parsing_used",toJson (codes.contains 18)),
      ("error",toJson (match outcome with | .ok _ => "" | .error e => e))]).compress
    unless passed do throw (IO.userError "public-receive service session failed")
  finally running.stop
