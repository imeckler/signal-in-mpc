import TlsMpc.TlsWebSocketUpgrade
import TlsMpc.TlsWebSocketFrame
import TlsMpc.TlsWebSocketIdle
import TlsMpc.TlsWebSocketControl
import TlsMpc.TlsChatResponse

/-!
Replay of recorded LOCAL Signal-Server bytes through the MPC client's public-receive parsers,
executed on concrete bytes (`ByteAuth.concrete`), exactly as the controller runs them.

Run WITHOUT building anything (uses the repo's existing .olean files; does not touch the lakefile):
  lake -d /Users/izzy/repos/tls-mpc env lean --run /Users/izzy/repos/tls-mpc/local_signal_server/replay/Replay.lean \
    (head|wip) STREAM_FILE [EXPECT_REQUEST_ID]

`Head` and `Wip` are VERBATIM copies of `PublicReceive` from
handshake_backend/EmpHybridWork/PublicServiceController.lean (that file is an executable root, so it
cannot be imported):
  Head = commit e27de08 (2026-11-10): aborts on any server-initiated message.
  Wip  = working tree as read on 2026-11-10 ~14:50 (adds server-request scanning and queue/empty replies).
Only the copied definitions are used; the parsers they call (TlsWebSocketUpgrade, TlsWebSocketFrame,
TlsWebSocketIdle, TlsWebSocketControl, TlsChatResponse) are imported unchanged.
-/
open TlsMpc TlsMpc.Signal

namespace Head
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
  message : List Byte := []

def start (accept : List Byte) : State :=
  { upgrade := TlsWebSocketUpgrade.stateBytes (TlsWebSocketUpgrade.start ByteAuth.concrete)
    frame := TlsWebSocketFrame.stateBytes (TlsWebSocketFrame.start ByteAuth.concrete capacity)
    control := TlsWebSocketControl.stateBytes (TlsWebSocketControl.initial ByteAuth.concrete)
    accept }

def expect (s : State) (id : Nat) : State :=
  { s with pending := true
           response := TlsChatResponse.stateBytes Word64.concrete
             (TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity (BitVec.ofNat 64 id)) }

def get (bytes : List Byte) (index : Nat) : Byte := bytes.getD index 0

def mayReveal (s : State) : Bool := s.message.length < 2 || s.message == [8, 2]

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
end Head

namespace Wip
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
  message : List Byte := []
  held : Option (List Byte × Byte) := none
  request : List Byte := []
  bodySkipped : Bool := false
  skip : Nat := 0
  requests : List (List Byte) := []

def start (accept : List Byte) : State :=
  { upgrade := TlsWebSocketUpgrade.stateBytes (TlsWebSocketUpgrade.start ByteAuth.concrete)
    frame := TlsWebSocketFrame.stateBytes (TlsWebSocketFrame.start ByteAuth.concrete capacity)
    control := TlsWebSocketControl.stateBytes (TlsWebSocketControl.initial ByteAuth.concrete)
    accept }

def expect (s : State) (id : Nat) : State :=
  { s with pending := true
           response := TlsChatResponse.stateBytes Word64.concrete
             (TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity (BitVec.ofNat 64 id)) }

def get (bytes : List Byte) (index : Nat) : Byte := bytes.getD index 0

def varintAt (bytes : List Byte) (index : Nat) : Option (Nat × Nat) :=
  let rec go (fuel pos shift acc : Nat) : Option (Nat × Nat) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      if pos ≥ bytes.length then none else
      let b := (get bytes pos).toNat
      let acc := acc + (b % 128) * 2 ^ shift
      if b < 128 then some (acc, pos + 1) else go fuel (pos + 1) (shift + 7) acc
  go 10 index 0 0

inductive Need where
  | more
  | skip (count : Nat)
  | malformed
  deriving BEq

structure Fields where
  verb : List Byte := []
  path : List Byte := []
  id : Option Nat := none
  body : Option Nat := none

def scan (bytes : List Byte) (bodySkipped : Bool) : Need × Fields := Id.run do
  if bytes.length < 3 then return (.more, {})
  unless bytes.take 2 == [8, 1] && get bytes 2 == 0x12 do return (.malformed, {})
  let some (_, first) := varintAt bytes 3 | return (.more, {})
  let mut pos := first
  let mut fields : Fields := {}
  for _ in [0:bytes.length + 1] do
    if pos ≥ bytes.length then return (.more, fields)
    let tag := (get bytes pos).toNat
    if tag == 0x20 then
      let some (value, next) := varintAt bytes (pos + 1) | return (.more, fields)
      fields := { fields with id := some value }
      pos := next
    else if tag == 0x0a || tag == 0x12 || tag == 0x2a then
      let some (count, next) := varintAt bytes (pos + 1) | return (.more, fields)
      if next + count > bytes.length then return (.more, fields)
      let value := (bytes.drop next).take count
      if tag == 0x0a then fields := { fields with verb := value }
      if tag == 0x12 then fields := { fields with path := value }
      pos := next + count
    else if tag == 0x1a then
      let some (count, next) := varintAt bytes (pos + 1) | return (.more, fields)
      if fields.body.isSome then return (.malformed, fields)
      fields := { fields with body := some count }
      if next == bytes.length && !bodySkipped && count > 0 then return (.skip count, fields)
      pos := next
    else return (.malformed, fields)
  return (.more, fields)

def mayReveal (s : State) : Bool :=
  s.skip == 0 && (s.message.length < 2 || s.message == [8, 2] || s.message == [8, 1])

def step (s : State) (byte : Byte) : Except String (State × Bool) := do
  let (activity, s) ← if s.upgraded then pure (on, s) else do
    let out := TlsWebSocketUpgrade.runByte ByteAuth.concrete (s.upgrade ++ s.accept ++ [on, byte])
    unless get out 0 == on do throw "WebSocket upgrade response rejected"
    pure (get out 2, { s with upgrade := out.drop 3, upgraded := get out 1 == on })
  unless s.skip == 0 do throw "a request body byte was revealed"
  let frame := TlsWebSocketFrame.runByte ByteAuth.concrete capacity (s.frame ++ [activity, byte])
  unless get frame 0 == on do throw "WebSocket frame rejected"
  let control := TlsWebSocketControl.run ByteAuth.concrete (s.control ++ [get frame 2, get frame 6, get frame 7, byte])
  let data := get frame 1 == on
  let done := get frame 5 == on
  let first := data && s.message.length == 0
  let message := if data && s.message.length < 2 then s.message ++ [byte] else s.message
  unless message.length < 2 || message == [8, 2] || message == [8, 1] do
    throw "server-initiated message of an unknown kind: not revealed further"
  if first && done then throw "one-byte message"
  let flags := [get frame 1, get frame 3, get frame 5]
  let feed : List (List Byte × Byte) :=
    if !data then [(flags, byte)]
    else if first then []
    else if message == [8, 2] then (if s.message.length == 1 then s.held.toList else []) ++ [(flags, byte)]
    else []
  let mut s := { s with frame := frame.drop 8, control, message,
                        held := if first then some (flags, byte) else if message.length ≥ 2 then none else s.held }
  let mut complete := false
  if s.pending then
    for (entry, value) in feed do
      if s.pending then
        let out := TlsChatResponse.runByte VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete capacity
          (s.response ++ entry ++ [value])
        unless get out 0 == on do throw "service response rejected or not correlated"
        s := { s with response := out.drop 6 }
        if get out 1 == on then
          unless get out 2 == on do throw "service response was not a success"
          complete := true
          s := { s with pending := false, response := [] }
  if data && message == [8, 1] then
    let request := if s.request.isEmpty then [8, 1] else s.request ++ [byte]
    s := { s with request }
    match (scan request s.bodySkipped).1 with
    | .malformed => throw "malformed server request"
    | .skip count => s := { s with skip := count, bodySkipped := true }
    | .more => pure ()
  if done then
    unless s.skip == 0 do throw "server request ended inside its body"
    if message == [8, 1] then s := { s with requests := s.requests ++ [s.request] }
    s := { s with message := [], held := none, request := [], bodySkipped := false }
  return (s, complete)

def stepSkipped (s : State) : Except String State := do
  unless s.upgraded && s.skip > 0 && s.message == [8, 1] do throw "nothing to skip"
  let frame := TlsWebSocketFrame.runByte ByteAuth.concrete capacity (s.frame ++ [on, 0])
  unless get frame 0 == on && get frame 1 == on do throw "request body left its frame"
  let control := TlsWebSocketControl.run ByteAuth.concrete (s.control ++ [get frame 2, get frame 6, get frame 7, 0])
  let mut s := { s with frame := frame.drop 8, control, skip := s.skip - 1 }
  if get frame 5 == on then
    unless s.skip == 0 do throw "server request ended inside its body"
    s := { s with requests := s.requests ++ [s.request], message := [], held := none, request := [], bodySkipped := false }
  return s

def clientFrame (mask payload : List Byte) : List Byte :=
  [0x82, BitVec.ofNat 8 (128 + payload.length)] ++ mask ++
    payload.zipIdx.map (fun (byte, index) => byte ^^^ get mask (index % 4))

def varint (n : Nat) : List Byte :=
  (List.range 10).filterMap fun i =>
    let rest := n / 128 ^ i
    if i > 0 && rest == 0 then none
    else some (BitVec.ofNat 8 (rest % 128 + (if rest / 128 == 0 then 0 else 128)))

def reply (request mask : List Byte) : Except String (Option (List Byte)) := do
  let (_, fields) := scan request true
  let some id := fields.id | throw "server request without an id"
  let path := String.fromUTF8! ⟨(fields.path.map (fun b => UInt8.ofNat b.toNat)).toArray⟩
  if path == "/api/v1/queue/empty" then
    let response := [0x08] ++ varint id ++ [0x10, 0xc8, 0x01, 0x1a, 0x02, 0x4f, 0x4b]
    let message := [0x08, 0x02, 0x1a] ++ varint response.length ++ response
    unless message.length < 126 && mask.length == 4 do throw "server request reply shape"
    return some (clientFrame mask message)
  else if path == "/api/v1/message" then return none
  else throw s!"unsupported server request {path}"
end Wip

/-! ## Driver -/

def toBits (b : ByteArray) : List (BitVec 8) := b.data.toList.map (fun x => BitVec.ofNat 8 x.toNat)
def hex (bs : List (BitVec 8)) : String :=
  String.join (bs.map fun b => let n := b.toNat; let h := "0123456789abcdef".toList
    String.ofList [h.getD (n / 16) '0', h.getD (n % 16) '0'])
def printable (bs : List (BitVec 8)) : String :=
  String.ofList (bs.map fun b => let n := b.toNat; if 32 ≤ n && n < 127 then Char.ofNat n else '.')

/-- The 28-character `Sec-WebSocket-Accept` value of the recorded 101 (what a correct client computes
from its own key; the authenticated sample's client key is not recorded because that request carries
the password). -/
def acceptOf (stream : List (BitVec 8)) : Option (List (BitVec 8)) := Id.run do
  let text := printable stream
  let marker := "Sec-WebSocket-Accept: "
  match (text.splitOn marker) with
  | _ :: rest :: _ => return some ((toBits rest.toUTF8).take 28)
  | _ => return none

def headLength (stream : List (BitVec 8)) : Nat := Id.run do
  for i in [0:stream.length] do
    if (stream.drop i).take 4 == [13, 10, 13, 10] then return i + 4
  return stream.length

def main (args : List String) : IO UInt32 := do
  let (mode, file, expectId) ← match args with
    | [m, f] => pure (m, f, none)
    | [m, f, i] => pure (m, f, i.toNat?)
    | _ => throw (IO.userError "usage: (head|wip) STREAM_FILE [EXPECT_REQUEST_ID]")
  let stream := toBits (← IO.FS.readBinFile file)
  let some accept := acceptOf stream | throw (IO.userError "no Sec-WebSocket-Accept in stream")
  let head := headLength stream
  IO.println s!"stream {file}: {stream.length} bytes, HTTP head {head} bytes, frames {stream.length - head} bytes"
  IO.println s!"frame bytes: {hex (stream.drop head)}"
  let report (i : Nat) (err : String) : IO UInt32 := do
    let where_ := if i < head then s!"in the HTTP head (offset {i}, char {printable [stream.getD i 0]}, line '{(printable (stream.take head)).splitOn "\r\n" |>.getD (((printable (stream.take i)).splitOn "\r\n").length - 1) ""}')"
      else s!"in the frames (frame offset {i - head})"
    IO.println s!"REJECTED at stream byte {i} = 0x{hex [stream.getD i 0]} {where_}: {err}"
    return 1
  if mode == "head" then
    let mut s := Head.start accept
    let mut armed := false
    let mut completed := 0
    for i in [0:stream.length] do
      if s.upgraded && !armed then
        if let some id := expectId then s := Head.expect s id
        armed := true
      unless Head.mayReveal s do
        IO.println s!"STOP at stream byte {i}: the controller would refuse to reveal it (server-initiated message)"
        return 2
      match Head.step s (stream.getD i 0) with
      | .error e => return ← report i e
      | .ok (next, done) => s := next; if done then completed := completed + 1
    IO.println s!"ACCEPTED all {stream.length} bytes: upgraded={s.upgraded} responses_completed={completed} pending={s.pending}"
    return 0
  else
    let mut s := Wip.start accept
    let mut armed := false
    let mut completed := 0
    let mut i := 0
    let mut skipped := 0
    while i < stream.length do
      if s.upgraded && !armed then
        if let some id := expectId then s := Wip.expect s id
        armed := true
      if s.skip > 0 then
        match Wip.stepSkipped s with
        | .error e => return ← report i e
        | .ok next => s := next; skipped := skipped + 1
      else
        unless Wip.mayReveal s do
          IO.println s!"STOP at stream byte {i}: the controller would refuse to reveal it"
          return 2
        match Wip.step s (stream.getD i 0) with
        | .error e => return ← report i e
        | .ok (next, done) => s := next; if done then completed := completed + 1
      i := i + 1
    IO.println s!"ACCEPTED all {stream.length} bytes: upgraded={s.upgraded} responses_completed={completed} pending={s.pending} body_bytes_skipped_unrevealed={skipped}"
    for r in s.requests do
      let (_, f) := Wip.scan r true
      IO.println s!"  server request: verb={printable f.verb} path={printable f.path} id={f.id} revealed={hex r}"
      match Wip.reply r [1, 2, 3, 4] with
      | .ok (some frame) => IO.println s!"  reply frame (mask 01020304): {hex frame}"
      | .ok none => IO.println "  no reply (message delivery is not acknowledged)"
      | .error e => IO.println s!"  reply error: {e}"
    return 0
