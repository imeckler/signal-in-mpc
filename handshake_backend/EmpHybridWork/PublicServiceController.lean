import Lean
import Std.Time
import TlsMpc.TlsWorkerProcess
import TlsMpc.TlsWebSocketUpgrade
import TlsMpc.TlsWebSocketFrame
import TlsMpc.TlsWebSocketIdle
import TlsMpc.TlsWebSocketControl
import TlsMpc.TlsChatResponse
import TlsMpc.Signal.RelayEncoding
import TlsMpc.Signal.PrivateTextNotification
import TlsMpc.Signal.RelayUpgrade

/-!
Service controller for the public-receive profile.

Secret from the two parties: the contact list and the client's own keys.
Everything the server sends back is handled in the clear: each record is still
decrypted and authenticated inside the engines under the shared TLS keys, then
its bytes are revealed one at a time and parsed HERE, by the same Lean parsers
the private profile compiles to circuits, run on concrete bytes
(`ByteAuth.concrete`). Each party runs this controller; the workers act only on
requests both controllers issue identically.

One restriction keeps contacts hidden: of a server-initiated request only the
verb, path, id and headers are revealed, never its body. The body of a
delivered message is an envelope: its field keys, lengths and varints are
revealed, and its sealed content goes to the engines unopened, where it is
received as a NEW contact's first message (`TlsMpc/ReceiveKernels.lean`).
Public from that: which of our prekeys the message names, its Kyber
ciphertext, and the message text. The sender's identity stays in the engines;
the contact's record is sealed and stored under a new id, and only then is the
message acknowledged. Later messages from an existing contact are not
supported yet (they are refused and acknowledged).

Public here: record lengths and contents of responses and control frames,
request ids, the WebSocket nonce and masks. Private: credentials, every
request the client sends, all session and identity state.
-/
open TlsMpc TlsMpc.TlsWire TlsMpc.TlsClient TlsMpc.Signal
open Lean (toJson)

namespace PublicReceive

abbrev Byte := BitVec 8
def capacity : Nat := 4096

/-- The byte operations the parsers below run on, for values in the clear. Equal to
`ByteAuth.concrete` (`fast_eq`); the differences are in how three operations are computed at
run time. `ByteAuth.concrete` builds the mask of one bit with `BitVec.replicate`, and its
constants and complements go through `2 ^ 8` as an arbitrary-precision power each time; together
that made every parsed byte cost milliseconds. -/
def fastConst (n : Nat) : BitVec 8 := BitVec.ofFin ⟨n % 256, Nat.mod_lt n (by decide)⟩
theorem fastConst_eq (n : Nat) : fastConst n = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq
  simp [fastConst]

def fastNot (x : BitVec 8) : BitVec 8 := x ^^^ 255#8
theorem fastNot_eq : ∀ x : BitVec 8, fastNot x = ~~~x := by decide

def fastMask (x : BitVec 8) (i : Nat) : BitVec 8 := if x.getLsbD i then 255#8 else 0#8

theorem fastMask_eq (x : BitVec 8) (i : Nat) : fastMask x i = BitVec.replicate 8 (x.extractLsb' i 1) := by
  have h : x.extractLsb' i 1 = BitVec.ofBool (x.getLsbD i) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have hz : j = 0 := by omega
    subst hz
    simp
  rw [h]
  unfold fastMask
  cases x.getLsbD i <;> decide

def fast : ByteAuth.Ops (BitVec 8) where
  const := fastConst
  xor := (· ^^^ ·)
  and := (· &&& ·)
  not := fastNot
  maskBit := fastMask

theorem fast_eq : fast = ByteAuth.concrete := by
  have hc : fastConst = BitVec.ofNat 8 := funext fastConst_eq
  have hn : fastNot = (fun x : BitVec 8 => ~~~x) := funext fastNot_eq
  have hm : fastMask = (fun (x : BitVec 8) (i : Nat) => BitVec.replicate 8 (x.extractLsb' i 1)) :=
    funext fun x => funext fun i => fastMask_eq x i
  unfold fast ByteAuth.concrete
  rw [hc, hn, hm]
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
  /-- The first payload byte of a message whose kind is not known yet, with its
  frame flags, held back from the response parser until the second byte. -/
  held : Option (List Byte × Byte) := none
  /-- Revealed payload of the server request in progress; its body is never
  revealed and is absent here. -/
  request : List Byte := []
  bodySkipped : Bool := false
  /-- Body bytes of the request in progress still to pass over unrevealed. -/
  skip : Nat := 0
  /-- The bytes being passed over are a delivered envelope's sealed content, to be
  kept (still unrevealed) for the engines. -/
  capture : Bool := false
  /-- A delivered envelope being walked: its revealed bytes (field payloads
  omitted), how many payloads have been passed, and the body bytes left. -/
  inner : Option (List Byte × Nat × Nat) := none
  /-- Completed envelopes: (type, sealed content length). -/
  envelopes : List (Nat × Nat) := []
  /-- Completed server requests awaiting a reply. -/
  requests : List (List Byte) := []
  /-- The response parser's state at the start of the frame in progress. A frame's header
  bytes reach that parser before its payload shows whether the message is a response; if it
  turns out to be a server request, the parser is put back to this state. -/
  rollback : List Byte := []
  /-- Before the upgrade completes: how many bytes of the header terminator
  CR LF CR LF the revealed bytes currently end with (0..3). -/
  terminator : Nat := 0

def start (accept : List Byte) : State :=
  { upgrade := TlsWebSocketUpgrade.stateBytes (TlsWebSocketUpgrade.start PublicReceive.fast)
    frame := TlsWebSocketFrame.stateBytes (TlsWebSocketFrame.start PublicReceive.fast capacity)
    control := TlsWebSocketControl.stateBytes (TlsWebSocketControl.initial PublicReceive.fast)
    accept }

/-- Expect the response to the request with this id. -/
def expect (s : State) (id : Nat) : State :=
  { s with pending := true
           response := TlsChatResponse.stateBytes Word64.concrete
             (TlsChatResponse.initial Word64.concrete PublicReceive.fast capacity (BitVec.ofNat 64 id)) }

def get (bytes : List Byte) (index : Nat) : Byte := bytes.getD index 0

/-! ### Server requests

A server-initiated message is a request (`08 01`): `12 len { verb (0a), path
(12), body (1a), id (20), headers (2a) }`. Its verb, path, id and headers are
revealed; its BODY never is, because the body of a delivered message can name
its sender. The scanner below walks the revealed bytes (which omit the body's
content) and says what to do next. -/

/-- A protobuf varint at `index`: its value and the index after it. -/
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
  | more                 -- reveal the next byte
  | skip (count : Nat)   -- pass over this many body bytes without revealing them
  | malformed
  deriving BEq

structure Fields where
  verb : List Byte := []
  path : List Byte := []
  id : Option Nat := none
  body : Option Nat := none   -- body length, if a body field was present

/-- Walk the fields of a request from the revealed bytes. `bodySkipped` says
whether the body's content has already been passed over. -/
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

/-! ### Delivered envelopes

The body of a `PUT /api/v1/message` request is an `Envelope`. Its sealed
`content` (field 8) is what identifies the sender once opened, so it is never
revealed: it is passed to the engines as it is. Every other length-delimited
or fixed-width field is passed over unrevealed and unused (some of them name
the sender when a message is not sealed). Only field keys, lengths and varint
values are revealed: the envelope type, timestamps and flags. -/

inductive EnvelopeNeed where
  | more (boundary : Bool)             -- reveal the next byte; `boundary`: at the end of a field
  | pass (count : Nat) (content : Bool) -- pass over a payload; `content`: keep it for the engines
  | malformed
  deriving BEq

/-- Walk an envelope's revealed bytes; `passed` payloads have been passed over
already. Also returns the type (field 1) and the content length seen so far. -/
def envelopeScan (bytes : List Byte) (passed : Nat) : EnvelopeNeed × Nat × Nat := Id.run do
  let mut pos := 0
  let mut seen := 0
  let mut kind := 0
  let mut content := 0
  for _ in [0:bytes.length + 1] do
    if pos ≥ bytes.length then return (.more true, kind, content)
    let some (key, next) := varintAt bytes pos | return (.more false, kind, content)
    let wire := key % 8
    if wire == 0 then
      let some (value, after) := varintAt bytes next | return (.more false, kind, content)
      if key / 8 == 1 then kind := value
      pos := after
    else if wire == 1 || wire == 2 || wire == 5 then
      let (count, after) ← if wire == 2 then
          match varintAt bytes next with
          | some found => pure found
          | none => return (.more false, kind, content)
        else pure ((if wire == 1 then 8 else 4), next)
      if wire == 2 && key / 8 == 8 then
        if content != 0 then return (.malformed, kind, content)
        content := count
      if count == 0 then pos := after
      else if seen < passed then
        seen := seen + 1
        pos := after
      else if after == bytes.length then return (.pass count (wire == 2 && key / 8 == 8), kind, content)
      else return (.malformed, kind, content)
    else return (.malformed, kind, content)
  return (.more false, kind, content)

/-- After a revealed byte or a passed payload of the envelope being walked. -/
def envelopeAdvance (s : State) (header : List Byte) (passed remaining : Nat) : Except String State := do
  let (need, kind, content) := envelopeScan header passed
  match need with
  | .malformed => throw "malformed envelope"
  | .more boundary =>
    if remaining == 0 then
      unless boundary do throw "envelope ended inside a field"
      return { s with inner := none, envelopes := s.envelopes ++ [(kind, content)] }
    else return { s with inner := some (header, passed, remaining) }
  | .pass count capture =>
    unless count ≤ remaining do throw "envelope field runs past the body"
    return { s with inner := some (header, passed, remaining), skip := count, capture }

/-- Whether another byte of the current record may be revealed: never a third
payload byte of a message that is neither a response nor a request, and never
a request's body. -/
def mayReveal (s : State) : Bool :=
  s.skip == 0 && (s.message.length < 2 || s.message == [8, 2] || s.message == [8, 1])

/-- Bytes still unrevealed of the field a request's revealed bytes end in, when
that field is its verb, path or a header (never its body). -/
def fieldMissing (bytes : List Byte) : Nat := Id.run do
  if bytes.length < 3 then return 0
  let some (_, first) := varintAt bytes 3 | return 0
  let mut pos := first
  for _ in [0:bytes.length + 1] do
    if pos ≥ bytes.length then return 0
    let tag := (get bytes pos).toNat
    if tag == 0x0a || tag == 0x12 || tag == 0x2a then
      let some (count, next) := varintAt bytes (pos + 1) | return 0
      if next + count > bytes.length then return next + count - bytes.length
      pos := next + count
    else if tag == 0x20 || tag == 0x1a then
      -- the id's value; or the body's length (its content is not among these bytes)
      let some (_, next) := varintAt bytes (pos + 1) | return 0
      pos := next
    else return 0
  return 0

/-- How many bytes may be revealed in one step: as many as are certain to be
bytes this controller may see, given what has been revealed so far. Each step
is a round trip between the parties, so longer steps matter.

* Before the upgrade completes, the response headers end at the first
  CR LF CR LF: with `k` of its bytes just seen, the next `4 - k` bytes cannot
  reach past it.
* A frame's header is at least two bytes, and an extended length is two.
* A control frame's payload, and the payload of a message confirmed as a
  response (`08 02`), to the end of the frame.
* The first two payload bytes of a message say what it is.
* In a server request (`08 01`): the rest of its verb, path or header field,
  once that field's length has been revealed. Never its body.

The caller checks, byte by byte, that what is left of a step is still within
this bound. (Frame state: which byte is expected next at 0..4 — first header,
second header, extended length high, low, payload — the opcode at 7, and the
payload bytes left at 10..11.) -/
def budget (s : State) : Nat :=
  if !s.upgraded then 4 - min s.terminator 3 else
  let expects := fun i => get s.frame i == on
  let remaining := (get s.frame 10).toNat * 256 + (get s.frame 11).toNat
  if expects 0 || expects 2 then 2
  else if !expects 4 || remaining == 0 then 1
  else if (get s.frame 7).toNat ≥ 8 then remaining
  else if s.message == [8, 2] then remaining
  else if s.message == [8, 1] then max 1 (min remaining (fieldMissing s.request))
  else if s.message.isEmpty then min 2 remaining
  else 1

/-- Consume one revealed byte. Returns the new state and whether a successful
response to the pending request completed at this byte. -/
def step (s : State) (byte : Byte) : Except String (State × Bool) := do
  let (activity, s) ← if s.upgraded then pure (on, s) else do
    let out := TlsWebSocketUpgrade.runByte PublicReceive.fast (s.upgrade ++ s.accept ++ [on, byte])
    unless get out 0 == on do throw "WebSocket upgrade response rejected"
    let expected : Byte := if s.terminator % 2 == 0 then 13 else 10
    let terminator := if byte == expected then s.terminator + 1 else if byte == 13 then 1 else 0
    -- The upgrade parser and this count must agree on where the headers end.
    unless (get out 1 == on) == (terminator == 4) do throw "upgrade response headers ended unexpectedly"
    pure (get out 2, { s with upgrade := out.drop 3, upgraded := get out 1 == on, terminator })
  unless s.skip == 0 do throw "a request body byte was revealed"
  let s := if s.pending && s.message.isEmpty && get s.frame 0 == on then { s with rollback := s.response } else s
  let wasFirst := s.message.length == 1
  -- The general frame parser: server requests are data frames too.
  let frame := TlsWebSocketFrame.runByte PublicReceive.fast capacity (s.frame ++ [activity, byte])
  unless get frame 0 == on do throw "WebSocket frame rejected"
  let control := TlsWebSocketControl.run PublicReceive.fast (s.control ++ [get frame 2, get frame 6, get frame 7, byte])
  let data := get frame 1 == on
  let done := get frame 5 == on
  let first := data && s.message.length == 0
  let message := if data && s.message.length < 2 then s.message ++ [byte] else s.message
  unless message.length < 2 || message == [8, 2] || message == [8, 1] do
    throw "server-initiated message of an unknown kind: not revealed further"
  if first && done then throw "one-byte message"
  let flags := [get frame 1, get frame 3, get frame 5]
  -- What the response parser sees: everything except the payload of a request. The first
  -- payload byte waits until the second shows which kind of message this is.
  let feed : List (List Byte × Byte) :=
    if !data then [(flags, byte)]
    else if first then []
    else if message == [8, 2] then (if s.message.length == 1 then s.held.toList else []) ++ [(flags, byte)]
    else []
  let mut s := { s with frame := frame.drop 8, control, message,
                        held := if first then some (flags, byte) else if message.length ≥ 2 then none else s.held }
  let mut complete := false
  -- A server request arriving while a response is awaited: its header bytes were not the
  -- response's.
  if s.pending && wasFirst && message == [8, 1] then s := { s with response := s.rollback }
  if s.pending then
    for (entry, value) in feed do
      if s.pending then
        let out := TlsChatResponse.runByte VarintDecode.Spqr.concrete Word64.concrete PublicReceive.fast capacity
          (s.response ++ entry ++ [value])
        unless get out 0 == on do throw "service response rejected or not correlated"
        s := { s with response := out.drop 6 }
        if get out 1 == on then
          unless get out 2 == on do throw "service response was not a success"
          complete := true
          s := { s with pending := false, response := [] }
  if data && message == [8, 1] then
    match s.inner with
    | some (header, passed, remaining) =>
      unless remaining > 0 do throw "envelope state"
      s ← envelopeAdvance s (header ++ [byte]) passed (remaining - 1)
    | none =>
      let request := if s.request.isEmpty then [8, 1] else s.request ++ [byte]
      s := { s with request }
      match scan request s.bodySkipped with
      | (.malformed, _) => throw "malformed server request"
      | (.skip count, fields) =>
        -- A delivered message's body is walked; any other body is passed over whole.
        if fields.path == "/api/v1/message".toUTF8.data.toList.map (fun b => BitVec.ofNat 8 b.toNat) then
          s ← envelopeAdvance { s with bodySkipped := true } [] 0 count
        else s := { s with skip := count, capture := false, bodySkipped := true }
      | (.more, _) => pure ()
  if done then
    unless s.skip == 0 && s.inner.isNone do throw "server request ended inside its body"
    if message == [8, 1] then s := { s with requests := s.requests ++ [s.request] }
    s := { s with message := [], held := none, request := [], bodySkipped := false }
  return (s, complete)

/-- Pass over one unrevealed body byte of a server request: only the frame
parser advances (it does not look at the payload of a binary frame). -/
def stepSkipped (s : State) : Except String State := do
  unless s.upgraded && s.skip > 0 && s.message == [8, 1] do throw "nothing to skip"
  let frame := TlsWebSocketFrame.runByte PublicReceive.fast capacity (s.frame ++ [on, 0])
  unless get frame 0 == on && get frame 1 == on do throw "request body left its frame"
  let control := TlsWebSocketControl.run PublicReceive.fast (s.control ++ [get frame 2, get frame 6, get frame 7, 0])
  let mut s := { s with frame := frame.drop 8, control, skip := s.skip - 1 }
  if let some (header, passed, remaining) := s.inner then
    unless remaining > 0 do throw "envelope state"
    if s.skip == 0 then s ← envelopeAdvance { s with capture := false } header (passed + 1) (remaining - 1)
    else s := { s with inner := some (header, passed, remaining - 1) }
  if get frame 5 == on then
    unless s.skip == 0 && s.inner.isNone do throw "server request ended inside its body"
    s := { s with requests := s.requests ++ [s.request], message := [], held := none, request := [], bodySkipped := false }
  return s

/-- A masked client frame carrying a binary message shorter than 126 bytes. -/
def clientFrame (mask payload : List Byte) : List Byte :=
  [0x82, BitVec.ofNat 8 (128 + payload.length)] ++ mask ++
    payload.zipIdx.map (fun (byte, index) => byte ^^^ get mask (index % 4))

def varint (n : Nat) : List Byte :=
  (List.range 10).filterMap fun i =>
    let rest := n / 128 ^ i
    if i > 0 && rest == 0 then none
    else some (BitVec.ofNat 8 (rest % 128 + (if rest / 128 == 0 then 0 else 128)))

/-- The `200 OK` reply to a completed server request (`queue/empty`, or a
delivered message), and whether it was a delivered message. Replying to a
delivered message acknowledges it: the server then removes it from its queue,
so the caller sends that reply only once the message has been dealt with.
Anything else is an error. -/
def reply (request mask : List Byte) : Except String (List Byte × Bool) := do
  let (_, fields) := scan request true
  let some id := fields.id | throw "server request without an id"
  let path := String.fromUTF8! ⟨(fields.path.map (fun b => UInt8.ofNat b.toNat)).toArray⟩
  let delivered := path == "/api/v1/message"
  unless delivered || path == "/api/v1/queue/empty" do throw s!"unsupported server request {path}"
  let response := [0x08] ++ varint id ++ [0x10, 0xc8, 0x01, 0x1a, 0x02, 0x4f, 0x4b]
  let message := [0x08, 0x02, 0x1a] ++ varint response.length ++ response
  unless message.length < 126 && mask.length == 4 do throw "server request reply shape"
  return (clientFrame mask message, delivered)

/-- A `GET /v1/keepalive` request (the server drops a socket that is silent for
90 seconds and never pings first). Its response is correlated like any other. -/
def keepalive (id : Nat) (mask : List Byte) : Except String (List Byte) := do
  let ascii (s : String) : List Byte := s.toUTF8.data.toList.map (fun b => BitVec.ofNat 8 b.toNat)
  let request := [0x0a, 3] ++ ascii "GET" ++ [0x12, 13] ++ ascii "/v1/keepalive" ++ [0x20] ++ varint id
  let message := [0x08, 0x01, 0x12] ++ varint request.length ++ request
  unless message.length < 126 && mask.length == 4 do throw "keepalive shape"
  return clientFrame mask message

/-- Queued control replies as (kind, masked frame bytes); the queue is cleared. -/
def replies (s : State) (mask : List Byte) : Except String (State × List (Nat × List Byte)) := do
  unless get s.control 0 == on do throw "control queue rejected"
  let count := (get s.control 127).toNat
  unless count ≤ 4 do throw "control queue count"
  let frames ← (List.range count).mapM fun i => do
    let kind := get s.control (128 + i)
    unless kind == 8 || kind == 10 do throw "control kind"
    let out := TlsWebSocketControl.encode PublicReceive.fast
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
    .bytes (text "{\"messages\":[{\"content\":\"" ++ RelayEncoding.base64 PublicReceive.fast envelope ++
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

private def fromHex (text : String) : Except String Bytes := do
  let chars := text.toList
  unless chars.length % 2 == 0 do throw "odd-length hex string"
  let digit (c : Char) : Except String Nat :=
    if c.isDigit then pure (c.toNat - 48)
    else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 87)
    else if 'A' ≤ c && c ≤ 'F' then pure (c.toNat - 55)
    else throw "invalid hex digit"
  (List.range (chars.length / 2)).mapM (fun i => do
    pure (UInt8.ofNat (16 * (← digit (chars.getD (2 * i) '0')) + (← digit (chars.getD (2 * i + 1) '0')))))

/-- TEST state for a run against the local Signal server: the file written by
`lss-provision export-mpc` (local_signal_server/). Returns the sender's
certificate and identity key and, per contact, its id and record without the
certificate (session block ++ metadata). -/
private def readExport (text : String) : Except String (Bytes × Bytes × List (Nat × Bytes)) := do
  let json ← Lean.Json.parse text
  let sender ← json.getObjVal? "sender"
  let certificate ← fromHex (← sender.getObjValAs? String "certificate_hex")
  let identity ← fromHex (← sender.getObjValAs? String "identity_private_hex")
  let contacts ← json.getObjValAs? (Array Lean.Json) "contacts"
  let records ← contacts.toList.mapM (fun contact => do
    let id ← fromHex (← contact.getObjValAs? String "contact_id_u128_hex")
    let session ← fromHex (← contact.getObjValAs? String "session_block_hex")
    let metadata ← fromHex (← contact.getObjValAs? String "metadata_hex")
    unless id.length == 16 && session.length == 262 && metadata.length == 57 do throw "export contact shape"
    pure (number id, session ++ metadata))
  unless identity.length == 32 && 0 < certificate.length && certificate.length ≤ 1024 && !records.isEmpty do
    throw "export shape"
  pure (certificate, identity, records)

/-- What receiving a new contact's first message needs besides the shared
identity key: our public identity key and address, OUR prekey private keys by
id (held in the clear by both parties), and the server certificate that signs
sender certificates (validated against the trust root by the export tool). -/
structure ReceiveKeys where
  identityPublic : Bytes
  address : Bytes
  serverKey : Bytes
  serverCertificate : Bytes
  serverId : Nat
  oneTime : List (Nat × Bytes)
  signed : List (Nat × Bytes)
  kyber : List (Nat × Bytes)

private def readReceive (text : String) : Except String ReceiveKeys := do
  let json ← Lean.Json.parse text
  let sender ← json.getObjVal? "sender"
  let server ← json.getObjVal? "sealed_sender_server"
  let keys (name : String) : Except String (List (Nat × Bytes)) := do
    (← sender.getObjValAs? (Array Lean.Json) name).toList.mapM (fun entry => do
      pure (← entry.getObjValAs? Nat "id", ← fromHex (← entry.getObjValAs? String "key_hex")))
  let identityPublic ← fromHex (← sender.getObjValAs? String "identity_public_hex")
  let account ← fromHex (← sender.getObjValAs? String "aci_hex")
  let serverKey ← fromHex (← server.getObjValAs? String "public_key_hex")
  let oneTime ← keys "one_time_prekeys"
  let signed ← keys "signed_prekeys"
  unless identityPublic.length == 32 && account.length == 16 && serverKey.length == 32 &&
      (oneTime ++ signed).all (fun entry => entry.2.length == 32) do throw "export receive shape"
  pure { identityPublic, address := account ++ [1], serverKey
         serverCertificate := ← fromHex (← server.getObjValAs? String "certificate_hex")
         serverId := ← server.getObjValAs? Nat "key_id", oneTime, signed, kyber := ← keys "kyber_prekeys" }

/-- Measurement only (`public_service_controller parse-bench`): the cost per byte of the
parsers this controller runs on revealed bytes. -/
def parseBench : IO Unit := do
  let zero ← IO.rand 0 0   -- not a compile-time constant, so nothing is evaluated ahead
  let frame := TlsWebSocketFrame.stateBytes (TlsWebSocketFrame.start PublicReceive.fast PublicReceive.capacity)
  let control := TlsWebSocketControl.stateBytes (TlsWebSocketControl.initial PublicReceive.fast)
  let response := TlsChatResponse.stateBytes Word64.concrete
    (TlsChatResponse.initial Word64.concrete PublicReceive.fast PublicReceive.capacity (BitVec.ofNat 64 5))
  let upgrade := TlsWebSocketUpgrade.stateBytes (TlsWebSocketUpgrade.start PublicReceive.fast)
  let time (name : String) (rounds : Nat) (run : Nat → Nat) : IO Unit := do
    let start ← IO.monoNanosNow
    let mut sum := 0
    for i in [0:rounds] do sum := sum + run (i + zero)
    let stop ← IO.monoNanosNow
    IO.println s!"{name}: {(stop - start) / rounds / 1000} microseconds per byte (checksum {sum})"
  time "frame parser" 200 (fun i => (TlsWebSocketFrame.runByte PublicReceive.fast PublicReceive.capacity
    (frame ++ [255, BitVec.ofNat 8 (0x82 + i % 2 * 0)])).length)
  time "control queue" 200 (fun i => (TlsWebSocketControl.run PublicReceive.fast (control ++ [0, 0, 0, BitVec.ofNat 8 i])).length)
  time "response parser" 200 (fun i => (TlsChatResponse.runByte VarintDecode.Spqr.concrete Word64.concrete PublicReceive.fast PublicReceive.capacity
    (response ++ [255, 255, 0] ++ [BitVec.ofNat 8 i])).length)
  time "upgrade parser" 200 (fun i => (TlsWebSocketUpgrade.runByte PublicReceive.fast (upgrade ++ List.replicate 28 65 ++ [255, BitVec.ofNat 8 (72 + i % 2)])).length)
  IO.println s!"state sizes: frame {frame.length}, control {control.length}, response {response.length}, upgrade {upgrade.length}"

def main (args : List String) : IO Unit := do
  if args == ["parse-bench"] then
    parseBench
    return
  if let ["db-delete", party, request] := args then
    -- The application's signed delete request: this party submits it to the database nodes,
    -- which act once both parties have. Repeated until all but one node has confirmed.
    let setting (name : String) : IO String := do
      match ← IO.getEnv name with
      | some value => pure value
      | none => throw (IO.userError s!"{name} is required")
    let out := s!"{← setting "SIGNAL_DB_WORK"}/delete.json"
    for _ in [0:40] do
      let run ← IO.Process.output { cmd := ← setting "SIGNAL_DB_CLIENT", args := #["delete", "--network", ← setting "SIGNAL_DB_NETWORK",
        "--key", ← setting "SIGNAL_DB_KEY", "--party", party, "--request", request, "--out", out] }
      unless run.exitCode == 0 do throw (IO.userError s!"database client delete: {run.stderr}")
      let done := match Lean.Json.parse (← IO.FS.readFile out) with
        | .ok json => (json.getObjValAs? Bool "acknowledged").toOption.getD false
        | .error _ => false
      if done then
        IO.println "{\"deleted\":true}"
        return
      IO.sleep 500
    throw (IO.userError "the database nodes did not confirm the delete")
  let [worker,directory,party,hosts,basePort,manifest,session,endpoint,port,hostname,auth,trust,_unused] := args |
    throw (IO.userError "WORKER DIRECTORY PARTY HOSTS PORT MANIFEST SESSION ENDPOINT PORT HOSTNAME AUTH TRUST UNUSED")
  let certificate ← IO.mkRef false
  let operations ← IO.mkRef ([] : List Nat)
  let revealed ← IO.mkRef 0
  -- Authenticated-socket session (SIGNAL_LOCAL_CREDENTIALS: this party's XOR share of the
  -- account id and password, hex): wait for delivered messages instead of sending.
  -- SIGNAL_LOCAL_RECEIVE without credentials: the same session with the account (identity key,
  -- password) loaded from the database nodes; the share is then empty.
  let credentials ← do
    match ← IO.getEnv "SIGNAL_LOCAL_CREDENTIALS" with
    | some share => pure (some share)
    | none => pure ((← IO.getEnv "SIGNAL_LOCAL_RECEIVE").map (fun _ => ""))
  let delivered ← IO.mkRef 0
  let keepalives ← IO.mkRef 0
  let envelopes ← IO.mkRef ([] : List (Nat × Nat))
  -- New contacts received in this session: (contact id, the text of their first message).
  let received ← IO.mkRef ([] : List (Nat × String))
  let refused ← IO.mkRef 0
  let kept ← IO.mkRef (none : Option Bytes)
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
      let app ← liftM (TlsWorker.applicationSession rpc handshake (some (TlsWorker.waitingTransport rpc kept)))
      let sendPublic (bytes : Bytes) : M Unit := do
        let handle ← rpc.call .publicBuffer bytes
        insist (handle.length == 8 && number handle != 0) "invalid public buffer handle"
        TlsApplication.send app ⟨number handle⟩ bytes.length
      -- Two ways to start. Fixture: state admitted by the worker, authenticated upgrade
      -- with private credentials. Local Signal server (SIGNAL_LOCAL_EXPORT): contacts
      -- admitted from the export, and the UNAUTHENTICATED socket, whose upgrade request is
      -- public (sealed-sender sends must not go on an authenticated socket).
      let exportPath ← liftM (IO.getEnv "SIGNAL_LOCAL_EXPORT" : IO (Option String))
      -- TEST stand-in for the database nodes (SIGNAL_LOCAL_STORE, one directory per party): per
      -- contact, this party's key share and the stored state (version, check, ciphertext).
      let storeDirectory ← liftM (IO.getEnv "SIGNAL_LOCAL_STORE" : IO (Option String))
      let freshShare : M Bytes := do
        let random ← liftM (IO.getRandomBytes 32 : IO ByteArray)
        -- below 2^254, so below the share modulus
        pure (random.data.toList.take 31 ++ [(random.data.toList.getD 31 0) &&& 0x3f])
      /- The database nodes (SIGNAL_DB_CLIENT: the `handoff_client` of secret-shared-db, with
      SIGNAL_DB_NETWORK, SIGNAL_DB_KEY and a scratch directory SIGNAL_DB_WORK). Each party
      runs the client itself: its key shares never leave it. Between the parties go only the
      parity shares of a read (whose sums must be zero) and small status bytes. A contact's
      state is one blob, `nonce ‖ check ‖ ciphertext`, which the nodes accept only when both
      parties submit the same bytes as the next version. -/
      let dbClient ← liftM (IO.getEnv "SIGNAL_DB_CLIENT" : IO (Option String))
      let dbEnv (name : String) : M String := do
        match ← liftM (IO.getEnv name : IO (Option String)) with
        | some value => pure value
        | none => throw s!"{name} is required with SIGNAL_DB_CLIENT"
      let dbWork (name : String) : M String := do pure s!"{← dbEnv "SIGNAL_DB_WORK"}/{name}"
      let dbTry (arguments : List String) : M Bool := do
        let some tool := dbClient | throw "no database client"
        let out ← liftM (IO.Process.output { cmd := tool, args := arguments.toArray })
        if out.exitCode != 0 then liftM (IO.eprintln s!"database client {arguments.headD ""}: {out.stderr}" : IO Unit)
        pure (out.exitCode == 0)
      let db (arguments : List String) : M Unit := do
        insist (← dbTry arguments) s!"database client failed: {arguments.headD ""}"
      let dbParty : M (List String) := do
        pure ["--network", ← dbEnv "SIGNAL_DB_NETWORK", "--key", ← dbEnv "SIGNAL_DB_KEY", "--party", party]
      let dbJson (name : String) : M Lean.Json := do
        liftResult (Lean.Json.parse (← liftM (IO.FS.readFile (← dbWork name) : IO String)))
      -- Each party sends the other its bytes (of any length).
      let swap (mine : Bytes) : M Bytes := do
        let size ← rpc.call .exchange (uint 4 mine.length)
        insist (size.length == 4) "invalid exchange reply"
        let width := max mine.length (number size)
        let mut rest := mine ++ List.replicate (width - mine.length) 0
        let mut theirs : Bytes := []
        while !rest.isEmpty do
          theirs := theirs ++ (← rpc.call .exchange (rest.take 60000))
          rest := rest.drop 60000
        pure (theirs.take (number size))
      -- The current time (milliseconds), agreed: each controller reads its own clock, they tell
      -- each other, and both use the later one if the two are within two minutes. (A test may
      -- fix it with SIGNAL_LOCAL_TIMESTAMP, the same for both.)
      let agreedNow : M Nat := do
        match (← liftM (IO.getEnv "SIGNAL_LOCAL_TIMESTAMP" : IO (Option String))).bind String.toNat? with
        | some fixed => pure fixed
        | none =>
          let mine := (← liftM (Std.Time.Timestamp.now : IO Std.Time.Timestamp)).toMillisecondsSinceUnixEpoch.val.toNat
          let theirs := number (← swap (uint 8 mine))
          insist (mine ≤ theirs + 120000 && theirs ≤ mine + 120000) "the two parties' clocks differ by more than two minutes"
          pure (max mine theirs)
      -- A new nonce for each seal of a contact's state: joint randomness.
      let nonce : M Bytes := do
        let random ← rpc.call .publicRandom []
        insist (random.length == 32 && random.take 8 != List.replicate 8 255) "invalid joint randomness"
        pure (random.take 8)
      -- Store a contact's sealed state as blob `version`. Counts once all but one node committed it.
      let dbSubmit (name : String) (authority : List String) (version : Nat) (blob : Bytes) : M Bool := do
        let file ← dbWork s!"blob-{name}"
        liftM (IO.FS.writeBinFile file ⟨blob.toArray⟩ : IO Unit)
        let arguments := ["write-blob"] ++ (← dbParty) ++ authority ++ ["--version", toString version,
          "--blob-file", file, "--out", ← dbWork s!"write-{name}.json"]
        db arguments
        let _ ← swap [1]   -- both parties have submitted
        db arguments       -- repeating it reports the commit to whichever party was first
        pure (((← dbJson s!"write-{name}.json").getObjValAs? Bool "acknowledged").toOption.getD false)
      let dbWrite (contact version : Nat) (authority : List String) : M Bool := do
        let fresh ← nonce
        let stored ← rpc.call .contactSeal (uint 16 contact ++ fresh)
        insist (stored.length > 16) "invalid stored contact state"
        dbSubmit (toString contact) (authority ++ ["--id", toString contact]) version (fresh ++ stored)
      -- Read this party's shares (under the application's request, or of the account's own
      -- row), check them against the other party's with the parity shares, and combine.
      -- Returns the read output and the combined shares.
      let dbRead (source : List String) (name : String) : M (Lean.Json × Lean.Json) := do
        let read ← dbWork s!"{name}-read.json"
        let mine ← dbWork s!"{name}-parity-mine.json"
        let theirs ← dbWork s!"{name}-parity-theirs.json"
        let sums ← dbWork s!"{name}-sums.json"
        let shares ← dbWork s!"{name}-shares.json"
        db (["read"] ++ (← dbParty) ++ source ++ ["--out", read])
        db ["parity", "--summands", read, "--out", mine]
        let received ← swap (← liftM (IO.FS.readBinFile mine : IO ByteArray)).data.toList
        liftM (IO.FS.writeBinFile theirs ⟨received.toArray⟩ : IO Unit)
        db ["verify-signatures", "--network", ← dbEnv "SIGNAL_DB_NETWORK", "--reports", theirs]
        db ["parity-sum", "--mine", mine, "--theirs", theirs, "--out", sums]
        db ["combine", "--summands", read, "--parity-sums", sums, "--out", shares]
        pure (← dbJson s!"{name}-read.json", ← dbJson s!"{name}-shares.json")
      -- From a read: an id's combined share, and its blob (version, bytes in hex).
      let dbEntry (json : Lean.Json) (contact : Nat) : Option Lean.Json :=
        (((json.getObjValAs? (Array Lean.Json) "ids").toOption.getD #[]).toList).find?
          (fun e => (e.getObjValAs? String "id").toOption == some (toString contact))
      let dbShare (shares : Lean.Json) (contact : Nat) : Option String :=
        (dbEntry shares contact).bind (fun e => (e.getObjValAs? String "share").toOption)
      let dbBlob (read : Lean.Json) (contact : Nat) : Option (Nat × String) :=
        ((dbEntry read contact).bind (fun e => (e.getObjVal? "blob").toOption)).bind (fun b =>
          match b.getObjValAs? Nat "version", b.getObjValAs? String "hex" with
          | .ok version, .ok hex => some (version, hex)
          | _, _ => none)
      -- The account's own row on the database nodes (identity key, password, certificate): a
      -- reserved id that the two parties may read and write without an application request.
      let accountId := 2 ^ 128 - 2
      -- Deal this party's half of a new contact's key under the application's signup token
      -- for that id. The dealt summand is this party's share of the key.
      let dbDeal (contact : Nat) (token : String) : M (Option Bytes) := do
        let random ← rpc.call .publicRandom []
        insist (random.length == 32) "invalid joint randomness"
        let dealt ← dbTry (["deal"] ++ (← dbParty) ++ ["--signup-token", token, "--id", toString contact,
          "--session", TlsWorkerProcess.hex (random.take 16), "--out", ← dbWork s!"deal-{contact}.json"])
        let (committed, summand) ← if dealt then do
            let deal ← dbJson s!"deal-{contact}.json"
            let nodes := ((deal.getObjValAs? (Array String) "nodes").toOption.getD #[]).toList
            pure (nodes.map (fun status => if status == "committed" then (1 : UInt8) else 0), (deal.getObjValAs? String "summand").toOption)
          else pure ([], none)
        -- A node commits when the second of the two halves reaches it, and tells only that
        -- party. The parties tell each other which nodes they saw commit; all but one must have.
        let mine := committed ++ List.replicate (16 - committed.length) 0
        let theirs ← swap mine
        let both := (List.zipWith (fun a b => a == 1 || b == 1) mine theirs).filter id
        match summand with
        | some summand =>
          if both.length < 4 then return none
          return some (← liftResult (fromHex summand))
        | none => return none
      -- Per contact: id, key share, version of the stored state it was loaded from (0: none).
      let (accept, known, keyed) ← match exportPath with
        | none => do
          let catalogue ← rpc.call .providerCatalogue []
          insist (catalogue.length ≥ 10) "invalid provider catalogue"
          let state := number (catalogue.take 8)
          let count := number ((catalogue.drop 8).take 2)
          insist (state != 0 && count == 4 && catalogue.length == 10+8*count) "fixture catalogue changed"
          -- Private upgrade request; the expected accept value is public.
          let upgrade ← rpc.call .providerUpgradeOpen (uint 8 state)
          insist (upgrade.length == 38) "invalid upgrade receipt"
          TlsApplication.send app ⟨number (upgrade.take 8)⟩ (number ((upgrade.drop 8).take 2))
          pure (upgrade.drop 10, [(1, ← freshShare, 0), (2, ← freshShare, 0)], false)
        | some path => do
          let text ← liftM (IO.FS.readFile path : IO String)
          let (certificate, identity, records) ← liftResult (readExport text)
          let accountStored ← if dbClient.isSome then do
              let (accountRead, accountShares) ← dbRead ["--account"] "account"
              match dbShare accountShares accountId, dbBlob accountRead accountId with
              | some share, some (_, blob) =>
                let _ ← rpc.call .accountKey (← liftResult (fromHex share))
                let _ ← rpc.call .accountOpen (← liftResult (fromHex blob))
                pure true
              | _, _ => pure false
            else pure false
          -- TEST: until the account's row exists it is admitted from the export.
          unless accountStored do
            let _ ← rpc.call .accountAdmit (identity ++ certificate)
          -- Contacts that exist only in the store (received in an earlier session).
          let extra := ((← liftM (IO.getEnv "SIGNAL_LOCAL_EXTRA_CONTACTS" : IO (Option String))).getD "").splitOn ","
            |>.filterMap String.toNat? |>.map (fun contact => (contact, ([] : Bytes)))
          let wanted := if credentials.isSome then [] else records ++ extra
          let known ← if dbClient.isSome && !wanted.isEmpty then do
            -- From the database nodes, under the application's signed request for these ids.
            let (readJson, sharesJson) ← dbRead ["--request", ← dbEnv "SIGNAL_DB_REQUEST"] "contacts"
            -- A contact created moments ago is not served until the nodes' next epoch.
            let waiting := ((readJson.getObjValAs? (Array String) "not_yet_readable").toOption.getD #[]).toList
            insist (wanted.all (fun (contact, _) => !waiting.contains (toString contact))) "a contact is not readable until the database's next epoch"
            wanted.mapM (fun (contact, record) => do
              let share := dbShare sharesJson contact
              let blob := dbBlob readJson contact
              match share, blob with
              | some share, some (version, blob) =>
                let share ← liftResult (fromHex share)
                let _ ← rpc.call .contactKey (uint 16 contact ++ share)
                -- Both parties must have been given the same blob: the request is agreed.
                let _ ← rpc.call .contactOpen (uint 16 contact ++ (← liftResult (fromHex blob)))
                pure (contact, share, version)
              | _, _ =>
                -- TEST: a contact of the export that the database does not have yet is created
                -- there, under a signup token the harness supplies (SIGNAL_DB_TOKENS/<id>.json).
                insist (!record.isEmpty) "contact is not in the database"
                let some share ← dbDeal contact s!"{← dbEnv "SIGNAL_DB_TOKENS"}/{contact}.json" | throw "dealing a contact key failed"
                let _ ← rpc.call .contactAdmit (uint 16 contact ++ record)
                let _ ← rpc.call .contactKey (uint 16 contact ++ share)
                pure (contact, share, 0))
          else wanted.mapM (fun (contact, record) => do
            let file := storeDirectory.map (fun directory => (directory : System.FilePath) / toString contact)
            let saved ← match file with
              | none => pure none
              | some file => do
                if ← liftM (file.pathExists : IO Bool) then
                  pure (some (← liftResult (fromHex (← liftM (IO.FS.readFile file : IO String)).trimAscii.toString)))
                else pure none
            match saved with
            | some bytes =>
              -- A stored contact: key from the shares, then the state from its ciphertext.
              insist (bytes.length > 56) "stored contact shape"
              let share := bytes.take 32
              let _ ← rpc.call .contactKey (uint 16 contact ++ share)
              let _ ← rpc.call .contactOpen (uint 16 contact ++ bytes.drop 32)
              pure (contact, share, number ((bytes.drop 32).take 8))
            | none =>
              insist (!record.isEmpty) "contact has no stored state"
              let share ← freshShare
              let _ ← rpc.call .contactAdmit (uint 16 contact ++ record)
              let _ ← rpc.call .contactKey (uint 16 contact ++ share)
              pure (contact, share, 0))
          match credentials with
          | some share =>
            -- The password is shared: neither party can open this socket alone.
            if share.isEmpty then insist accountStored "no credentials: the account is not stored and none were given"
            else
              let _ ← rpc.call .accountCredentials (← liftResult (fromHex share))
              if dbClient.isSome && !accountStored then
                -- TEST: the first session that has the account's key and credentials creates its
                -- row on the database nodes (key dealt under a token for the reserved id).
                let some keyShare ← dbDeal accountId s!"{← dbEnv "SIGNAL_DB_TOKENS"}/{accountId}.json" | throw "dealing the account key failed"
                let _ ← rpc.call .accountKey keyShare
                let fresh ← nonce
                let stored ← rpc.call .accountSeal fresh
                insist (stored.length > 16) "invalid stored account state"
                insist (← dbSubmit "account" ["--account"] 1 (fresh ++ stored)) "the database did not acknowledge the account's state"
            let upgrade ← rpc.call .providerUpgradeOpen (uint 8 1)
            insist (upgrade.length == 38) "invalid upgrade receipt"
            TlsApplication.send app ⟨number (upgrade.take 8)⟩ (number ((upgrade.drop 8).take 2))
            pure (upgrade.drop 10, known, true)
          | none =>
            let upgrade ← rpc.call .publicUpgrade []
            insist (upgrade.length == 44) "invalid public upgrade receipt"
            sendPublic (toBytes (RelayUpgrade.anonymousRequest PublicReceive.fast (toBits (upgrade.take 16))))
            pure (upgrade.drop 16, known, true)
      let contacts := known.map (·.1)
      -- Receiving (authenticated socket with an export): a delivered sealed-sender envelope is
      -- opened in the engines as a NEW contact's first message. Public here: our prekey ids the
      -- message names, the Kyber ciphertext, and the message text. The contact's record is
      -- sealed and stored under a new id before the message is acknowledged.
      let receiving ← match exportPath, credentials with
        | some path, some _ => do
          pure (some (← liftResult (readReceive (← liftM (IO.FS.readFile path : IO String)))))
        | _, _ => pure none
      let nextContact ← liftM (IO.mkRef (((← IO.getEnv "SIGNAL_LOCAL_NEW_CONTACT").bind String.toNat?).getD 1000) : IO (IO.Ref Nat))
      let decapsulate (key ciphertext : Bytes) : M Bytes := do
        -- Kyber-1024 decapsulation runs outside the engines, with a key both parties hold.
        let some tool ← liftM (IO.getEnv "SIGNAL_LOCAL_KEM" : IO (Option String)) | throw "SIGNAL_LOCAL_KEM (decapsulation tool) is required"
        let out ← liftM (IO.Process.output { cmd := tool, args := #["kem-decapsulate", TlsWorkerProcess.hex key, TlsWorkerProcess.hex ([8] ++ ciphertext)] })
        insist (out.exitCode == 0) "decapsulation failed"
        let secret ← liftResult (fromHex out.stdout.trimAscii.toString)
        insist (secret.length == 32) "decapsulated secret shape"
        pure secret
      let receiveFirst (keys : ReceiveKeys) : M (Option (Nat × String)) := do
        -- The certificate's expiry is checked against a time both controllers agree on.
        let now ← agreedNow
        let signerId := toBytes (PublicReceive.varint keys.serverId)
        let opened ← rpc.call .envelopeOpen (keys.identityPublic ++ uint 8 now ++ keys.serverKey ++
          uint 2 keys.serverCertificate.length ++ keys.serverCertificate ++ uint 2 signerId.length ++ signerId)
        if opened.head? != some 255 then return none
        insist (opened.length == 14 + 1568) "invalid opened prekey message"
        let find (table : List (Nat × Bytes)) (at_ : Nat) : Option Bytes :=
          (table.find? (·.1 == number ((opened.drop at_).take 4))).map (·.2)
        let oneTime := if opened.getD 1 0 == 1 then find keys.oneTime 2 else some (List.replicate 32 0)
        match oneTime, find keys.signed 6, find keys.kyber 10 with
        | some oneTime, some signed, some kyber =>
          let secret ← decapsulate kyber (opened.drop 14)
          -- With the database, the contact's id is named by the message itself; until then
          -- the contact is held under a provisional id.
          let provisional := 2 ^ 128 - 1
          let contact ← if dbClient.isSome then pure provisional else liftM (nextContact.modifyGet (fun n => (n, n + 1)) : IO Nat)
          let result ← rpc.call .envelopeSession (uint 16 contact ++ keys.address ++ signed ++ oneTime ++ secret ++ uint 8 (2 ^ 63))
          if result.head? != some 255 then return none
          insist (result.length ≥ 3 && result.length == 3 + number ((result.drop 1).take 2)) "invalid received text"
          let text := (String.fromUTF8? ⟨(result.drop 3).toArray⟩).getD ""
          if dbClient.isSome then
            -- The text is the application's signup token (JSON: id, signature). It names the
            -- contact's id and is what authorises the database nodes to create it. A token the
            -- nodes do not accept (forged, or already used) refuses the message.
            let refuse (contact : Nat) : M (Option (Nat × String)) := do
              let _ ← rpc.call .contactEvict (uint 16 contact)
              return none
            -- Fixed width: base64 of the id (16 bytes) and the application's signature (64).
            let pasted ← dbWork "token-received"
            liftM (IO.FS.writeFile pasted text : IO Unit)
            let some tool := dbClient | throw "no database client"
            let parsed ← liftM (IO.Process.output { cmd := tool, args := #["token-id", "--signup-token", pasted, "--require-fixed"] })
            let named := if parsed.exitCode == 0 then parsed.stdout.trimAscii.toString.toNat? else none
            match named with
            | none => refuse provisional
            | some id =>
              if id ≥ accountId then return ← refuse provisional
              let token ← dbWork s!"token-{id}"
              liftM (IO.FS.writeFile token text : IO Unit)
              if (← rpc.call .contactAssign (uint 16 provisional ++ uint 16 id)) != [255] then return none
              match ← dbDeal id token with
              | none => refuse id
              | some share =>
                let _ ← rpc.call .contactKey (uint 16 id ++ share)
                -- Stored (acknowledged by the nodes) before the message is acknowledged.
                if !(← dbWrite id 1 ["--signup-token", token]) then return ← refuse id
                return some (id, text)
          else
          -- Stored before it is acknowledged.
          let share ← freshShare
          let fresh ← nonce
          let _ ← rpc.call .contactKey (uint 16 contact ++ share)
          let stored ← rpc.call .contactSeal (uint 16 contact ++ fresh)
          insist (stored.length > 16) "invalid stored contact state"
          match storeDirectory with
          | some directory =>
            liftM (IO.FS.writeFile ((directory : System.FilePath) / toString contact)
              (TlsWorkerProcess.hex (share ++ fresh ++ stored) ++ "\n") : IO Unit)
          | none => pure ()
          return some (contact, text)
        | _, _, _ =>
          -- The message names a prekey we do not hold.
          TlsWorker.emptyReply rpc .envelopeDrop []
          return none
      let handleEnvelope (kind size : Nat) : M Unit := do
        liftM (envelopes.modify (· ++ [(kind, size)]) : IO Unit)
        match receiving with
        | some keys =>
          if kind == 6 && size > 0 then
            match ← receiveFirst keys with
            | some entry => liftM (received.modify (· ++ [entry]) : IO Unit)
            | none => liftM (refused.modify (· + 1) : IO Unit)
          else
            -- Not a sealed-sender message: not supported, dropped.
            liftM (refused.modify (· + 1) : IO Unit)
            TlsWorker.emptyReply rpc .envelopeDrop []
        | none => TlsWorker.emptyReply rpc .envelopeDrop []
      -- Reveal and parse one authenticated record, byte by byte.
      let record (handle : Nat) (start : PublicReceive.State) : M (PublicReceive.State × Bool) := do
        let mut s := start
        let mut complete := false
        let mut offset := 0
        -- The length alone (an offset past any record reveals no byte).
        let probe ← rpc.call .revealRange (uint 8 handle ++ uint 2 65535 ++ uint 2 1)
        insist (probe.length == 2) "invalid reveal reply"
        let mut length := number probe
        while offset < length do
          if s.skip > 0 then
            -- A server request's body: passed over, never revealed.
            let count := min s.skip (length - offset)
            if s.capture then
              -- A delivered envelope's sealed content goes to the engines as it is.
              let held ← rpc.call .envelopeTake (uint 8 handle ++ uint 2 offset ++ uint 2 count)
              insist (held.length == 4) "invalid envelope reply"
            for _ in [0:count] do
              s ← liftResult (PublicReceive.stepSkipped s)
            offset := offset + count
            -- A completed envelope is dealt with before anything further is read.
            for (kind, size) in s.envelopes do handleEnvelope kind size
            s := { s with envelopes := [] }
            continue
          insist (PublicReceive.mayReveal s) "refusing to reveal a server-initiated message"
          let count := PublicReceive.budget s
          let out ← rpc.call .revealRange (uint 8 handle ++ uint 2 offset ++ uint 2 count)
          insist (out.length ≥ 2 && out.length ≤ 2 + count) "invalid reveal reply"
          length := number (out.take 2)
          let bytes := out.drop 2
          if offset < length then
            insist (!bytes.isEmpty) "missing revealed bytes"
            liftM (revealed.modify (· + bytes.length) : IO Unit)
            -- Diagnostics: the revealed (public) bytes, on request.
            if (← liftM (IO.getEnv "SIGNAL_LOCAL_TRACE" : IO (Option String))).isSome then
              liftM (IO.eprintln s!"revealed {TlsWorkerProcess.hex bytes}" : IO Unit)
            for (byte, index) in bytes.zipIdx do
              let (next, done) ← liftResult (PublicReceive.step s (BitVec.ofNat 8 byte.toNat))
              -- What is left of this step must still be within what may be revealed.
              insist (bytes.length - (index + 1) == 0 || (PublicReceive.mayReveal next && bytes.length - (index + 1) ≤ PublicReceive.budget next))
                "revealed range went past what may be revealed"
              s := next
              complete := complete || done
          offset := offset + (if bytes.isEmpty then 1 else bytes.length)
          for (kind, size) in s.envelopes do handleEnvelope kind size
          s := { s with envelopes := [] }
        return (s, complete)
      -- One send: the engines produce and open the sealed-sender envelope; the request
      -- is assembled here; the engines insert the contact's fields and seal the record.
      -- With the database: the contact's advanced state is stored (and acknowledged by the
      -- nodes) BEFORE its message leaves. If the session dies afterwards the stored state is
      -- never behind what was sent, so no message key or counter can be used twice; at worst
      -- a message that was stored for but never sent leaves a gap in the counter.
      let versions ← liftM (IO.mkRef (known.map (fun (contact, _, version) => (contact, version))) : IO (IO.Ref (List (Nat × Nat))))
      let storeAdvanced (contact : Nat) : M Unit := do
        if dbClient.isSome then
          let version := ((← liftM (versions.get : IO (List (Nat × Nat)))).find? (·.1 == contact)).map (·.2) |>.getD 0
          insist (← dbWrite contact (version + 1) ["--request", ← dbEnv "SIGNAL_DB_REQUEST"]) "the database did not acknowledge a contact's state"
          liftM (versions.modify (fun all => all.map (fun (c, v) => if c == contact then (c, version + 1) else (c, v))) : IO Unit)
      let sendMessage (send : Nat × Bytes) (id : Nat) : M Unit := do
        let sealed ← rpc.call .contactSend (uint 16 send.1 ++ send.2)
        insist (sealed.length ≥ 10) "invalid sealed envelope reply"
        storeAdvanced send.1
        let timestamp := number (sealed.take 8)
        let length := number ((sealed.drop 8).take 2)
        insist (0 < length && length ≤ sealed.length - 10) "invalid sealed envelope length"
        let random ← rpc.call .publicRandom []
        insist (random.length == 32) "invalid joint randomness"
        let (frame, offsets) ← liftResult (PublicRequest.build (toBits ((sealed.drop 10).take length)) timestamp id (toBits (random.take 4)))
        let handle ← rpc.call .contactRequest (uint 16 send.1 ++ offsets.flatMap (uint 2) ++ random.take 4 ++ toBytes frame)
        insist (handle.length == 8 && number handle != 0) "invalid request handle"
        TlsApplication.send app ⟨number handle⟩ frame.length
      -- Contact state at rest (TEST: the two fixture contacts have ids 1 and 2, and each
      -- controller's key share is local randomness standing in for what the database
      -- nodes would deliver). After one send to each contact the state is sealed,
      -- evicted and reloaded from the ciphertext, so the remaining sends prove the
      -- round trip preserved it.
      -- Every seal under a contact's key uses a new version (the version is the cipher's nonce).
      let keyContacts : M Unit := do
        unless keyed do
          for (contact, share, _) in known do
            let _ ← rpc.call .contactKey (uint 16 contact ++ share)
      let reloadContacts : M Unit := do
        for (contact, share, _) in known do
          let version ← nonce
          let stored ← rpc.call .contactSeal (uint 16 contact ++ version)
          insist (stored.length > 16) "invalid stored contact state"
          let _ ← rpc.call .contactEvict (uint 16 contact)
          let _ ← rpc.call .contactKey (uint 16 contact ++ share)
          let _ ← rpc.call .contactOpen (uint 16 contact ++ version ++ stored)
      -- After the sends: every contact's advanced state goes back to the store.
      let writeBack : M Unit := do
        if dbClient.isSome then pure ()   -- stored before each send (storeAdvanced)
        else
        match storeDirectory with
        | none => pure ()
        | some directory =>
          for (contact, share, _) in known do
            let version ← nonce
            let stored ← rpc.call .contactSeal (uint 16 contact ++ version)
            insist (stored.length > 16) "invalid stored contact state"
            liftM (IO.FS.writeFile ((directory : System.FilePath) / toString contact)
              (TlsWorkerProcess.hex (share ++ version ++ stored) ++ "\n") : IO Unit)
      -- The application's request: `notify(ids, message)`. Ids and text are public to both
      -- parties; it expands to one send per contact. The text is 1..256 bytes of UTF-8. What
      -- goes to the engines is the built message of its size class c in 1..4: a validity byte,
      -- a kind byte, 80c bytes of padded content (Content, 0x80, zeros: Signal's padding in
      -- 80-byte blocks) and the 8-byte timestamp. The envelope's size depends on c alone, so
      -- its observer learns c: the Content's length rounded up to 80 bytes (with today's
      -- timestamps, text of 1..68, 69..146, 147..226 or 227..256 bytes), not the exact length.
      let notify(ids : List Nat) (message : String) (timestamp : Nat) : M (List (Nat × Bytes)) := do
        let body := message.toUTF8.data.toList
        insist (0 < body.length && body.length ≤ 256) "notify message must be 1..256 bytes"
        insist (ids.all (· < 2 ^ 128)) "contact ids are u128"
        -- The text is public, so the message content (protobuf, padding) is built here
        -- with the same definition the private path compiles to a circuit
        -- (`PrivateTextNotification.buildPublic`: the smallest of the four size classes that
        -- holds the content; texts of at most 48 bytes get exactly what `build` gave them).
        ids.zipIdx.mapM (fun (contact, index) => do
          let (classes, built) := (PrivateTextNotification.buildPublic 4 (toBits body) (toBits (uint 8 (timestamp + index)))).getD (0, [])
          insist (1 ≤ classes && classes ≤ 4 && built.length == 10 + 80 * classes && built.head? == some 255) "message text rejected"
          pure (contact, toBytes built))
      let inputs ← match exportPath with
        | none => do
          -- TEST: the fixture recipient compares each envelope with pre-computed ciphertext
          -- for these exact texts and timestamps, so each call names one contact here.
          pure ((← notify [1] "Hello, Signal! ☕" 0x1ba60d33800) ++ (← notify [2] "你好，世界" 0x1ba60d33801)
            ++ (← notify [1] "Second private notification" 0x1ba60d33802) ++ (← notify [2] "Delivery ready 😀" 0x1ba60d33803))
        | some _ => do
          -- Two broadcasts to every contact. The timestamp is public and must be the same
          -- for both controllers, so the harness supplies it.
          let base ← agreedNow
          -- Further broadcasts on request (SIGNAL_LOCAL_BROADCASTS, for measuring the cost per message).
          let count := ((← liftM (IO.getEnv "SIGNAL_LOCAL_BROADCASTS" : IO (Option String))).bind String.toNat?).getD 2
          let more ← ((List.range (count - 2)).mapM (fun k => notify contacts
            -- the third broadcast is 200 bytes long (a larger size class)
            (if k == 0 then "MPC broadcast 3 " ++ String.ofList (List.replicate 184 'x') else s!"MPC broadcast {k + 3}") (base + 1000 * (k + 2))))
          pure ((← notify contacts "MPC broadcast one" base) ++ (← notify contacts "MPC broadcast two ☕" (base + 1000)) ++ more.flatten)
      let rec loop (fuel : Nat) (s : PublicReceive.State) (inputs : List (Nat × Bytes)) (completed : Nat) : M Nat := do
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
            -- Replies to completed server requests (each with its own joint mask).
            for request in s.requests do
              let random ← rpc.call .publicRandom []
              insist (random.length == 32) "invalid joint randomness"
              let (frame, message) ← liftResult (PublicReceive.reply request (toBits (random.take 4)))
              -- Nothing is received on this socket: a delivered message is left unacknowledged.
              unless message do sendPublic (toBytes frame)
            let s := { s with requests := [] }
            insist (!complete || wasPending) "unsolicited service response"
            let finished := completed + (if complete then 1 else 0)
            if complete && finished == 1 then TlsApplication.keyUpdate app false
            if s.upgraded && !s.pending then
              match inputs with
              | [] => insist (finished > 0) "private provider supplied no requests"; return finished
              | input::tail =>
                -- Request ids are public: a counter from 2^63, as the service expects.
                let id := 2 ^ 63 + finished
                if finished == 0 then keyContacts
                if finished == 2 then reloadContacts
                sendMessage input id
                loop fuel (PublicReceive.expect s id) tail finished
            else loop fuel s inputs finished
          | .control => loop fuel s inputs completed
          | .closed => throw "TLS closed before private responses"
      -- The authenticated socket: answer the server's requests, keep the connection alive
      -- while nothing arrives, and stop after the expected number of delivered messages.
      -- A delivered message's body stays unrevealed and is not acknowledged yet.
      let closing ← liftM (IO.mkRef false : IO (IO.Ref Bool))
      let rec waiting (fuel : Nat) (s : PublicReceive.State) (pings : Nat) (expected : Nat) : M Nat := do
        match fuel with
        | 0 => throw "receive budget exhausted"
        | fuel+1 =>
          if (← liftM (delivered.get : IO Nat)) ≥ expected then
            -- Before leaving: one keepalive, answered. The server answers in order, so its
            -- reply shows it has read everything sent before it, the acknowledgements included;
            -- closing straight after an acknowledgement could lose it, and the message would be
            -- delivered again.
            if ← liftM (closing.get : IO Bool) then
              if !s.pending then return pings
            else
              liftM (closing.set true : IO Unit)
              let random ← rpc.call .publicRandom []
              insist (random.length == 32) "invalid joint randomness"
              let id := 2 ^ 63 + pings
              sendPublic (toBytes (← liftResult (PublicReceive.keepalive id (toBits (random.take 4)))))
              liftM (keepalives.modify (· + 1) : IO Unit)
              return ← waiting fuel (PublicReceive.expect s id) (pings + 1) expected
          -- 25 seconds of agreed silence, then a keepalive.
          if s.upgraded && !(← TlsWorker.awaitRecord rpc kept 100 250) then
            insist (!s.pending) "keepalive was not answered"
            let random ← rpc.call .publicRandom []
            insist (random.length == 32) "invalid joint randomness"
            let id := 2 ^ 63 + pings
            sendPublic (toBytes (← liftResult (PublicReceive.keepalive id (toBits (random.take 4)))))
            liftM (keepalives.modify (· + 1) : IO Unit)
            waiting fuel (PublicReceive.expect s id) (pings + 1) expected
          else
          match ← TlsApplication.receive app with
          | .application handle =>
            let (s, _) ← record handle.id s
            let mask ← if (PublicReceive.get s.control 127) == 0 then pure [0, 0, 0, 0] else do
              let random ← rpc.call .publicRandom []
              insist (random.length == 32) "invalid joint randomness"
              pure (random.take 4)
            let (s, frames) ← liftResult (PublicReceive.replies s (toBits mask))
            for (kind, frame) in frames do
              sendPublic (toBytes frame)
              insist (kind != 8) "WebSocket peer closed before completion"
            for request in s.requests do
              let random ← rpc.call .publicRandom []
              insist (random.length == 32) "invalid joint randomness"
              let (frame, message) ← liftResult (PublicReceive.reply request (toBits (random.take 4)))
              -- A delivered message was dealt with (stored or refused) while its record was
              -- read; acknowledging it lets the server remove it from the queue.
              if message then liftM (delivered.modify (· + 1) : IO Unit)
              if !message || receiving.isSome then sendPublic (toBytes frame)
            waiting fuel { s with requests := [] } pings expected
          | .control => waiting fuel s pings expected
          | .closed => throw "TLS closed while waiting for messages"
      match credentials with
      | some _ =>
        let expect ← liftM (IO.getEnv "SIGNAL_LOCAL_EXPECT" : IO (Option String))
        let pings ← waiting 4096 (PublicReceive.start (toBits accept)) 0 ((expect.bind String.toNat?).getD 1)
        TlsApplication.abort app
        return pings
      | none =>
        let finished ← loop (256 + 16 * inputs.length) (PublicReceive.start (toBits accept)) inputs 0
        writeBack
        TlsApplication.abort app
        return finished
    let outcome ← action.run
    if !outcome.isOk then
      let _ ← (TlsWorker.emptyReply running.rpc .abort []).run
      pure ()
    let verified ← certificate.get
    let codes ← operations.get
    let passed := verified && outcome.isOk && !codes.contains 18 && (credentials.isSome ||
      (codes.contains 15 && codes.contains 43 &&codes.contains 41 && codes.contains 42 && codes.contains 37 && codes.contains 38))
    IO.println (Lean.Json.mkObj [("passed",toJson passed),("certificate_verified",toJson verified),
      ("responses_completed",toJson (match outcome with | .ok n => n | .error _ => 0)),
      ("bytes_revealed",toJson (← revealed.get)),("messages_delivered",toJson (← delivered.get)),("keepalives",toJson (← keepalives.get)),
      ("envelopes",toJson ((← envelopes.get).map (fun (kind, size) => [kind, size]))),
      ("received",toJson ((← received.get).map (fun (contact, text) => [toString contact, text]))),("refused",toJson (← refused.get)),("private_receive_parsing_used",toJson (codes.contains 18)),
      ("error",toJson (match outcome with | .ok _ => "" | .error e => e))]).compress
    unless passed do throw (IO.userError "public-receive service session failed")
  finally running.stop
