/-!
# T1's reference: which bytes of the server's stream may be revealed

REORGANIZATION_PLAN.md section 8, T1 (proof track P1). New file; it changes no definition, imports
nothing from this repository, and no emitter or executable imports it.

Everything a server connection delivers after the TLS handshake is one byte stream: the
concatenated plaintexts of the server's application-data records. The controller reveals some of
those bytes to both nodes and passes over the others unrevealed (`PublicReceive` in
`Policy/Receive.lean`, driven by `record` in the controller). This file says, independently of that
code and from the protocol descriptions alone, which bytes it may reveal: `classify` gives every
byte of a stream a `Class`, and a class is either public or `secret`.

## The protocol, layer by layer

1. **The upgrade response** (RFC 6455 section 4.2.2): an HTTP response head, up to and including
   the first blank line (CR LF CR LF). Public: `head`.
2. **WebSocket frames** (RFC 6455 section 5.2): a header of 2 bytes (FIN, RSV1-3, opcode; MASK,
   7-bit length), then 2 more for a 16-bit length (code 126), then the payload. Header bytes are
   public (`frameHeader`); so is the payload of a control frame (close, ping, pong: `control`).
   The payloads of a binary message's frames (opcode 2, then continuations, opcode 0, up to the
   frame with FIN) are concatenated into one message.
3. **Messages** (Signal's `WebSocketMessage` protobuf): `08 01` + field 2 (`12 len request`) is a
   server request, `08 02` + field 3 (`1a len response`) a response. The first two bytes say which
   (`kind`, public). Every byte after the second of a message of any other kind is `unknown`
   (secret).
4. **A server request** (`WebSocketRequestMessage`): verb (field 1, key `0a`), path (2, `12`),
   body (3, `1a`), id (4, `20`), headers (5, `2a`). Keys, lengths and the id are `structure`;
   the verb's, path's and headers' bytes are `text` (public). The body's bytes are `body`
   (secret: the body of a delivered message can name its sender), except that the body of a
   request whose path (the last path field before the body) is `/api/v1/message` is an
   **Envelope** (Signal's `Envelope` protobuf), read field by field: its keys, lengths and varint
   values (type, timestamps, flags) are `structure`, and the payload of every length-delimited
   or fixed-width field (the sealed content, and the fields that name a sender when a message is
   not sealed) is `envelope` (secret).
5. **A response** (`WebSocketResponseMessage`): id (field 1, `08`), status (2, `10`), message
   (3, `1a`), body (4, `22`), headers (5, `2a`). Keys, lengths, id and status are `structure`;
   message and headers are `text`; the body is `body` (secret: the body of a prekey response is the
   contact's bundle; that of a 409/410 to a send lists the contact's devices). With `openBody`
   (the registration ceremony only, CEREMONY.md) a response's body is `text` instead.

Protobuf varints (keys of the envelope, lengths, values) are at most 10 bytes.

## Leaving the protocol: fail closed

A byte that cannot occur in the protocol at that place makes the stream malformed: a frame header
with a reserved bit, an undefined or out-of-place opcode (a continuation with no message in
progress, a new message inside a fragmented one, a fragmented control frame; text, opcode 1, is
outside this binary profile), a masked server frame, a 64-bit length (code 127: more than this
protocol's messages), a control frame with an extended length, a 16-bit length below 126; a
wrapper key other than `12` (request) or `1a` (response); a request or response key outside the
lists above; an envelope key of wire type 3, 4, 6 or 7; a varint whose 10th byte still has its top
bit set. The offending byte itself keeps its class (a header byte, a key, a varint byte), and
**every later byte of the stream is `error` (secret)**: `failClosed`.

Not errors here (the controller may still refuse them, which is stricter): the declared length of
the request or response wrapper (the reference reads the request's or response's fields to the
end of the message, as the server writes them; the length bytes are `structure`), a field that runs
past the end of its message or of the body, message sizes, close codes, and anything after a close
frame.

## What T1 asks (`Policy/ReceiveProofs.lean`, `Policy/ReceiveTest.lean`)

The controller reveals byte `q` of a stream only if `allowed openBody stream q`, except possibly the
one byte right after the first malformed byte (`firstError`): the controller reveals bytes in
runs it computes in advance and checks each byte after it is revealed, so it may have revealed the
byte after an offending key before it refuses the key and stops.

The deployed policy does NOT meet this on streams with a varint longer than 10 bytes (the
scanners take such a varint for an unfinished one and reveal the rest of the message, body
included): `ReceiveTest.overlongRequest`, `ReceiveTest.overlongResponse`.
-/

namespace ReceiveSpec

abbrev Byte := BitVec 8

/-- Why a byte may, or may not, be revealed. -/
inductive Class where
  /-- The HTTP head of the upgrade response, up to its blank line. -/
  | head
  /-- A WebSocket frame header byte. -/
  | frameHeader
  /-- The payload of a control frame (close, ping, pong). -/
  | control
  /-- The first two payload bytes of a message: which kind it is. -/
  | kind
  /-- A protobuf key, a length, a varint value (id, status, envelope type and timestamps). -/
  | structure
  /-- The content of a request's verb, path or header, a response's message or header. -/
  | text
  /-- **Secret.** The content of a request's body (not a delivered envelope) or a response's body. -/
  | body
  /-- **Secret.** The payload of a delivered envelope's length-delimited or fixed-width field. -/
  | envelope
  /-- **Secret.** A payload byte after the second of a message that is neither a request nor a
  response. -/
  | unknown
  /-- **Secret.** Any byte after the first byte that does not fit the protocol. -/
  | error
  deriving DecidableEq, Repr

def Class.secret : Class → Bool
  | .body | .envelope | .unknown | .error => true
  | _ => false

/-- Every byte of `bytes` of class `c`. -/
def fill {α : Type} (c : Class) (bytes : List α) : List Class := bytes.map fun _ => c

/-! ### Protobuf varints -/

/-- Where a varint at the head of a list of bytes ends. -/
inductive VarintEnd where
  /-- After `n` bytes (`1 ≤ n ≤ 10`). -/
  | done (n : Nat)
  /-- The bytes end inside it. -/
  | short
  /-- Its 10th byte still has its top bit set: malformed. -/
  | tooLong

/-- `varintEnd 10 bytes`: where the varint at the head of `bytes` ends (`allowed`: bytes left). -/
def varintEnd : (allowed : Nat) → List Byte → VarintEnd
  | 0, _ => .tooLong
  | _ + 1, [] => .short
  | k + 1, b :: rest =>
    if b.toNat < 128 then .done 1 else
    match varintEnd k rest with
    | .done n => .done (n + 1)
    | other => other

/-- The value of a varint's bytes (least significant group first). -/
def varintValue : List Byte → Nat
  | [] => 0
  | b :: rest => b.toNat % 128 + 128 * varintValue rest

/-- A varint, then what follows it: its bytes are `structure`, and `next value rest` classifies the
bytes after it. A varint the bytes end inside is all `structure`; a varint of more than 10 bytes
is malformed: its 10 bytes are `structure` and every byte after them `error`. -/
def varintThen (bytes : List Byte) (next : Nat → List Byte → List Class) : List Class :=
  match varintEnd 10 bytes with
  | .done n => fill .structure (bytes.take n) ++ next (varintValue (bytes.take n)) (bytes.drop n)
  | .short => fill .structure bytes
  | .tooLong => fill .structure (bytes.take 10) ++ fill .error (bytes.drop 10)

/-- A length-delimited field's length and content: the length is a varint (`structure`), the
content is the next `length` bytes (`content` classifies them), and `next content rest`
classifies what follows. -/
def delimitedThen (bytes : List Byte) (content : List Byte → List Class)
    (next : List Byte → List Byte → List Class) : List Class :=
  varintThen bytes fun length after =>
    content (after.take length) ++ next (after.take length) (after.drop length)

/-! ### Envelopes, requests, responses

Each reads fields until its bytes end. `fuel` bounds the recursion; the callers give more fuel than
there are bytes (each field consumes at least one byte), so it never runs out. -/

/-- A delivered `Envelope`'s fields: keys, lengths and varint values are `structure`; the payload
of a length-delimited (wire type 2) or fixed-width (1: 8 bytes, 5: 4 bytes) field is `envelope`. -/
def envelope : (fuel : Nat) → List Byte → List Class
  | 0, bytes => fill .error bytes
  | _ + 1, [] => []
  | fuel + 1, bytes@(_ :: _) =>
    varintThen bytes fun key after =>
      match key % 8 with
      | 0 => varintThen after fun _ rest => envelope fuel rest
      | 1 => fill .envelope (after.take 8) ++ envelope fuel (after.drop 8)
      | 5 => fill .envelope (after.take 4) ++ envelope fuel (after.drop 4)
      | 2 => delimitedThen after (fill .envelope) fun _ rest => envelope fuel rest
      | _ => fill .error after

/-- The path of a delivered message. -/
def messagePath : List Byte := "/api/v1/message".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat

/-- A request's body: an envelope if the path so far is `/api/v1/message`, else secret whole. -/
def requestBody (path content : List Byte) : List Class :=
  if path = messagePath then envelope (content.length + 1) content else fill .body content

/-- A `WebSocketRequestMessage`'s fields; `path` is the last path field read so far. -/
def request : (fuel : Nat) → (path : List Byte) → List Byte → List Class
  | 0, _, bytes => fill .error bytes
  | _ + 1, _, [] => []
  | fuel + 1, path, key :: rest =>
    if key = 0x20 then
      .structure :: varintThen rest fun _ after => request fuel path after
    else if key = 0x0a ∨ key = 0x12 ∨ key = 0x2a then
      .structure :: delimitedThen rest (fill .text) fun content after =>
        request fuel (if key = 0x12 then content else path) after
    else if key = 0x1a then
      .structure :: delimitedThen rest (requestBody path) fun _ after => request fuel path after
    else .structure :: fill .error rest

/-- A `WebSocketResponseMessage`'s fields. -/
def response (openBody : Bool) : (fuel : Nat) → List Byte → List Class
  | 0, bytes => fill .error bytes
  | _ + 1, [] => []
  | fuel + 1, key :: rest =>
    if key = 0x08 ∨ key = 0x10 then
      .structure :: varintThen rest fun _ after => response openBody fuel after
    else if key = 0x1a ∨ key = 0x2a then
      .structure :: delimitedThen rest (fill .text) fun _ after => response openBody fuel after
    else if key = 0x22 then
      .structure :: delimitedThen rest (fill (if openBody then .text else .body)) fun _ after =>
        response openBody fuel after
    else .structure :: fill .error rest

/-- `WebSocketMessage`'s wrapper of a request (key `12`) or response (key `1a`): the key and the
length are `structure`, and `fields` classifies the rest of the message. -/
def wrapper (key : Byte) (fields : List Byte → List Class) : List Byte → List Class
  | [] => []
  | k :: rest =>
    if k = key then .structure :: varintThen rest fun _ after => fields after
    else .structure :: fill .error rest

/-- A whole message's payload (its frames' payloads, concatenated). -/
def message (openBody : Bool) : List Byte → List Class
  | a :: b :: rest =>
    if a = 8 ∧ b = 1 then .kind :: .kind :: wrapper 0x12 (fun fields => request (fields.length + 1) [] fields) rest
    else if a = 8 ∧ b = 2 then .kind :: .kind :: wrapper 0x1a (fun fields => response openBody (fields.length + 1) fields) rest
    else .kind :: .kind :: fill .unknown rest
  | short => fill .kind short

/-! ### Frames -/

/-- A network-byte-order 16-bit number. -/
def word (hi lo : Byte) : Nat := hi.toNat * 256 + lo.toNat

/-- The frames after the upgrade. `msg`: the payload of the binary message in progress so far
(empty between messages); `fragmented`: a binary message is in progress (its last frame had FIN
clear). A data frame's payload bytes get their classes in the whole message read so far: those
of `msg ++ payload` after `msg` (the classes above depend only on the bytes before). -/
def frames (openBody : Bool) : (fuel : Nat) → (msg : List Byte) → (fragmented : Bool) → List Byte → List Class
  | 0, _, _, bytes => fill .error bytes
  | _ + 1, _, _, [] => []
  | fuel + 1, msg, fragmented, b0 :: rest =>
    let fin := decide (128 ≤ b0.toNat)
    let opcode := b0.toNat % 16
    let isControl := decide (opcode = 8 ∨ opcode = 9 ∨ opcode = 10)
    let headerFits := b0.toNat / 16 % 8 = 0 ∧
      ((opcode = 2 ∧ !fragmented) ∨ (opcode = 0 ∧ fragmented) ∨ (isControl ∧ fin))
    if ¬headerFits then .frameHeader :: fill .error rest else
    match rest with
    | [] => [.frameHeader]
    | b1 :: rest =>
      let len7 := b1.toNat % 128
      if 128 ≤ b1.toNat ∨ len7 = 127 ∨ (isControl ∧ len7 = 126) then .frameHeader :: .frameHeader :: fill .error rest else
      -- The payload: `length` bytes after a header of `header` bytes.
      let payload (header : List Class) (length : Nat) (rest : List Byte) : List Class :=
        let bytes := rest.take length
        let classes := if isControl then fill .control bytes else (message openBody (msg ++ bytes)).drop msg.length
        let (msg', fragmented') :=
          if isControl then (msg, fragmented) else if fin then ([], false) else (msg ++ bytes, true)
        header ++ classes ++ (if bytes.length < length then [] else frames openBody fuel msg' fragmented' (rest.drop length))
      if len7 = 126 then
        match rest with
        | hi :: lo :: rest =>
          if word hi lo < 126 then [.frameHeader, .frameHeader, .frameHeader, .frameHeader] ++ fill .error rest
          else payload [.frameHeader, .frameHeader, .frameHeader, .frameHeader] (word hi lo) rest
        | short => .frameHeader :: .frameHeader :: fill .frameHeader short
      else payload [.frameHeader, .frameHeader] len7 rest

/-! ### The stream -/

/-- Where the upgrade response's head ends: the length up to and including its first CR LF CR LF. -/
def headLength : List Byte → Option Nat
  | 13 :: 10 :: 13 :: 10 :: _ => some 4
  | _ :: rest => (headLength rest).map (· + 1)
  | [] => none

/-- After the first `error`, every byte is `error`. -/
def failClosed : List Class → List Class
  | [] => []
  | .error :: rest => .error :: fill .error rest
  | c :: rest => c :: failClosed rest

/-- The frames of an upgraded connection (`bytes` starts at a frame boundary, no message in
progress). -/
def classifyFrames (openBody : Bool) (bytes : List Byte) : List Class :=
  failClosed (frames openBody (bytes.length + 1) [] false bytes)

/-- **The reference classifier.** The class of every byte of a server connection's stream,
from its first byte (the upgrade response). -/
def classify (openBody : Bool) (stream : List Byte) : List Class :=
  match headLength stream with
  | none => fill .head stream
  | some n => fill .head (stream.take n) ++ classifyFrames openBody (stream.drop n)

/-- Byte `q` of the stream may be revealed. -/
def allowedIn (classes : List Class) (q : Nat) : Bool :=
  match classes[q]? with
  | some c => !c.secret
  | none => false

/-- The first byte after the first malformed byte, if any (`failClosed`: every later byte is
`error`). The one byte the controller may have revealed past the end of the protocol. -/
def firstError (classes : List Class) : Option Nat := classes.findIdx? (· == .error)

def allowed (openBody : Bool) (stream : List Byte) (q : Nat) : Bool := allowedIn (classify openBody stream) q

end ReceiveSpec
