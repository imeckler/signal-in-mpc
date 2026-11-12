import TlsMpc.TlsWebSocketUpgrade
import TlsMpc.TlsWebSocketFrame
import TlsMpc.TlsWebSocketControl
import TlsMpc.TlsChatResponse
import TlsMpc.Signal.Word64Fast
import TlsMpc.Node.Bytes
import TlsMpc.Node.PassOver

/-!
# What the controller reveals of the server's bytes, and how it parses them (pure)

Moved unchanged (names kept) from the controller
(`handshake_backend/EmpHybridWork/PublicServiceController.lean`, which imports this module) in
REORGANIZATION_PLAN.md stage S2. No emitter imports this module.

Everything the server sends back is handled in the clear: each record is still decrypted and
authenticated inside the engines under the shared TLS keys, then its bytes are revealed one at a
time and parsed here, by the same Lean parsers the private profile compiles to circuits, run on
concrete bytes (`PublicReceive.fast`, equal to `ByteAuth.concrete`). What may be revealed is
decided here (`budget`, `mayReveal`, `scan`, `replyScan`, `envelopeScan`): never a server request's
body, never a response's body (unless `openBody`, the registration ceremony only), never a
delivered envelope's payloads. Bodies are passed over unrevealed (`stepPassed`, `stepSkipped`), in
bulk where the parsers only count (`passRoom`, `passBulk`, `passRun_bulk`).

Also here: the replies the controller sends to server requests and control frames (`reply`,
`keepalive`, `ping`, `replies`, `clientFrame`).
-/

open TlsMpc TlsMpc.Signal

namespace PublicReceive

abbrev Byte := BitVec 8
/-- Largest WebSocket message accepted from the server. A prekey response for six devices (the
server's limit) is under 15,000 bytes; it was 4096 before such responses were read. -/
def capacity : Nat := 16384

-- `fast`, the byte operations the parsers below run on (equal to `ByteAuth.concrete`, `fast_eq`),
-- is in `TlsMpc/Node/Bytes.lean`; the parsers' pass-over theorems are in `TlsMpc/Node/PassOver.lean`.
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
  /-- Revealed payload of the response in progress; its body is never revealed and is
  absent here. -/
  reply : List Byte := []
  replySkipped : Bool := false
  /-- The request id of a pending prekey fetch. Only the body of a `200` response with this
  id is kept (still unrevealed) for the engines; every other response body is passed over. -/
  fetch : Option Nat := none
  /-- The bytes being passed over are such a body. -/
  collect : Bool := false
  /-- Length of the prekey response body handed to the engines. -/
  bundle : Option Nat := none
  /-- A response that is not a success ends the session (`false`), or is completed like any
  other and left to the caller, who reads `status` (`true`: a send may be answered 409/410). -/
  lenient : Bool := false
  /-- Status of the last completed response. -/
  status : Nat := 0
  /-- Its `Retry-After` header in seconds, if it had one (`retryAfterOf`). -/
  retryAfter : Option Nat := none
  /-- The registration ceremony only (CEREMONY.md): a response's body is revealed like its other
  fields. Those bodies are a verification session, the new account's ids and our own sender
  certificate: nothing about a contact. Never set by a send or receive session. -/
  openBody : Bool := false
  /-- With `openBody`: the body of the last completed response. -/
  body : List Byte := []

def start (accept : List Byte) : State :=
  { upgrade := TlsWebSocketUpgrade.stateBytes (TlsWebSocketUpgrade.start PublicReceive.fast)
    frame := TlsWebSocketFrame.stateBytes (TlsWebSocketFrame.start PublicReceive.fast capacity)
    control := TlsWebSocketControl.stateBytes (TlsWebSocketControl.initial PublicReceive.fast)
    accept }

/-- Expect the response to the request with this id. -/
def expect (s : State) (id : Nat) : State :=
  { s with pending := true
           response := TlsChatResponse.stateBytes Word64.fast
             (TlsChatResponse.initial Word64.fast PublicReceive.fast capacity (BitVec.ofNat 64 id)) }

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

/-- The varint at `index` is longer than a varint may be: its first 10 bytes are all there and all
have their top bit set (a protobuf varint has at most 10 bytes). `varintAt` returns `none` both for
such a varint and for one the bytes end inside; the scanners below refuse the first and wait for
more bytes of the second. (Without this distinction a server could write an 11-byte varint, which
the scanners would wait on forever while every later byte of the message, its body included, was
revealed: REORGANIZATION_PLAN.md P1.) -/
def varintTooLong (bytes : List Byte) (index : Nat) : Bool :=
  (List.range 10).all fun i => decide (index + i < bytes.length) && decide (128 ≤ (get bytes (index + i)).toNat)

/-- How the varint at `index` ends: complete (its value and the index after it), not yet
(the bytes end inside it), or never (more than 10 bytes: malformed). -/
inductive VarintRead where
  | done (value next : Nat)
  | unfinished
  | tooLong

def varintRead (bytes : List Byte) (index : Nat) : VarintRead :=
  match varintAt bytes index with
  | some (value, next) => .done value next
  | none => if varintTooLong bytes index then .tooLong else .unfinished

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
  let some (_, first) := varintAt bytes 3
    | return (if varintTooLong bytes 3 then .malformed else .more, {})
  let mut pos := first
  let mut fields : Fields := {}
  for _ in [0:bytes.length + 1] do
    if pos ≥ bytes.length then return (.more, fields)
    let tag := (get bytes pos).toNat
    if tag == 0x20 then
      let some (value, next) := varintAt bytes (pos + 1)
        | return (if varintTooLong bytes (pos + 1) then .malformed else .more, fields)
      fields := { fields with id := some value }
      pos := next
    else if tag == 0x0a || tag == 0x12 || tag == 0x2a then
      let some (count, next) := varintAt bytes (pos + 1)
        | return (if varintTooLong bytes (pos + 1) then .malformed else .more, fields)
      if next + count > bytes.length then return (.more, fields)
      let value := (bytes.drop next).take count
      if tag == 0x0a then fields := { fields with verb := value }
      if tag == 0x12 then fields := { fields with path := value }
      pos := next + count
    else if tag == 0x1a then
      let some (count, next) := varintAt bytes (pos + 1)
        | return (if varintTooLong bytes (pos + 1) then .malformed else .more, fields)
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
    let some (key, next) := varintAt bytes pos
      | return (if varintTooLong bytes pos then .malformed else .more false, kind, content)
    let wire := key % 8
    if wire == 0 then
      let some (value, after) := varintAt bytes next
        | return (if varintTooLong bytes next then .malformed else .more false, kind, content)
      if key / 8 == 1 then kind := value
      pos := after
    else if wire == 1 || wire == 2 || wire == 5 then
      let (count, after) ← if wire == 2 then
          match varintAt bytes next with
          | some found => pure found
          | none => return (if varintTooLong bytes next then .malformed else .more false, kind, content)
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

/-! ### Responses

A response (`08 02`) is `1a len { id (08), status (10), message (1a), body (22),
headers (2a) }`; both the server and protobuf libraries write the fields in
number order, so id and status come before the body. Its id, status, message
and headers are revealed; its BODY never is: the body of a prekey response is
the contact's bundle (identity key, prekeys, device and registration ids), and
the body of a 409/410 to a send lists the contact's device ids
(MULTI_DEVICE.md, section 1). The body is passed over exactly as a request's
body is (`skip`), and the one body the engines need, that of a `200` to the
pending prekey fetch, is handed to them unopened (`collect`). -/

structure ReplyFields where
  id : Option Nat := none
  status : Option Nat := none
  body : Option Nat := none   -- body length, if a body field was present

/-- Walk the fields of a response from the revealed bytes (which omit the
body's content). `bodySkipped` says whether the body has been passed over. -/
def replyScan (bytes : List Byte) (bodySkipped : Bool) (inline : Bool := false) : Need × ReplyFields := Id.run do
  if bytes.length < 3 then return (.more, {})
  unless bytes.take 2 == [8, 2] && get bytes 2 == 0x1a do return (.malformed, {})
  let some (_, first) := varintAt bytes 3
    | return (if varintTooLong bytes 3 then .malformed else .more, {})
  let mut pos := first
  let mut fields : ReplyFields := {}
  for _ in [0:bytes.length + 1] do
    if pos ≥ bytes.length then return (.more, fields)
    let tag := (get bytes pos).toNat
    if tag == 0x08 || tag == 0x10 then
      let some (value, next) := varintAt bytes (pos + 1)
        | return (if varintTooLong bytes (pos + 1) then .malformed else .more, fields)
      fields := if tag == 0x08 then { fields with id := some value } else { fields with status := some value }
      pos := next
    else if tag == 0x1a || tag == 0x2a then
      let some (count, next) := varintAt bytes (pos + 1)
        | return (if varintTooLong bytes (pos + 1) then .malformed else .more, fields)
      if next + count > bytes.length then return (.more, fields)
      pos := next + count
    else if tag == 0x22 then
      let some (count, next) := varintAt bytes (pos + 1)
        | return (if varintTooLong bytes (pos + 1) then .malformed else .more, fields)
      if fields.body.isSome then return (.malformed, fields)
      fields := { fields with body := some count }
      -- (`inline`, the ceremony's `openBody`: the body's content is among the bytes, like a header's.)
      if next == bytes.length && !bodySkipped && !inline && count > 0 then return (.skip count, fields)
      if inline && next + count > bytes.length then return (.more, fields)
      pos := if inline then next + count else next
    else return (.malformed, fields)
  return (.more, fields)

/-- The body (field 4) of a response whose bytes were revealed with `openBody`; empty if it has
none or it is not complete. -/
def replyBody (bytes : List Byte) : List Byte := Id.run do
  if bytes.length < 3 then return []
  let some (_, first) := varintAt bytes 3 | return []
  let mut pos := first
  for _ in [0:bytes.length + 1] do
    if pos ≥ bytes.length then return []
    let tag := (get bytes pos).toNat
    if tag == 0x08 || tag == 0x10 then
      let some (_, next) := varintAt bytes (pos + 1) | return []
      pos := next
    else if tag == 0x1a || tag == 0x2a || tag == 0x22 then
      let some (count, next) := varintAt bytes (pos + 1) | return []
      if next + count > bytes.length then return []
      if tag == 0x22 then return (bytes.drop next).take count
      pos := next + count
    else return []
  return []

/-- The headers (field 5, each `name:value`) among a response's revealed bytes. No byte is
revealed for this: a response's headers were always revealed, like its id and status; only its
body is not, and `replyScan` leaves the body's content out of these bytes. -/
def replyHeaders (bytes : List Byte) : List String := Id.run do
  if bytes.length < 3 then return []
  let some (_, first) := varintAt bytes 3 | return []
  let mut pos := first
  let mut headers : List String := []
  for _ in [0:bytes.length + 1] do
    if pos ≥ bytes.length then return headers
    let tag := (get bytes pos).toNat
    if tag == 0x08 || tag == 0x10 then
      let some (_, next) := varintAt bytes (pos + 1) | return headers
      pos := next
    else if tag == 0x1a || tag == 0x2a then
      let some (count, next) := varintAt bytes (pos + 1) | return headers
      if next + count > bytes.length then return headers
      if tag == 0x2a then
        headers := headers ++ [String.ofList (((bytes.drop next).take count).map (fun b => Char.ofNat b.toNat))]
      pos := next + count
    else if tag == 0x22 then
      let some (_, next) := varintAt bytes (pos + 1) | return headers
      pos := next
    else return headers
  return headers

/-- The `Retry-After` header of a response, in seconds (the server sends one with a 429). -/
def retryAfterOf (bytes : List Byte) : Option Nat :=
  (replyHeaders bytes).findSome? fun header =>
    match header.splitOn ":" with
    | [name, value] => if name.trimAscii.toString.toLower == "retry-after" then value.trimAscii.toString.toNat? else none
    | _ => none

/-- How many further bytes of a response are certain not to be body content, given its
revealed bytes. A body byte can only follow the body's key (`22`) and its complete length, so:

* at the end of a field (or before the first): the next key and the byte after it (2);
* inside the id or the status (a varint whose last revealed byte says it continues): the next
  three bytes are the varint's, or its end and then a key, and then at most the first byte
  after that key (3); but never past the varint's 10th byte and the one after it (`11 - j` with
  `j` of its bytes revealed: a 10th byte with its top bit set is refused by `replyScan`);
* after a key, or inside a length: one byte (the length of the body may end there);
* inside the message or a header whose length is known: the rest of it.

Anything unexpected gives 1, and `step` then refuses the byte that does not parse. -/
def replyBudget (bytes : List Byte) (inline : Bool := false) : Nat := Id.run do
  if bytes.length < 3 then return 2
  let some (_, first) := varintAt bytes 3 | return 1
  let mut pos := first
  for _ in [0:bytes.length + 1] do
    if pos ≥ bytes.length then return 2
    let tag := (get bytes pos).toNat
    if tag == 0x08 || tag == 0x10 then
      match varintAt bytes (pos + 1) with
      | some (_, next) => pos := next
      | none => return (if pos + 1 ≥ bytes.length then 1 else min 3 (11 - (bytes.length - (pos + 1))))
    else if tag == 0x1a || tag == 0x2a then
      let some (count, next) := varintAt bytes (pos + 1) | return 1
      if next + count > bytes.length then return next + count - bytes.length
      pos := next + count
    else if tag == 0x22 then
      -- the body's length; its content is not among these bytes (unless `inline`: the ceremony)
      let some (count, next) := varintAt bytes (pos + 1) | return 1
      if inline && next + count > bytes.length then return next + count - bytes.length
      pos := if inline then next + count else next
    else return 1
  return 1

/-- Whether another byte of the current record may be revealed: never a third
payload byte of a message that is neither a response nor a request, and never
a request's body or a response's body (both are counted down in `skip`). -/
def mayReveal (s : State) : Bool :=
  s.skip == 0 && (s.message.length < 2 || s.message == [8, 2] || s.message == [8, 1])

/-- Bytes still unrevealed of the field a request's revealed bytes end in, when
that field is its verb, path or a header (never its body). 0 inside any varint, a too-long one
included (`scan` refuses that one at its 10th byte). -/
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

/-- Bytes still unrevealed of the field a response's revealed bytes end in, when that field is its
message or a header (or, with `inline`, its body): `fieldMissing` for responses. -/
def replyMissing (bytes : List Byte) (inline : Bool := false) : Nat := Id.run do
  if bytes.length < 3 then return 0
  let some (_, first) := varintAt bytes 3 | return 0
  let mut pos := first
  for _ in [0:bytes.length + 1] do
    if pos ≥ bytes.length then return 0
    let tag := (get bytes pos).toNat
    if tag == 0x08 || tag == 0x10 then
      let some (_, next) := varintAt bytes (pos + 1) | return 0
      pos := next
    else if tag == 0x1a || tag == 0x2a || (inline && tag == 0x22) then
      let some (count, next) := varintAt bytes (pos + 1) | return 0
      if next + count > bytes.length then return next + count - bytes.length
      pos := next + count
    else if tag == 0x22 then
      let some (_, next) := varintAt bytes (pos + 1) | return 0
      pos := next
    else return 0
  return 0

/-- Bytes the message in progress has declared and not delivered yet: what is left of the field its
revealed bytes end in (`fieldMissing`, `replyMissing`), of the body being passed over (`skip`), or
of the delivered envelope being walked. -/
def pendingField (s : State) : Nat :=
  if s.message == [8, 1] then
    match s.inner with
    | some (_, _, remaining) => remaining
    | none => if s.skip > 0 then s.skip else fieldMissing s.request
  else if s.message == [8, 2] then
    if s.skip > 0 then s.skip else replyMissing s.reply s.openBody
  else 0

/-- How many bytes may be revealed in one step: as many as are certain to be
bytes this controller may see, given what has been revealed so far. Each step
is a round trip between the parties, so longer steps matter.

* Before the upgrade completes, the response headers end at the first
  CR LF CR LF: with `k` of its bytes just seen, the next `4 - k` bytes cannot
  reach past it.
* A frame's header is at least two bytes, and an extended length is two.
* A control frame's payload, to the end of the frame.
* In a response (`08 02`): what `replyBudget` allows. Never its body.
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
  -- A response used to be revealed to the end of its frame. Its body must stay unrevealed
  -- (a prekey bundle; the device ids of a 409/410), so it is now walked field by field.
  else if s.message == [8, 2] then max 1 (min remaining (replyBudget s.reply s.openBody))
  else if s.message == [8, 1] then max 1 (min remaining (fieldMissing s.request))
  else if s.message.isEmpty then min 2 remaining
  else 1

/-- The upgrade, frame and control part of `step` on one revealed byte: the upgrade parser (before
the upgrade completes), the check that no body byte is being revealed, the response parser's
rollback point at a frame's first byte, the frame parser and the control queue. Returns the state
with the new upgrade, frame and control states, and the byte's frame event: its 8 bytes are
valid, data, control data, message start, frame done, message done, control done, control kind
(`TlsMpc/KernelSpecs/ParseWebSocketFrame.lean`, `eventBytes`). -/
def frameByte (s : State) (byte : Byte) : Except String (State × List Byte) := do
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
  -- The general frame parser: server requests are data frames too.
  let frame := TlsWebSocketFrame.runByte PublicReceive.fast capacity (s.frame ++ [activity, byte])
  unless get frame 0 == on do throw "WebSocket frame rejected"
  let control := TlsWebSocketControl.run PublicReceive.fast (s.control ++ [get frame 2, get frame 6, get frame 7, byte])
  return ({ s with frame := frame.drop 8, control }, frame.take 8)

/-- The message part of `step` on one revealed byte, after `frameByte`: `data` (the byte is a data
frame's payload byte), `done` (it ends the message), `first` (it is the message's first payload
byte), `flags` (the frame event's data, message-start and message-done bytes, as the response parser
takes them). The message's kind (its first two payload bytes), the response parser's feed and its
rollback when the message turns out to be a server request, a response's fields
(`replyScan`), a server request's fields (`scan`) or its delivered envelope (`envelopeAdvance`),
the check that no field runs past the end of its message, and the reset at the message's end.
Returns the new state and whether a successful response to the pending request completed at this
byte. -/
def payloadByte (s : State) (byte : Byte) (data done first : Bool) (flags : List Byte) :
    Except String (State × Bool) := do
  let wasFirst := s.message.length == 1
  let message := if data && s.message.length < 2 then s.message ++ [byte] else s.message
  unless message.length < 2 || message == [8, 2] || message == [8, 1] do
    throw "server-initiated message of an unknown kind: not revealed further"
  if first && done then throw "one-byte message"
  -- What the response parser sees: everything except the payload of a request. The first
  -- payload byte waits until the second shows which kind of message this is.
  let feed : List (List Byte × Byte) :=
    if !data then [(flags, byte)]
    else if first then []
    else if message == [8, 2] then (if s.message.length == 1 then s.held.toList else []) ++ [(flags, byte)]
    else []
  let mut s := { s with message, held := if first then some (flags, byte) else if message.length ≥ 2 then none else s.held }
  let mut complete := false
  -- A server request arriving while a response is awaited: its header bytes were not the
  -- response's.
  if s.pending && wasFirst && message == [8, 1] then s := { s with response := s.rollback }
  if s.pending then
    for (entry, value) in feed do
      if s.pending then
        let out := TlsChatResponse.runByte VarintDecode.Spqr.concrete Word64.fast PublicReceive.fast capacity
          (s.response ++ entry ++ [value])
        unless get out 0 == on do throw "service response rejected or not correlated"
        s := { s with response := out.drop 6 }
        if get out 1 == on then
          unless get out 2 == on || s.lenient do throw "service response was not a success"
          complete := true
          s := { s with pending := false, response := [] }
  if data && message == [8, 2] then
    -- The response's own fields, walked in the clear: its body is passed over, never revealed.
    let reply := if s.reply.isEmpty then [8, 2] else s.reply ++ [byte]
    s := { s with reply }
    match replyScan reply s.replySkipped s.openBody with
    | (.malformed, _) => throw "malformed service response"
    | (.skip count, fields) =>
      -- Kept for the engines only if this is the 200 to the pending prekey fetch.
      let wanted := s.fetch.isSome && fields.id == s.fetch && fields.status == some 200
      s := { s with skip := count, capture := false, collect := wanted, replySkipped := true,
                    bundle := if wanted then some count else s.bundle }
    | (.more, _) => pure ()
    if complete then s := { s with status := ((replyScan s.reply true s.openBody).2.status).getD 0,
                                   retryAfter := if s.openBody then none else retryAfterOf s.reply,
                                   body := if s.openBody then replyBody s.reply else [] }
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
  -- No field (nor a body) may run past the end of its message (fail closed). Once the message's last
  -- frame is known (its FIN is set and its payload is next), what is still declared must fit in the
  -- rest of that frame; at the message's end nothing may still be declared. Checked at the byte that
  -- completes a length, or at the last frame's header, before anything of the field is revealed.
  if get s.frame 4 == on && get s.frame 8 == on && (get s.frame 7).toNat < 8 &&
      pendingField s > (get s.frame 10).toNat * 256 + (get s.frame 11).toNat then
    throw "a field runs past the end of its message"
  if done then
    unless s.skip == 0 && s.inner.isNone do throw "server request ended inside its body"
    unless pendingField s == 0 do throw "a field runs past the end of its message"
    if message == [8, 1] then s := { s with requests := s.requests ++ [s.request] }
    s := { s with message := [], held := none, request := [], bodySkipped := false, reply := [], replySkipped := false }
  return (s, complete)

/-- Consume one revealed byte. Returns the new state and whether a successful
response to the pending request completed at this byte. The frame side (`frameByte`), then the
message side (`payloadByte`). -/
def step (s : State) (byte : Byte) : Except String (State × Bool) := do
  let (s, event) ← frameByte s byte
  let data := get event 1 == on
  payloadByte s byte data (get event 5 == on) (data && s.message.length == 0) [get event 1, get event 3, get event 5]

/-- Pass over one unrevealed body byte of a response: the frame parser advances, and the
response parser is given a zero byte in its place (it only counts a body's bytes). Returns
the new state and whether the pending response completed at this byte. -/
def stepPassed (s : State) : Except String (State × Bool) := do
  unless s.upgraded && s.skip > 0 && s.message == [8, 2] do throw "nothing to pass over"
  let frame := TlsWebSocketFrame.runByte PublicReceive.fast capacity (s.frame ++ [on, 0])
  unless get frame 0 == on && get frame 1 == on do throw "response body left its frame"
  let control := TlsWebSocketControl.run PublicReceive.fast (s.control ++ [get frame 2, get frame 6, get frame 7, 0])
  let mut s := { s with frame := frame.drop 8, control, skip := s.skip - 1 }
  let mut complete := false
  if s.skip == 0 then s := { s with collect := false }
  if s.pending then
    let out := TlsChatResponse.runByte VarintDecode.Spqr.concrete Word64.fast PublicReceive.fast capacity
      (s.response ++ [get frame 1, get frame 3, get frame 5] ++ [0])
    unless get out 0 == on do throw "service response rejected or not correlated"
    s := { s with response := out.drop 6 }
    if get out 1 == on then
      unless get out 2 == on || s.lenient do throw "service response was not a success"
      complete := true
      s := { s with pending := false, response := [], status := ((replyScan s.reply true).2.status).getD 0,
                    retryAfter := retryAfterOf s.reply }
  if get frame 5 == on then
    unless s.skip == 0 do throw "service response ended inside its body"
    s := { s with message := [], held := none, reply := [], replySkipped := false }
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

/-! ### Passing over a body in bulk

The record loop passes over an unrevealed body one byte at a time (`passOne`, `passRun`): each
byte runs the frame parser, the control queue and, for a response, the response parser in the
clear, about a millisecond per byte. Inside a body those parsers only count, so `passBulk k`
advances them by `k` bytes at once, for any `k ≤ passRoom s`; `passRun_bulk` proves that this is
exactly what `k` steps of `passOne` give (the parsers' part: `TlsMpc/Node/PassOver.lean`).
`passRoom` is 0 whenever its conditions do not hold; the loop then takes every byte one at a time. -/

/-- One passed-over body byte, as the record loop takes it. -/
def passOne (s : State) : Except String (State × Bool) :=
  if s.message == [8, 2] then stepPassed s else do pure (← stepSkipped s, false)

/-- `n` passed-over bytes: the state after them, and whether a response completed at one of them. -/
def passRun : Nat → State → Except String (State × Bool)
  | 0, s => pure (s, false)
  | n + 1, s => do
    let (s, done) ← passOne s
    let (s, later) ← passRun n s
    pure (s, done || later)

/-- How many body bytes `passBulk` may pass over at once (0: none). Conditions: the upgrade is
done; the control queue's counts are in range (`PassOver.controlIdle`: a byte with no control
data, frame end or opcode leaves its state unchanged); the frame parser is inside a data frame's
payload (`PassOver.frameRoom`); and, for a response awaited, the response parser is inside its body
(`PassOver.responseRoom`). Never the body's last byte, nor a delivered envelope's (`inner`) last. -/
def passRoom (s : State) : Nat :=
  if s.upgraded ∧ PassOver.controlIdle s.control then
    if s.message = [8, 2] then
      min (s.skip - 1) (if s.pending then min (PassOver.frameRoom s.frame) (PassOver.responseRoom s.response)
        else PassOver.frameRoom s.frame)
    else if s.message = [8, 1] then
      min (s.skip - 1) (match s.inner with
        | some (_, _, remaining) => min (PassOver.frameRoom s.frame) remaining
        | none => PassOver.frameRoom s.frame)
    else 0
  else 0

/-- The state after `k ≤ passRoom s` passed-over body bytes, in one step. -/
def passBulk (k : Nat) (s : State) : State :=
  if k = 0 then s else
  { s with frame := PassOver.frameBulk k s.frame, skip := s.skip - k
           response := if s.message = [8, 2] ∧ s.pending then PassOver.responseBulk k s.response else s.response
           inner := if s.message = [8, 2] then s.inner else
             match s.inner with
             | some (header, passed, remaining) => some (header, passed, remaining - k)
             | none => none }

theorem passed_gets (X : List Byte) :
    get ([255, 255, 0, 0, 0, 0, 0, 0] ++ X) 0 = 255 ∧ get ([255, 255, 0, 0, 0, 0, 0, 0] ++ X) 1 = 255 ∧
    get ([255, 255, 0, 0, 0, 0, 0, 0] ++ X) 2 = 0 ∧ get ([255, 255, 0, 0, 0, 0, 0, 0] ++ X) 3 = 0 ∧
    get ([255, 255, 0, 0, 0, 0, 0, 0] ++ X) 5 = 0 ∧ get ([255, 255, 0, 0, 0, 0, 0, 0] ++ X) 6 = 0 ∧
    get ([255, 255, 0, 0, 0, 0, 0, 0] ++ X) 7 = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem passed_reply_gets (successful : Byte) (X : List Byte) :
    get ([255, 0, successful, 255, 0, 0] ++ X) 0 = 255 ∧ get ([255, 0, successful, 255, 0, 0] ++ X) 1 = 0 :=
  ⟨rfl, rfl⟩

theorem zero_beq_on : ((0 : Byte) == 255) = false := by decide

theorem drop_six (a b c d e f : Byte) (X : List Byte) : List.drop 6 ([a, b, c, d, e, f] ++ X) = X := rfl
theorem drop_eight (a b c d e f g i : Byte) (X : List Byte) : List.drop 8 ([a, b, c, d, e, f, g, i] ++ X) = X := rfl

theorem passOne_bulk (s : State) (h : 1 ≤ passRoom s) : passOne s = .ok (passBulk 1 s, false) := by
  unfold passRoom at h
  by_cases hc : s.upgraded ∧ PassOver.controlIdle s.control
  case neg => rw [if_neg hc] at h; omega
  rw [if_pos hc] at h
  obtain ⟨hup, hidle⟩ := hc
  have hctl := PassOver.control_idle s.control hidle
  obtain ⟨g0, g1, g2, g3, g5, g6, g7⟩ := passed_gets (PassOver.frameBulk 1 s.frame)
  by_cases hm : s.message = [8, 2]
  · rw [if_pos hm] at h
    have hf : 1 ≤ PassOver.frameRoom s.frame := by split at h <;> omega
    have hframe : TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0]) =
        [255, 255, 0, 0, 0, 0, 0, 0] ++ PassOver.frameBulk 1 s.frame := PassOver.frame_step_room capacity s.frame hf
    have hsk : 2 ≤ s.skip := by split at h <;> omega
    have hpos : decide (s.skip > 0) = true := decide_eq_true (by omega)
    have hne : (s.skip - 1 == 0) = false := by rw [beq_eq_false_iff_ne]; omega
    unfold passOne stepPassed
    dsimp only
    rw [hframe, g0, g1, g2, g3, g5, g6, g7, hctl]
    generalize replyScan s.reply true = scanned
    generalize retryAfterOf s.reply = retry
    by_cases hp : s.pending
    · have hr : 1 ≤ PassOver.responseRoom s.response := by rw [if_pos hp] at h; omega
      rw [PassOver.response_step_room capacity s.response hr]
      obtain ⟨r0, r1⟩ := passed_reply_gets (TlsChatResponse.readState Word64.fast fast s.response).successful
        (PassOver.responseBulk 1 s.response)
      simp only [hm, hup, hp, on, beq_self_eq_true, hpos, hne, zero_beq_on, Bool.and_self,
        if_true, if_false, Bool.false_eq_true, pure_bind]
      simp only [r0, r1, beq_self_eq_true, zero_beq_on, if_true, if_false, Bool.false_eq_true]
      rw [drop_six, drop_eight]
      unfold passBulk
      rw [if_neg Nat.one_ne_zero, if_pos ⟨hm, hp⟩, if_pos hm]
      cases s
      simp only at hup hp hm
      subst hup hp hm
      rfl
    · simp only [hm, hup, hp, on, beq_self_eq_true, hpos, hne, zero_beq_on, Bool.and_self,
        if_true, if_false, Bool.false_eq_true, pure_bind]
      rw [drop_eight]
      unfold passBulk
      rw [if_neg Nat.one_ne_zero, if_neg (fun e => hp e.2), if_pos hm]
      cases s
      simp only [Bool.not_eq_true] at hup hp hm
      subst hup hp hm
      rfl
  · rw [if_neg hm] at h
    by_cases hm1 : s.message = [8, 1]
    case neg => rw [if_neg hm1] at h; omega
    rw [if_pos hm1] at h
    have hf : 1 ≤ PassOver.frameRoom s.frame := by split at h <;> omega
    have hframe : TlsWebSocketFrame.runByte fast capacity (s.frame ++ [on, 0]) =
        [255, 255, 0, 0, 0, 0, 0, 0] ++ PassOver.frameBulk 1 s.frame := PassOver.frame_step_room capacity s.frame hf
    have hsk : 2 ≤ s.skip := by split at h <;> omega
    have hpos : decide (s.skip > 0) = true := decide_eq_true (by omega)
    have hne : (s.skip - 1 == 0) = false := by rw [beq_eq_false_iff_ne]; omega
    have h12 : ([8, 1] == ([8, 2] : List Byte)) = false := by decide
    unfold passOne stepSkipped
    dsimp only
    rw [hframe]
    simp only [g0, g1, g2, g5, g6, g7, hctl, hm1, h12, hup, on, beq_self_eq_true, hpos, hne, zero_beq_on,
      Bool.and_self, if_true, if_false, Bool.false_eq_true, pure_bind, drop_eight]
    unfold passBulk
    rw [if_neg Nat.one_ne_zero, if_neg (fun e => hm (e.1)), if_neg hm]
    cases hi : s.inner with
    | none =>
      simp only [pure_bind]
      cases s
      simp only at hup hm1 hi
      subst hup hm1 hi
      rfl
    | some v =>
      obtain ⟨hd, p, rem⟩ := v
      rw [hi] at h
      have hrem : rem > 0 := by simp only at h; omega
      simp only [if_pos hrem, pure_bind]
      cases s
      simp only at hup hm1 hi
      subst hup hm1 hi
      rfl

theorem passBulk_pos (s : State) (k : Nat) (hk : k ≠ 0) : passBulk k s =
    { s with frame := PassOver.frameBulk k s.frame, skip := s.skip - k
             response := if s.message = [8, 2] ∧ s.pending then PassOver.responseBulk k s.response else s.response
             inner := if s.message = [8, 2] then s.inner else
               match s.inner with
               | some (header, passed, remaining) => some (header, passed, remaining - k)
               | none => none } := by
  unfold passBulk; rw [if_neg hk]

/-- After one passed-over byte the room is one byte less. -/
theorem passRoom_one (s : State) (h : 1 ≤ passRoom s) : passRoom (passBulk 1 s) = passRoom s - 1 := by
  rw [passBulk_pos s 1 Nat.one_ne_zero]
  unfold passRoom at h ⊢
  dsimp only
  by_cases hc : s.upgraded ∧ PassOver.controlIdle s.control
  case neg => rw [if_neg hc] at h; omega
  simp only [if_pos hc] at h ⊢
  by_cases hm : s.message = [8, 2]
  · simp only [hm, if_true] at h ⊢
    have hf : 1 ≤ PassOver.frameRoom s.frame := by split at h <;> omega
    rw [PassOver.frameRoom_one _ hf]
    by_cases hp : s.pending
    · simp only [hp, if_true, and_self] at h ⊢
      have hr : 1 ≤ PassOver.responseRoom s.response := by omega
      rw [PassOver.responseRoom_one _ hr]
      omega
    · simp only [hp, if_false, and_false, Bool.false_eq_true] at h ⊢
      omega
  · simp only [hm, if_false] at h ⊢
    by_cases hm1 : s.message = [8, 1]
    case neg => simp only [hm1, if_false] at h; omega
    simp only [hm1, if_true] at h ⊢
    have hf : 1 ≤ PassOver.frameRoom s.frame := by split at h <;> omega
    rw [PassOver.frameRoom_one _ hf]
    cases hi : s.inner with
    | none => rw [hi] at h; simp only at h ⊢; omega
    | some v => obtain ⟨hd, p, rem⟩ := v; rw [hi] at h; simp only at h ⊢; omega

/-- Two bulk steps in a row are one. -/
theorem passBulk_succ (s : State) (k : Nat) (h : k + 1 ≤ passRoom s) :
    passBulk k (passBulk 1 s) = passBulk (k + 1) s := by
  by_cases hk : k = 0
  · subst hk; rfl
  rw [passBulk_pos s 1 Nat.one_ne_zero, passBulk_pos _ k hk, passBulk_pos s (k + 1) (Nat.succ_ne_zero k)]
  unfold passRoom at h
  by_cases hc : s.upgraded ∧ PassOver.controlIdle s.control
  case neg => rw [if_neg hc] at h; omega
  rw [if_pos hc] at h
  have hf : k + 1 ≤ PassOver.frameRoom s.frame := by
    split at h
    · split at h <;> omega
    · split at h
      · split at h <;> omega
      · omega
  dsimp only
  rw [PassOver.frameBulk_succ _ _ hf, Nat.sub_sub, Nat.add_comm 1 k]
  by_cases hm : s.message = [8, 2]
  · by_cases hp : s.pending
    · simp only [hm, hp, if_true] at h
      have hr : k + 1 ≤ PassOver.responseRoom s.response := by omega
      simp only [hm, hp, and_self, if_true, PassOver.responseBulk_succ _ _ hr]
    · simp only [hm, hp, and_false, if_false, if_true, Bool.false_eq_true]
  · simp only [hm, false_and, if_false]
    cases hi : s.inner with
    | none => rfl
    | some v => obtain ⟨hd, p, rem⟩ := v; simp only [Nat.sub_sub, Nat.add_comm 1 k]

/-- **The bulk pass-over is the byte-by-byte one.** For any `k ≤ passRoom s`, passing over `k`
body bytes one at a time (`passRun`, what the record loop did) succeeds, completes no response,
and ends in `passBulk k s`. -/
theorem passRun_bulk (k : Nat) : ∀ (s : State), k ≤ passRoom s → passRun k s = .ok (passBulk k s, false) := by
  induction k with
  | zero => intro s _; rfl
  | succ k ih =>
    intro s h
    have h1 : 1 ≤ passRoom s := by omega
    have first : passOne s = pure (passBulk 1 s, false) := passOne_bulk s h1
    have next : passRun k (passBulk 1 s) = pure (passBulk k (passBulk 1 s), false) :=
      ih (passBulk 1 s) (by rw [passRoom_one s h1]; omega)
    simp only [passRun, first, next, pure_bind, Bool.false_or, passBulk_succ s k h]
    rfl

/-- Passing over `a + b` bytes is passing over `a`, then `b`: the record loop's `passBulk` of
`bulk ≤ passRoom s` bytes followed by `count - bulk` steps of `passOne` is `passRun count`. -/
theorem passRun_add (b : Nat) : ∀ (a : Nat) (s : State), passRun (a + b) s =
    (do let (s1, d1) ← passRun a s; let (s2, d2) ← passRun b s1; pure (s2, d1 || d2))
  | 0, s => by
    simp only [Nat.zero_add, passRun, pure_bind, Bool.false_or]
    cases passRun b s <;> rfl
  | a + 1, s => by
    rw [Nat.add_right_comm]
    simp only [passRun, bind, Except.bind, pure, Except.pure]
    cases passOne s with
    | error e => rfl
    | ok r =>
      obtain ⟨s1, d1⟩ := r
      simp only [passRun_add b a s1, bind, Except.bind, pure, Except.pure]
      cases passRun a s1 with
      | error e => rfl
      | ok r2 =>
        obtain ⟨s2, d2⟩ := r2
        simp only
        cases passRun b s2 with
        | error e => rfl
        | ok r3 => obtain ⟨s3, d3⟩ := r3; simp only [Bool.or_assoc]

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

/-- A masked WebSocket ping with a one-byte payload, as libsignal-net sends after 31 seconds
idle (rust/net/infra/src/ws/connection.rs: `Message::Ping(vec![*ping_count])`). -/
def ping (count : Nat) (mask : List Byte) : List Byte :=
  [0x89, 0x81] ++ mask ++ [BitVec.ofNat 8 count ^^^ get mask 0]

/-- How many control replies are queued (`replies` needs one masking key for each). -/
def queuedReplies (s : State) : Nat := (get s.control 127).toNat

/-- Queued control replies as (kind, masked frame bytes); the queue is cleared. Reply `i` is
masked with `masks[i]`: RFC 6455 section 5.3 requires a fresh masking key for each frame, so the
caller draws one per queued reply (`queuedReplies`). -/
def replies (s : State) (masks : List (List Byte)) : Except String (State × List (Nat × List Byte)) := do
  unless get s.control 0 == on do throw "control queue rejected"
  let count := (get s.control 127).toNat
  unless count ≤ 4 do throw "control queue count"
  let frames ← (List.range count).mapM fun i => do
    let kind := get s.control (128 + i)
    unless kind == 8 || kind == 10 do throw "control kind"
    let some mask := masks[i]? | throw "control reply without a masking key"
    unless mask.length == 4 do throw "control reply masking key shape"
    let out := TlsWebSocketControl.encode PublicReceive.fast
      ([get s.control 0, 0, get s.control (132 + i), kind] ++ mask ++ (s.control.drop (136 + 125 * i)).take 125)
    unless get out 0 == on && get out 1 == 0 do throw "control reply rejected"
    pure (kind.toNat, (out.drop 3).take (get out 2).toNat)
  return ({ s with control := s.control.take 127 ++ List.replicate 509 0 }, frames)

end PublicReceive
