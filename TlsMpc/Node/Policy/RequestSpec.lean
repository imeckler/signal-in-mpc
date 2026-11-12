import TlsMpc.KernelSpecs.SlotBase64

/-!
# Reference encoders for the requests the controller sends (REORGANIZATION_PLAN.md P2, T8)

New file. It defines references only; `RequestProofs.lean` proves the controller's builders
(`TlsMpc/Node/Policy/Request.lean`, `Policy/Receive.lean`) equal to them. No emitter imports it.

Everything here is written from the wire formats, not from the builders:

* **Protobuf** (proto2 wire format: a field is its key `field * 8 + wire type` as a varint, then a
  varint value (wire type 0) or a varint length and the bytes (wire type 2); varints are base-128
  little-endian groups with the high bit on every group but the last, the shortest form).
  The messages are Signal-Server's
  `websocket-resources/src/main/proto/WebSocketProtocol.proto`:
  `WebSocketRequestMessage { verb = 1; path = 2; body = 3; id = 4 (uint64); headers = 5 (repeated) }`,
  `WebSocketResponseMessage { id = 1; status = 2; message = 3; headers = 5; body = 4 }`,
  `WebSocketMessage { type = 1 (REQUEST = 1, RESPONSE = 2); request = 2; response = 3 }`.
  Fields are written in field-number order, as protobuf-java serializes them.
* **JSON** (RFC 8259, compact: no whitespace except what a number slot carries, see
  `Json.number`): strings, booleans, numbers, arrays and objects with members in a stated order.
* **The send body**, Signal-Server's
  `service/src/main/java/org/whispersystems/textsecuregcm/entities/IncomingMessageList.java`
  (`messages`, `online`, `urgent`, `timestamp`) and `IncomingMessage.java` (`type`,
  `destinationDeviceId` (a Java `byte`), `destinationRegistrationId` (a Java `int`), `content`
  (base64, `ByteArrayBase64Deserializer`)). Jackson reads object members in any order; the two
  profiles write them in two orders (`IncomingMessage.json`, `IncomingMessageList.json`).
* **The routes**: `PUT /v1/messages/{destination}` with the `story` query parameter
  (`controllers/MessageController.java`, `@Path("/v1/messages")`, `@Path("/{destination}")`,
  `@QueryParam("story")`), `GET /v2/keys/{identifier}/{device_id}` with `device_id = *`
  (`controllers/KeysController.java`), `GET /v1/keepalive` (`controllers/KeepAliveController.java`),
  the header `Unidentified-Access-Key` (`util/HeaderUtils.java`; 16 bytes in base64,
  `auth/Anonymous.java`), headers as `name: value` strings split at `:` and trimmed
  (`websocket-resources/.../protobuf/ProtobufWebSocketRequestMessage.java`, `getHeaders`), and the
  reply the server expects to its own requests `PUT /api/v1/message` and `PUT /api/v1/queue/empty`
  (`websocket/WebSocketConnection.java`: a status in 200..299, `isSuccessResponse`).
* **WebSocket client frames** (RFC 6455 section 5.2 and 5.3): FIN, RSV1-3 zero, opcode; MASK set;
  payload length in 7 bits, or 126 and 16 bits, or 127 and 64 bits, "the minimal number of bytes
  MUST be used"; the 4-byte masking key; payload octet `i` XOR key octet `i mod 4`. Also a decoder
  (`decodeFrame`) that reads a frame as the server's parser does and reports whether the length
  was minimal.
* **Base64**: RFC 4648 with padding, `TlsMpc.KernelSpecs.SlotBase64.refBase64` (written
  independently there).
-/

namespace TlsMpc.Node.RequestSpec

abbrev Byte := BitVec 8

/-- The UTF-8 bytes of a string. -/
def utf8 (s : String) : List Byte := s.toUTF8.data.toList.map (fun b => BitVec.ofNat 8 b.toNat)

/-! ## Protobuf -/

/-- Base-128 varint with an explicit bound on the number of groups (`fuel`); `pbVarint` gives it
enough. -/
def varintFuel : Nat → Nat → List Byte
  | 0, n => [BitVec.ofNat 8 n]
  | fuel + 1, n => if n < 128 then [BitVec.ofNat 8 n] else BitVec.ofNat 8 (n % 128 + 128) :: varintFuel fuel (n / 128)

/-- The (shortest) protobuf varint of `n`: low 7 bits first, the high bit set on every byte but
the last. -/
def pbVarint (n : Nat) : List Byte := varintFuel n n

/-- A field key: `field * 8 + wire type`, as a varint. -/
def pbKey (field wire : Nat) : List Byte := pbVarint (8 * field + wire)

/-- A varint field (wire type 0). -/
def pbVarintField (field value : Nat) : List Byte := pbKey field 0 ++ pbVarint value

/-- A length-delimited field (wire type 2): string, bytes or an embedded message. -/
def pbBytesField (field : Nat) (value : List Byte) : List Byte := pbKey field 2 ++ pbVarint value.length ++ value

/-- `WebSocketRequestMessage` (`WebSocketProtocol.proto`). `path`, `body` and the headers are bytes
so that the engines' slot values can stand in them. -/
structure WebSocketRequestMessage where
  verb : String
  path : List Byte
  body : Option (List Byte)
  headers : List (List Byte)
  id : Nat

/-- Fields in number order: verb 1, path 2, body 3 (when present), id 4, headers 5. -/
def WebSocketRequestMessage.encode (r : WebSocketRequestMessage) : List Byte :=
  pbBytesField 1 (utf8 r.verb) ++ pbBytesField 2 r.path ++ (match r.body with | some b => pbBytesField 3 b | none => []) ++
    pbVarintField 4 r.id ++ r.headers.flatMap (pbBytesField 5)

/-- `WebSocketResponseMessage` without headers or body. -/
structure WebSocketResponseMessage where
  id : Nat
  status : Nat
  message : String

def WebSocketResponseMessage.encode (r : WebSocketResponseMessage) : List Byte :=
  pbVarintField 1 r.id ++ pbVarintField 2 r.status ++ pbBytesField 3 (utf8 r.message)

/-- `WebSocketMessage`: a request (`type = REQUEST = 1`, field 2) or a response (`type = RESPONSE
= 2`, field 3). -/
inductive WebSocketMessage where
  | request (r : WebSocketRequestMessage)
  | response (r : WebSocketResponseMessage)

def WebSocketMessage.encode : WebSocketMessage → List Byte
  | .request r => pbVarintField 1 1 ++ pbBytesField 2 r.encode
  | .response r => pbVarintField 1 2 ++ pbBytesField 3 r.encode

/-! ## JSON (compact) -/

/-- Values joined with `,`. -/
def commaSeparated : List (List Byte) → List Byte
  | [] => []
  | x :: xs => x ++ xs.flatMap (fun y => utf8 "," ++ y)

/-- A string whose characters need no escaping (base64 text, field names). -/
def jsonString (chars : List Byte) : List Byte := utf8 "\"" ++ chars ++ utf8 "\""

def jsonBool (b : Bool) : List Byte := utf8 (if b then "true" else "false")

/-- A number written in decimal. -/
def jsonNat (n : Nat) : List Byte := utf8 (toString n)

/-- An object with its members in the given order. -/
def jsonObject (members : List (String × List Byte)) : List Byte :=
  utf8 "{" ++ commaSeparated (members.map (fun m => jsonString (utf8 m.1) ++ utf8 ":" ++ m.2)) ++ utf8 "}"

def jsonArray (items : List (List Byte)) : List Byte := utf8 "[" ++ commaSeparated items ++ utf8 "]"

/-! ## The send body (`IncomingMessageList`, `IncomingMessage`) -/

/-- One `IncomingMessage`. The device and registration ids are the number texts the engines
write into their slots (digits then spaces, `SlotDecimal.refPadded`; JSON allows whitespace after
a number). -/
structure IncomingMessage where
  type : Nat
  destinationDeviceId : List Byte
  destinationRegistrationId : List Byte
  content : List Byte

/-- Members in key order (`official = false`), or in libsignal-net's declaration order
(`official = true`: `type`, `destinationDeviceId`, `destinationRegistrationId`, `content`,
rust/net/chat/src/ws/messages.rs `SingleOutboundMessageRepresentation`). The content is base64. -/
def IncomingMessage.json (m : IncomingMessage) (official : Bool) : List Byte :=
  let content := ("content", jsonString (TlsMpc.KernelSpecs.SlotBase64.refBase64 m.content))
  let device := ("destinationDeviceId", m.destinationDeviceId)
  let registration := ("destinationRegistrationId", m.destinationRegistrationId)
  let type := ("type", jsonNat m.type)
  jsonObject (if official then [type, device, registration, content] else [content, device, registration, type])

structure IncomingMessageList where
  messages : List IncomingMessage
  online : Bool
  urgent : Bool
  timestamp : Nat

/-- Members in key order (`messages`, `online`, `timestamp`, `urgent`), or in libsignal-net's
order (`messages`, `online`, `urgent`, `timestamp`, `SendMessageRequest`). -/
def IncomingMessageList.json (l : IncomingMessageList) (official : Bool) : List Byte :=
  let messages := ("messages", jsonArray (l.messages.map (fun m => m.json official)))
  let online := ("online", jsonBool l.online)
  let urgent := ("urgent", jsonBool l.urgent)
  let timestamp := ("timestamp", jsonNat l.timestamp)
  jsonObject (if official then [messages, online, urgent, timestamp] else [messages, online, timestamp, urgent])

/-! ## The requests -/

/-- The sealed-sender envelope type (`TextSecure.proto`, `Envelope.Type.UNIDENTIFIED_SENDER = 6`). -/
def unidentifiedSender : Nat := 6

/-- The send body for one contact: one message per device (envelope, device id text,
registration id text), not online, urgent. -/
def sendBody (devices : List (List Byte × List Byte × List Byte)) (timestamp : Nat) : IncomingMessageList :=
  { messages := devices.map (fun d =>
      { type := unidentifiedSender, destinationDeviceId := d.2.1, destinationRegistrationId := d.2.2, content := d.1 })
    online := false, urgent := true, timestamp := timestamp }

/-- `PUT /v1/messages/{uuid}` (with `?story=false` unless official), sealed sender: the access key
header instead of an account login. -/
def sendRequest (uuid accessKey : List Byte) (body : IncomingMessageList) (id : Nat) (official : Bool) :
    WebSocketRequestMessage :=
  { verb := "PUT"
    path := utf8 "/v1/messages/" ++ uuid ++ (if official then [] else utf8 "?story=false")
    body := some (body.json official)
    headers := [utf8 "content-type: application/json", utf8 "unidentified-access-key: " ++ accessKey]
    id := id }

/-- `GET /v2/keys/{uuid}/*`: every device's prekey bundle, with the access key. -/
def keysRequest (uuid accessKey : List Byte) (id : Nat) : WebSocketRequestMessage :=
  { verb := "GET", path := utf8 "/v2/keys/" ++ uuid ++ utf8 "/*", body := none,
    headers := [utf8 "unidentified-access-key: " ++ accessKey], id := id }

/-- `GET /v1/keepalive`. -/
def keepaliveRequest (id : Nat) : WebSocketRequestMessage :=
  { verb := "GET", path := utf8 "/v1/keepalive", body := none, headers := [], id := id }

/-- The `200 OK` response to the server's request `id`. -/
def okResponse (id : Nat) : WebSocketResponseMessage := { id := id, status := 200, message := "OK" }

/-! ## WebSocket client frames (RFC 6455) -/

/-- Section 5.3: octet `i` of the payload XOR octet `i mod 4` of the masking key. -/
def maskPayload (key payload : List Byte) : List Byte :=
  payload.zipIdx.map (fun p => p.1 ^^^ key.getD (p.2 % 4) 0)

/-- Section 5.2, the second byte onwards of the length: MASK bit set; 7-bit length, or 126 and a
16-bit length, or 127 and a 64-bit length, the shortest that fits. -/
def lengthField (n : Nat) : List Byte :=
  if n < 126 then [BitVec.ofNat 8 (128 + n)]
  else if n < 65536 then [BitVec.ofNat 8 (128 + 126), BitVec.ofNat 8 (n / 256), BitVec.ofNat 8 (n % 256)]
  else BitVec.ofNat 8 (128 + 127) :: (List.range 8).reverse.map (fun i => BitVec.ofNat 8 (n / 256 ^ i % 256))

/-- A complete (FIN) masked client frame. Opcodes: 2 binary, 8 close, 9 ping, 10 pong. -/
def clientFrame (opcode : Nat) (key payload : List Byte) : List Byte :=
  [BitVec.ofNat 8 (128 + opcode)] ++ lengthField payload.length ++ key ++ maskPayload key payload

def binary : Nat := 2
def pingOpcode : Nat := 9

/-- A frame as RFC 6455 section 5.2 reads it. -/
structure Frame where
  fin : Bool
  opcode : Nat
  masked : Bool
  key : List Byte
  /-- Unmasked. -/
  payload : List Byte
  /-- The length was written in the minimal number of bytes. -/
  minimalLength : Bool
  deriving DecidableEq

/-- Big-endian value of bytes. -/
def bigEndian (bytes : List Byte) : Nat := bytes.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Read exactly one frame: `none` if a reserved bit is set or the bytes are not one whole frame. -/
def decodeFrame : List Byte → Option Frame
  | b0 :: b1 :: rest =>
    let len7 := b1.toNat % 128
    let extra := if len7 < 126 then 0 else if len7 = 126 then 2 else 8
    let length := if len7 < 126 then len7 else bigEndian (rest.take extra)
    let minimal := if len7 < 126 then true else if len7 = 126 then decide (126 ≤ length) else decide (65536 ≤ length)
    let masked := decide (128 ≤ b1.toNat)
    let after := rest.drop extra
    let key := if masked then after.take 4 else []
    let data := after.drop key.length
    if b0.toNat / 16 % 8 ≠ 0 ∨ rest.length < extra ∨ after.length < key.length ∨ (masked ∧ after.length < 4) ∨
        data.length ≠ length then none
    else some {
      fin := decide (128 ≤ b0.toNat), opcode := b0.toNat % 16, masked := masked, key := key,
      payload := if masked then maskPayload key data else data, minimalLength := minimal }
  | _ => none

end TlsMpc.Node.RequestSpec
