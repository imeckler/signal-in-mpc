import TlsMpc.Node.Bytes
import TlsMpc.Signal.RelayEncoding

/-!
# The request templates the controller builds in the clear (pure)

Moved from the controller (`handshake_backend/EmpHybridWork/PublicServiceController.lean`, which
imports this module and uses the same names) in REORGANIZATION_PLAN.md stage S2. No emitter
imports this module.

The relay request around an opened sealed-sender envelope, assembled in the clear. Fixed-width
slots are left as zero bytes for the engines to fill: recipient UUID text (36), access key in
base64 (24), device id (3, space padded) and registration id (10, space padded). Everything else,
including the request id, timestamp and WebSocket mask, is public.

Each builder is split into the message it frames (`sendMessage`, `fetchMessage`,
`devicesMessage`: a list of pieces, text or slot) and the framing (`build`, `assemble`), so that
the theorems about them (`TlsMpc/KernelSpecs/RequestFrame.lean`, restated in
`TlsMpc/Security.lean` section 2d) are about these very definitions.
-/

open TlsMpc TlsMpc.Signal

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

/-- The send body as libsignal-net serializes it (`SendMessageRequest` and
`SingleOutboundMessageRepresentation` in rust/net/chat/src/ws/messages.rs, serde_json, field
declaration order): `messages` [`type`, `destinationDeviceId`, `destinationRegistrationId`,
`content`], `online`, `urgent`, `timestamp`. The device and registration ids are still the
engines' space-padded slots (3 and 10 bytes), so this is canonical JSON except for those spaces
(CLIENT_FINGERPRINT.md, section (d)). One entry per envelope, in the contact's device order. -/
def officialJson (envelopes : List (List Byte)) (timestamp : Nat) : List Piece :=
  let messages : List Piece := (envelopes.zipIdx.map fun (envelope, index) =>
    [Piece.bytes (text ((if index == 0 then "" else ",") ++ "{\"type\":6,\"destinationDeviceId\":")), .slot (2 + 2 * index) 3,
     .bytes (text ",\"destinationRegistrationId\":"), .slot (3 + 2 * index) 10,
     .bytes (text ",\"content\":\"" ++ RelayEncoding.base64 PublicReceive.fast envelope ++ text "\"}")]).flatten
  [.bytes (text "{\"messages\":[")] ++ messages ++
    [.bytes (text ("],\"online\":false,\"urgent\":true,\"timestamp\":" ++ toString timestamp ++ "}"))]

/-- The message `build` frames: `PUT /v1/messages/{uuid}` for one device. Slot 0 is the UUID,
1 the access key, 2 the device id, 3 the registration id. -/
def sendMessage (envelope : List Byte) (timestamp id : Nat) (official : Bool) : List Piece :=
  let json : List Piece := if official then officialJson [envelope] timestamp else [
    .bytes (text "{\"messages\":[{\"content\":\"" ++ RelayEncoding.base64 PublicReceive.fast envelope ++
      text "\",\"destinationDeviceId\":"), .slot 2 3,
    .bytes (text ",\"destinationRegistrationId\":"), .slot 3 10,
    .bytes (text (",\"type\":6}],\"online\":false,\"timestamp\":" ++ toString timestamp ++ ",\"urgent\":true}"))]
  let request := field 10 [.bytes (text "PUT")] ++
    field 18 ([.bytes (text "/v1/messages/"), .slot 0 36] ++ (if official then [] else [.bytes (text "?story=false")])) ++
    field 26 json ++ [.bytes (32 :: varint id)] ++
    field 42 [.bytes (text "content-type: application/json")] ++
    field 42 [.bytes (text "unidentified-access-key: "), .slot 1 24]
  Piece.bytes [8, 1] :: field 18 request

/-- The masked WebSocket frame with zeroed slots, and the frame offsets of the
UUID, access-key, device and registration slots. -/
def build (envelope : List Byte) (timestamp id : Nat) (mask : List Byte) (official : Bool := false) :
    Except String (List Byte × List Nat) := do
  let message := sendMessage envelope timestamp id official
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

/-! Requests for a contact with several devices (MULTI_DEVICE.md). As above, every private
value is a slot of zero bytes that the engines fill (`bundle-fetch-ctr`,
`bundle-request-ctr`); slot 0 is the UUID, slot 1 the access key, and slots `2 + 2i`,
`3 + 2i` the device id and registration id of device `i`. -/

/-- The masked WebSocket frame of a message with zeroed slots, where its payload starts, and
the frame offset of each of the `slots` slots. -/
def assemble (message : List Piece) (mask : List Byte) (slots : Nat) : Except String (List Byte × Nat × List Nat) := do
  let size := total message
  unless 0 < size && size < 65536 && mask.length == 4 do throw "request size"
  let header : List Byte := (if size < 126 then [130, BitVec.ofNat 8 (128 + size)]
    else [130, 254, BitVec.ofNat 8 (size / 256), BitVec.ofNat 8 size]) ++ mask
  let mut frame := header.toArray
  let mut offsets := Array.replicate slots 0
  for piece in message do
    match piece with
    | .bytes value =>
      for byte in value do
        frame := frame.push (byte ^^^ mask.getD ((frame.size - header.length) % 4) 0)
    | .slot index width =>
      offsets := offsets.set! index frame.size
      frame := frame ++ Array.replicate width 0
  return (frame.toList, header.length, offsets.toList)

/-- The message `buildFetch` frames: `GET /v2/keys/{uuid}/*` with the contact's access key. -/
def fetchMessage (id : Nat) : List Piece :=
  let request := field 10 [.bytes (text "GET")] ++
    field 18 [.bytes (text "/v2/keys/"), .slot 0 36, .bytes (text "/*")] ++ [.bytes (32 :: varint id)] ++
    field 42 [.bytes (text "unidentified-access-key: "), .slot 1 24]
  Piece.bytes [8, 1] :: field 18 request

/-- `GET /v2/keys/{uuid}/*` with the contact's access key: every device's prekey bundle. -/
def buildFetch (id : Nat) (mask : List Byte) : Except String (List Byte × Nat × List Nat) :=
  assemble (fetchMessage id) mask 2

/-- The message `buildDevices` frames: `PUT /v1/messages/{uuid}` with one message per device, in
the contact's device order. -/
def devicesMessage (envelopes : List (List Byte)) (timestamp id : Nat) (official : Bool) : List Piece :=
  let messages : List Piece := (envelopes.zipIdx.map fun (envelope, index) =>
    [Piece.bytes (text ((if index == 0 then "" else ",") ++ "{\"content\":\"") ++ RelayEncoding.base64 PublicReceive.fast envelope ++
      text "\",\"destinationDeviceId\":"), .slot (2 + 2 * index) 3,
     .bytes (text ",\"destinationRegistrationId\":"), .slot (3 + 2 * index) 10, .bytes (text ",\"type\":6}")]).flatten
  let json : List Piece := if official then officialJson envelopes timestamp else [.bytes (text "{\"messages\":[")] ++ messages ++
    [.bytes (text ("],\"online\":false,\"timestamp\":" ++ toString timestamp ++ ",\"urgent\":true}"))]
  let request := field 10 [.bytes (text "PUT")] ++
    field 18 ([.bytes (text "/v1/messages/"), .slot 0 36] ++ (if official then [] else [.bytes (text "?story=false")])) ++
    field 26 json ++ [.bytes (32 :: varint id)] ++
    field 42 [.bytes (text "content-type: application/json")] ++
    field 42 [.bytes (text "unidentified-access-key: "), .slot 1 24]
  Piece.bytes [8, 1] :: field 18 request

/-- `PUT /v1/messages/{uuid}` with one message per device, in the contact's device order. -/
def buildDevices (envelopes : List (List Byte)) (timestamp id : Nat) (mask : List Byte) (official : Bool := false) :
    Except String (List Byte × Nat × List Nat) := do
  unless !envelopes.isEmpty do throw "no devices"
  assemble (devicesMessage envelopes timestamp id official) mask (2 + 2 * envelopes.length)

end PublicRequest
