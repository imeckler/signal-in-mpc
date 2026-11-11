import TlsMpc.EstablishKernels
import TlsMpc.Signal.BundleResponse

/-!
Worker kernels for a contact with several devices: reading a prekey-bundle
response that stays private, binding it to the contact, and the requests that
name the contact. In the conventions of `TlsMpc/HybridKernels.lean`: named input
and output fields, and only outputs marked `opened` may be opened.

The bodies are the definitions of `TlsMpc/Signal/BundleResponse.lean` (which
describes the response and the server sources it was read from). The theorems
are in `TlsMpc/BundleProofs.lean`. The whole flow, what the controllers do and
what must be added to the worker are in
`handshake_backend/EmpHybridWork/MULTI_DEVICE.md`.

What stays private: every byte of the response body — the identity key, every
prekey, signature, key id, registration id and device id — and whether the
body was well formed. What is opened: `shape`, one flag per body byte saying
whether it is JSON punctuation, which determines the number of devices, the
digit counts of each device's five numbers and whether it has a one-time
prekey, and nothing else; and, by the two request kernels, the sealed TLS
record of a request (as `signal-request-ctr`).

## Order of operations for one response body of `SIZE` bytes

 1. `bundle-shape SIZE`: opens `shape`.
 2. Controllers, in the clear: `BundleResponse.layout?` on the flags gives the
    devices' `Widths`; `arguments` gives one parameter list per device.
 3. For each device, `bundle-device SIZE START D R S P K`: private `valid` and
    the bundle fields under exactly the names the establishment kernels take
    (`identityKey`, `signedPrekey`, `signedPrekeySignature`, `kyberPrekey`,
    `kyberPrekeySignature`, `deviceId`, `registrationId`, `signedPrekeyId`,
    `kyberPrekeyId`, and with a one-time prekey `oneTimePrekey`,
    `oneTimePrekeyId`).
 4. Steps 1–5 of `TlsMpc/EstablishKernels.lean` on those fields give the
    private `verified`.
 5. `bundle-bind` with an existing record of the contact: the private
    `verified` that `establish-session` takes (it now also requires the body
    to have parsed and the identity key to be the contact's), and the
    contact's `uuid` and `accessKey` for `establish-session`.
 6. Steps 6–8 of `TlsMpc/EstablishKernels.lean`. `establish-session` opens the
    one status byte; its `conversation` output (certificate, then the 319-byte
    record) is the device's record, and `pending` goes with it.
 7. Messages to that device: `bundle-seal` (`establish-seal` for a text the
    controllers built in the clear), until the device answers.

Requests: `bundle-fetch-ctr` seals `GET /v2/keys/{uuid}/*` and
`bundle-request-ctr` seals `PUT /v1/messages/{uuid}` with one message per
device; both insert the contact's fields into a frame built in the clear.
-/
namespace TlsMpc.BundleKernel
open Std.Tactic.BVDecide
open Signal
open HybridKernel (Kernel Shape Output lookup pub priv sl conversationBytes)
open BundleResponse (Widths)

/-- Size of one device's contact record: session block (262) and metadata (57). -/
def recordBytes : Nat := 319

/-! ### The response -/

def shapeInputs (size : Nat) : List (String × Shape) := [("body", Shape.bytes size)]

/-- Opens, for every byte of the body, whether it is JSON punctuation. -/
def bundleShape (size : Nat) : Kernel :=
  let out := BundleResponse.shape ByteAuth.symbolic (lookup (shapeInputs size) "body")
  { name := "bundle-shape", inputs := shapeInputs size, outputs := [pub "shape" (out.getD 0 [])] }

/-- One device's bundle fields. Everything is private; every field is zero
unless `valid` is 255 (`BundleResponse.device`). -/
def bundleDevice (size start : Nat) (w : Widths) : Kernel :=
  let out := BundleResponse.device ByteAuth.symbolic size start w (lookup (shapeInputs size) "body")
  { name := "bundle-device", inputs := shapeInputs size, outputs := [
      priv "valid" (out.getD 0 []), priv "identityKey" (out.getD 1 []), priv "deviceId" (out.getD 2 []),
      priv "registrationId" (out.getD 3 []), priv "signedPrekeyId" (out.getD 4 []), priv "signedPrekey" (out.getD 5 []),
      priv "signedPrekeySignature" (out.getD 6 []), priv "kyberPrekeyId" (out.getD 7 []),
      priv "kyberPrekey" (out.getD 8 []), priv "kyberPrekeySignature" (out.getD 9 [])] ++
      (if w.oneTime = 0 then [] else [priv "oneTimePrekeyId" (out.getD 10 []), priv "oneTimePrekey" (out.getD 11 [])]) }

def bindInputs : List (String × Shape) :=
  [("record", Shape.bytes recordBytes), ("valid", .bytes 1), ("verified", .bytes 1), ("identityKey", .bytes 32)]

/-- The check `establish-session` takes as `verified`, and the contact's
`uuid` and `accessKey` from one of its existing records
(`BundleResponse.bind`). All private. -/
def bundleBind (_ : Unit := ()) : Kernel :=   -- a function: a constant kernel would be built at program start
  let get := lookup bindInputs
  let out := BundleResponse.bind ByteAuth.symbolic (get "record") (get "valid") (get "verified") (get "identityKey")
  { name := "bundle-bind", inputs := bindInputs, outputs := [
      priv "verified" (out.getD 0 []), priv "uuid" (out.getD 1 []), priv "accessKey" (out.getD 2 [])] }

/-- `bundle-bind` without the comparison of identity keys (`BundleResponse.rebind`): a contact
that registered again is accepted. Opens one byte, `changed`: 255 when the bundle parsed and
verified and its identity key is not the stored one, else 0 (`rebind_rejects` in
`TlsMpc/BundleProofs.lean`: 0 whenever the check fails). Everything else is private. -/
def bundleRebind (_ : Unit := ()) : Kernel :=   -- a function, as `bundleBind`
  let get := lookup bindInputs
  let out := BundleResponse.rebind ByteAuth.symbolic (get "record") (get "valid") (get "verified") (get "identityKey")
  { name := "bundle-rebind", inputs := bindInputs, outputs := [
      priv "verified" (out.getD 0 []), priv "uuid" (out.getD 1 []), priv "accessKey" (out.getD 2 []),
      pub "changed" (out.getD 3 [])] }

/-! ### Messages on a session the device has not answered -/

def sealInputs (cert content : Nat) : List (String × Shape) :=
  [("conversation", Shape.bytes (conversationBytes cert 80)), ("pending", .bytes EstablishKernel.pendingBytes),
    ("localAddress", .bytes 17), ("text", .bytes (content + 10)), ("ephemeralPublic", .word), ("senderPublic", .word),
    ("ephemeralAgreement", .word), ("staticAgreement", .word)]

/-- `establish-seal` for a text the controllers built in the clear, as
`signal-seal-built`: `text` is validity (1), kind (1), `content` padded
content bytes, timestamp (8) — for `content = 80` the 90-byte output of
`PrivateTextNotification.build`. The record keeps its layout: its 80-byte
plaintext slot holds the first 80 bytes of the content. Everything else is as
in `EstablishKernel.establishSeal`. The envelope's length depends on the
certificate size, the one-time flag, the four widths and `content` only. -/
def bundleSeal (cert : Nat) (withOneTime : Bool) (content counterWidth previousWidth epochWidth indexWidth : Nat) :
    Kernel :=
  let inputs := sealInputs cert content
  let get := lookup inputs
  let record := get "conversation"
  let certificate := sl record 0 cert
  let metadata := sl record (cert + 262) 57
  let text := get "text"
  let out := Establish.sealMessage Aes.symbolic Varint64.symbolic Sha256Ripple.ops ByteAuth.symbolic withOneTime
    ⟨counterWidth, previousWidth, true⟩ ⟨epochWidth, indexWidth, 0, false⟩ content (sl record cert 262) metadata
    (get "pending") certificate (get "localAddress") text (get "ephemeralPublic") (get "senderPublic")
    (get "ephemeralAgreement") (get "staticAgreement")
  { name := "bundle-seal", inputs, outputs := [
      pub "status" (out.getD 0 []), priv "conversation" (certificate ++ (out.getD 1 []).take 262 ++ metadata),
      pub "timestamp" (sl text (2 + content) 8), pub "envelope" (out.getD 2 [])] }

/-! ### Requests that name the contact

As `HybridKernel.signalRequestCtr`: `frame` is the complete masked WebSocket
frame built in the clear with zero bytes in the slots; the kernel formats the
private values, applies the public WebSocket mask (the payload starts at
`payloadAt`, so the mask byte for frame index `i` is `mask[(i - payloadAt) % 4]`),
inserts them, and encrypts the TLS record without its tag (`gcm-tag` adds it). -/

def requestInputs (extra : String × Shape) (size : Nat) : List (String × Shape) :=
  [("clientApplication", Shape.bytes 60), ("sequence", .bytes 8), extra, ("frame", .bytes size), ("mask", .bytes 4)]

def sealSlots (name : String) (extra : String × Shape) (size payloadAt : Nat) (valid : BVExpr 8)
    (slots : List (Nat × List (BVExpr 8))) : Kernel :=
  let a := ByteAuth.symbolic
  let g := Gcm.symbolic
  let inputs := requestInputs extra size
  let get := lookup inputs
  let secretAt (index : Nat) : Option (BVExpr 8) := slots.findSome? (fun slot =>
    if slot.1 ≤ index && index < slot.1 + slot.2.length then some (HybridService.at' slot.2 (index - slot.1)) else none)
  let plaintext := (get "frame").zipIdx.map (fun pair => match secretAt pair.2 with
    | some secret => a.xor pair.1 (a.xor secret (HybridService.at' (get "mask") ((pair.2 - payloadAt) % 4)))
    | none => pair.1)
  let block := get "clientApplication"
  let inner := TlsRecord.inner g plaintext 23 0
  let ciphertext := Gcm.ctr g (HybridKernel.gcmExpanded block) (TlsRecord.nonce g (HybridKernel.blockIv block) (get "sequence")) inner
  { name, inputs, outputs := [
      pub "accepted" [valid], pub "header" (TlsRecord.header g (inner.length + 16)),
      pub "ciphertext" (ByteAuth.release a valid ciphertext),
      priv "pad" (HybridKernel.gcmPad block (get "sequence"))] }

/-- 255 exactly when the record is a live one (session version 4). -/
def live (record : List (BVExpr 8)) : BVExpr 8 :=
  ByteAuth.eqMask ByteAuth.symbolic (HybridService.at' record 0) (ByteAuth.symbolic.const 4)

/-- The prekey fetch for a contact: the UUID (36 characters) and the access
key in base64 (24) from one of the contact's records. -/
def bundleFetchCtr (size payloadAt uuidAt keyAt : Nat) : Kernel :=
  let a := ByteAuth.symbolic
  let extra := ("record", Shape.bytes recordBytes)
  let record := lookup (requestInputs extra size) "record"
  sealSlots "bundle-fetch-ctr" extra size payloadAt (live record)
    [(uuidAt, RelayEncoding.uuid a (sl record 262 16)), (keyAt, RelayEncoding.base64 a (sl record 278 16))]

/-- A send with one message per device: `records` is the devices' records one
after the other. The UUID and access key come from the first; each device's
id (3 characters) and registration id (10), space padded, from its own. -/
def bundleRequestCtr (size payloadAt uuidAt keyAt : Nat) (devices : List (Nat × Nat)) : Kernel :=
  let a := ByteAuth.symbolic
  let extra := ("records", Shape.bytes (recordBytes * devices.length))
  let records := lookup (requestInputs extra size) "records"
  let each := devices.zipIdx.map (fun (slot, index) =>
    let record := sl records (recordBytes * index) recordBytes
    let metadata := sl record 262 57
    let device := HybridKernel.paddedDecimal (RelayRequest.word Varint64.symbolic a metadata 48 1) 3
    let registration := HybridKernel.paddedDecimal (RelayRequest.word Varint64.symbolic a metadata 49 4) 10
    (a.and (live record) (a.and device.1 registration.1), [(slot.1, device.2), (slot.2, registration.2)]))
  sealSlots "bundle-request-ctr" extra size payloadAt
    (each.foldl (fun mask device => a.and mask device.1) (a.const 255))
    ([(uuidAt, RelayEncoding.uuid a (sl records 262 16)), (keyAt, RelayEncoding.base64 a (sl records 278 16))] ++
      each.flatMap (·.2))

/-! ### Lookup by name -/

/-- The parameter lists of `bundle-device`, one per device, for a body of
`size` bytes with the given layout. -/
def arguments (size : Nat) (ws : List Widths) : List (List String) :=
  ((BundleResponse.starts BundleResponse.firstItem ws).zip ws).map (fun (start, w) =>
    ["bundle-device", toString size, toString start, toString w.device, toString w.registration, toString w.signed,
      toString w.oneTime, toString w.kyber])

/-- Slots lie in the payload, inside the frame, and do not overlap. -/
def slotsOk (size payloadAt : Nat) (slots : List (Nat × Nat)) : Bool :=
  slots.all (fun slot => payloadAt ≤ slot.1 && slot.1 + slot.2 ≤ size) &&
    slots.zipIdx.all (fun (x, i) => slots.zipIdx.all (fun (y, j) => i == j || x.1 + x.2 ≤ y.1 || y.1 + y.2 ≤ x.1))

def pairs : List Nat → Option (List (Nat × Nat))
  | [] => some []
  | x :: y :: rest => (pairs rest).map ((x, y) :: ·)
  | _ => none

set_option compiler.extract_closed false in   -- or `bundleBind ()` would be built at program start
/-- Kernel named on the command line, with its public shape parameters:

`bundle-shape SIZE`, `bundle-device SIZE START D R S P K` (the item's offset
and the digit counts of its device id, registration id, signed prekey id,
one-time prekey id — 0 when it has none — and Kyber prekey id), `bundle-bind`,
`bundle-seal CERT ONETIME CONTENT COUNTER PREVIOUS EPOCH INDEX` (as
`establish-seal`; `CONTENT` is the padded content size, a multiple of 80),
`bundle-fetch-ctr SIZE PAYLOAD UUID KEY` (frame size, where the WebSocket
payload starts, and the two slots' offsets),
`bundle-request-ctr SIZE PAYLOAD UUID KEY DEVICE REGISTRATION ...` (one pair
of slot offsets per device). -/
def find (arguments : List String) : Option Kernel :=
  match arguments with
  | [] => none
  | name :: rest =>
      match name, rest.mapM (·.toNat?) with
      | "bundle-bind", some [] => some (bundleBind ())
      | "bundle-rebind", some [] => some (bundleRebind ())
      | "bundle-shape", some [size] => if 2540 ≤ size && size ≤ 65536 then some (bundleShape size) else none
      | "bundle-device", some [size, start, d, r, s, p, k] =>
          let w : Widths := ⟨d, r, s, p, k⟩
          let stop := start + BundleResponse.size (BundleResponse.item w)
          if w.ok && BundleResponse.firstItem ≤ start && size ≤ 65536 &&
              (stop + 2 == size || stop + 1 + 2465 + 2 ≤ size) then some (bundleDevice size start w) else none
      | "bundle-seal", some [cert, oneTime, content, cw, pw, ew, iw] =>
          -- `content`: 80k padded bytes, or the official clients' 80k − 1 (CLIENT_FINGERPRINT.md).
          if cert ≤ 1024 && oneTime ≤ 1 && 79 ≤ content && content ≤ 320 && (content % 80 == 0 || content % 80 == 79) &&
              1 ≤ cw && cw ≤ 5 && 1 ≤ pw && pw ≤ 5 && 1 ≤ ew && ew ≤ 10 && 1 ≤ iw && iw ≤ 5 then
            some (bundleSeal cert (oneTime == 1) content cw pw ew iw) else none
      | "bundle-fetch-ctr", some [size, payloadAt, uuidAt, keyAt] =>
          if size ≤ 16384 && 6 ≤ payloadAt && slotsOk size payloadAt [(uuidAt, 36), (keyAt, 24)] then
            some (bundleFetchCtr size payloadAt uuidAt keyAt) else none
      | "bundle-request-ctr", some (size :: payloadAt :: uuidAt :: keyAt :: rest) =>
          (pairs rest).bind (fun devices =>
            if size ≤ 16384 && 6 ≤ payloadAt && 1 ≤ devices.length && devices.length ≤ 16 &&
                slotsOk size payloadAt ([(uuidAt, 36), (keyAt, 24)] ++
                  devices.flatMap (fun slot => [(slot.1, 3), (slot.2, 10)])) then
              some (bundleRequestCtr size payloadAt uuidAt keyAt devices) else none)
      | _, _ => none

end TlsMpc.BundleKernel
