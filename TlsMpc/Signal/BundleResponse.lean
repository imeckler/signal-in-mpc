import TlsMpc.Signal.ReceiveFirst
import TlsMpc.Signal.RelayEncoding
import TlsMpc.Signal.PrivateBuffer

/-!
A prekey-bundle response (`GET /v2/keys/{uuid}/{device or *}`), held as private
bytes, as functions that are generic in the circuit operations. Instantiated
with the symbolic operations they are the bodies of the kernels in
`TlsMpc/BundleKernels.lean`; with the concrete operations they are the
specification those kernels are proved against (`TlsMpc/BundleProofs.lean`).

The body is the JSON that Signal-Server's Jackson mapper writes for
`entities/PreKeyResponse.java` (fields in declaration order, no whitespace):

    {"identityKey":"<44>","devices":[ITEM,ITEM,...]}

    ITEM = {"deviceId":D,"registrationId":R,
            "signedPreKey":{"keyId":S,"publicKey":"<44>","signature":"<86>"},
            "preKey":null | {"keyId":P,"publicKey":"<44>"},
            "pqPreKey":{"keyId":K,"publicKey":"<2092>","signature":"<86>"}}

(written here on several lines; the server sends one). `D R S P K` are decimal
numbers. The quoted values are standard base64: 44 characters for a 33-byte
key (`05 ‖ key`, `util/ECPublicKeyAdapter.java`, `IdentityKeyAdapter.java`),
2092 for the 1569-byte Kyber key (`08 ‖ key`, `KEMPublicKeyAdapter.java`), and
86 characters WITHOUT padding for a 64-byte signature
(`util/ByteArrayAdapter.java`).

Everything except the digit counts of the five numbers and whether `preKey` is
`null` is fixed text or fixed-length base64, so the body's layout is determined
by which of its bytes are JSON punctuation (`" , : [ ] { }`): none of these
occurs in base64 or in a number. `shape` computes exactly that, one flag per
byte, and it is the only thing about the body that is ever opened. `layout?`
(public arithmetic, for the controllers) turns the opened flags into the
`Widths` of each device, accepting only flags that are exactly those of the
template. `device` then checks every byte of one device's item against the
template for those widths and decodes its fields.

Proved in this file: every definition commutes with a homomorphism of the
operations (the step from circuit to values). The meaning of the per-character
functions and of `layout?` is in `TlsMpc/BundleProofs.lean`.
-/
namespace TlsMpc.Signal.BundleResponse
open Std.Tactic.BVDecide
open Establish (part)
open ReceiveFirst (expect all either any isSet)
open RelayEncoding (literal slice)

/-! ### Small pieces -/

/-- The byte whose bit `k` is the mask `bits[first + k]`. No gates. -/
def fromBits (a : ByteAuth.Ops B) (bits : List B) (first : Nat) : B :=
  (List.range 8).foldl (fun acc k => a.xor acc (a.and (OpenResult.get a bits (first + k)) (a.const (2 ^ k))))
    (a.const 0)

/-- Sum of two numbers given as mask bits, least significant first, modulo `2^width`. -/
def add (a : ByteAuth.Ops B) (width : Nat) (x y : List B) : List B :=
  (PrivateBuffer.addLoop a x y (List.range width) (a.const 0)).1

/-- `xs` when `present`, nothing otherwise (a public choice). -/
def optional (present : Bool) (xs : List α) : List α := if present then xs else []

/-! ### The opened shape -/

/-- `" , : [ ] { }` -/
def punctuation : List Nat := [34, 44, 58, 91, 93, 123, 125]

/-- 255 exactly when the byte is JSON punctuation. -/
def structural (a : ByteAuth.Ops B) (c : B) : B :=
  any a (punctuation.map (fun k => ByteAuth.eqMask a c (a.const k)))

/-- One flag per byte of the body. -/
def shape (a : ByteAuth.Ops B) (body : List B) : List (List B) := [body.map (structural a)]

/-! ### Base64 -/

/-- 255 exactly when the byte is a character of the standard base64 alphabet. -/
def sextetValid (a : ByteAuth.Ops B) (c : B) : B :=
  let b := a.maskBit c
  let letter := a.and (a.not (b 7)) (b 6)
  -- the low five bits are 1..26
  let inRange := a.and (either a (either a (b 0) (b 1)) (either a (b 2) (either a (b 3) (b 4))))
    (a.not (a.and (a.and (b 4) (b 3)) (either a (b 2) (a.and (b 1) (b 0)))))
  let low := a.and (a.and (a.not (b 7)) (a.not (b 6))) (b 5)
  let digit := a.and (a.and low (b 4)) (a.not (a.and (b 3) (either a (b 2) (b 1))))
  let symbol := a.and (a.and low (a.not (b 4))) (a.and (b 3) (a.and (b 1) (b 0)))
  either a (a.and letter inRange) (either a digit symbol)

/-- The six-bit value of a base64 character (meaningful when `sextetValid`):
the character plus a class-dependent constant, modulo 64. `A–Z`: +63,
`a–z`: +57, `0–9`: +4, `+`: +19, `/`: +16. -/
def sextetValue (a : ByteAuth.Ops B) (c : B) : B :=
  let b := a.maskBit c
  let letter := a.and (a.not (b 7)) (b 6)
  let upper := a.and letter (a.not (b 5))
  let lower := a.and letter (b 5)
  let low := a.and (a.and (a.not (b 7)) (a.not (b 6))) (b 5)
  let digit := a.and low (b 4)
  let symbol := a.and low (a.not (b 4))
  let plus := a.and symbol (a.not (b 2))
  let slash := a.and symbol (b 2)
  let offset := [a.xor (a.xor upper lower) plus, a.xor upper plus, a.xor upper digit, a.xor upper lower,
    a.xor (a.xor upper lower) (a.xor plus slash), a.xor upper lower]
  fromBits a (add a 6 ((List.range 6).map b) offset) 0

/-- Byte `j` of the decoding, from the six-bit values of the characters. -/
def byteAt (a : ByteAuth.Ops B) (values : List B) (j : Nat) : B :=
  if j % 3 = 0 then
    a.xor (slice a (OpenResult.get a values (4 * (j / 3))) 0 6 2) (slice a (OpenResult.get a values (4 * (j / 3) + 1)) 4 2 0)
  else if j % 3 = 1 then
    a.xor (slice a (OpenResult.get a values (4 * (j / 3) + 1)) 0 4 4) (slice a (OpenResult.get a values (4 * (j / 3) + 2)) 2 4 0)
  else
    a.xor (slice a (OpenResult.get a values (4 * (j / 3) + 2)) 0 2 6) (slice a (OpenResult.get a values (4 * (j / 3) + 3)) 0 6 0)

/-- Bits of the last character that carry no data. -/
def spare (count : Nat) : Nat := if count % 4 = 2 then 4 else if count % 4 = 3 then 2 else 0

/-- The bytes of `chars`, unpadded base64 (`chars.length * 3 / 4` bytes). -/
def decode (a : ByteAuth.Ops B) (chars : List B) : List B :=
  (List.range (chars.length * 3 / 4)).map (byteAt a (chars.map (sextetValue a)))

/-- 255 exactly when every character is in the alphabet and the unused bits of
the last one are zero (the encoding is the canonical one). -/
def decodeValid (a : ByteAuth.Ops B) (chars : List B) : B :=
  a.and (all a (chars.map (sextetValid a)))
    ((List.range (spare chars.length)).foldl
      (fun mask i => a.and mask (a.not (a.maskBit (sextetValue a (OpenResult.get a chars (chars.length - 1))) i)))
      (a.const 255))

/-! ### Decimal numbers -/

/-- 255 exactly when the byte is `0`–`9`. -/
def digitValid (a : ByteAuth.Ops B) (c : B) : B :=
  a.and (a.and (a.and (a.not (a.maskBit c 7)) (a.not (a.maskBit c 6))) (a.and (a.maskBit c 5) (a.maskBit c 4)))
    (a.not (a.and (a.maskBit c 3) (either a (a.maskBit c 2) (a.maskBit c 1))))

/-- `10 · acc + digit` on `width` mask bits, least significant first. -/
def pushDigit (a : ByteAuth.Ops B) (width : Nat) (acc : List B) (c : B) : List B :=
  add a width (add a width (a.const 0 :: acc) (a.const 0 :: a.const 0 :: a.const 0 :: acc))
    ((List.range 4).map (a.maskBit c))

/-- The value of a string of digits as mask bits, least significant first.
`4 · digits` bits: enough for any number of that many digits. -/
def numberBits (a : ByteAuth.Ops B) (chars : List B) : List B :=
  chars.foldl (pushDigit a (4 * chars.length)) (List.replicate (4 * chars.length) (a.const 0))

/-- 255 exactly when `chars` is a decimal number as JSON writes it (digits
only, no leading zero unless it is the only digit) and below `2^limit`. -/
def numberValid (a : ByteAuth.Ops B) (limit : Nat) (chars : List B) : B :=
  all a (chars.map (digitValid a) ++
    optional (decide (1 < chars.length)) [a.not (ByteAuth.eqMask a (OpenResult.get a chars 0) (a.const 48))] ++
    ((numberBits a chars).drop limit).map a.not)

/-- The number as `count` big-endian bytes. -/
def numberBytes (a : ByteAuth.Ops B) (count : Nat) (chars : List B) : List B :=
  (List.range count).map (fun j => fromBits a (numberBits a chars) (8 * (count - 1 - j)))

/-! ### The template -/

/-- A stretch of the body: fixed text, or a value of a public size. -/
inductive Piece where
  | text (s : String)
  | field (size : Nat)

def Piece.size : Piece → Nat
  | .text s => s.toUTF8.size
  | .field n => n

def size (pieces : List Piece) : Nat := (pieces.map Piece.size).foldl (· + ·) 0

/-- 255 exactly when every text piece is in place, the pieces laid out from `start`. -/
def literals (a : ByteAuth.Ops B) (body : List B) : Nat → List Piece → B
  | _, [] => a.const 255
  | start, .text s :: rest => a.and (expect a body start (literal a s)) (literals a body (start + s.toUTF8.size) rest)
  | start, .field n :: rest => literals a body (start + n) rest

/-- The bytes of the `index`-th field piece, the pieces laid out from `start`. -/
def fieldOf (body : List B) : Nat → List Piece → Nat → List B
  | _, [], _ => []
  | start, .text s :: rest, index => fieldOf body (start + s.toUTF8.size) rest index
  | start, .field n :: _, 0 => part body start n
  | start, .field n :: rest, index + 1 => fieldOf body (start + n) rest index

/-- Digit counts of one device's numbers; `oneTime = 0` when `preKey` is `null`. -/
structure Widths where
  device : Nat
  registration : Nat
  signed : Nat
  oneTime : Nat
  kyber : Nat
  deriving BEq, Repr

/-- Bounds from the server's types: device id a `byte`, registration id at most
`0x3FFF`, key ids at most `2^31 − 1`. -/
def Widths.ok (w : Widths) : Bool :=
  1 ≤ w.device && w.device ≤ 3 && 1 ≤ w.registration && w.registration ≤ 5 && 1 ≤ w.signed && w.signed ≤ 10 &&
    w.oneTime ≤ 10 && 1 ≤ w.kyber && w.kyber ≤ 10

def header : List Piece := [.text "{\"identityKey\":\"", .field 44, .text "\",\"devices\":["]

/-- Where the first device's item starts. -/
def firstItem : Nat := 73

def item (w : Widths) : List Piece :=
  [.text "{\"deviceId\":", .field w.device, .text ",\"registrationId\":", .field w.registration,
    .text ",\"signedPreKey\":{\"keyId\":", .field w.signed, .text ",\"publicKey\":\"", .field 44,
    .text "\",\"signature\":\"", .field 86, .text "\"},\"preKey\":"] ++
  (if w.oneTime = 0 then [.text "null"]
    else [.text "{\"keyId\":", .field w.oneTime, .text ",\"publicKey\":\"", .field 44, .text "\"}"]) ++
  [.text ",\"pqPreKey\":{\"keyId\":", .field w.kyber, .text ",\"publicKey\":\"", .field 2092,
    .text "\",\"signature\":\"", .field 86, .text "\"}}"]

/-- One device of the response. The first result is the validity (255 or 0);
the others are zero unless it is 255:

identity key (32), device id (1), registration id (4), signed prekey id (4),
signed prekey (32), its signature (64), Kyber prekey id (4), Kyber prekey
(1568), its signature (64), and, when the item has a one-time prekey, its id
(4) and the key (32). Ids are big endian.

Valid means: the header, this item (starting at `start`), the separator before
it, what follows it (`,`, or `]}` at the end of the body) and the body's last
two bytes are the template's text for `w`; every number is a canonical decimal
in range (device id below 128, the others below `2^32`); every base64 value is
canonical; and the key type bytes are 5, 5, (5,) 8. -/
def device (a : ByteAuth.Ops B) (total start : Nat) (w : Widths) (body : List B) : List (List B) :=
  let pieces := item w
  let field := fieldOf body start pieces
  let shift := if w.oneTime = 0 then 0 else 2
  let stop := start + size pieces
  let identity := decode a (fieldOf body 0 header 0)
  let signedKey := decode a (field 3)
  let oneTimeKey := decode a (field 6)
  let kyberKey := decode a (field (6 + shift))
  let ok := all a ([literals a body 0 header, literals a body start pieces,
      expect a body (start - 1) (literal a (if start = firstItem then "[" else ",")),
      expect a body stop (literal a (if stop + 2 = total then "]}" else ",")),
      expect a body (total - 2) (literal a "]}"),
      decodeValid a (fieldOf body 0 header 0), ByteAuth.eqMask a (OpenResult.get a identity 0) (a.const 5),
      numberValid a 7 (field 0), numberValid a 32 (field 1), numberValid a 32 (field 2),
      decodeValid a (field 3), ByteAuth.eqMask a (OpenResult.get a signedKey 0) (a.const 5), decodeValid a (field 4),
      numberValid a 32 (field (5 + shift)), decodeValid a (field (6 + shift)),
      ByteAuth.eqMask a (OpenResult.get a kyberKey 0) (a.const 8), decodeValid a (field (7 + shift))] ++
    optional (w.oneTime != 0) [numberValid a 32 (field 5), decodeValid a (field 6),
      ByteAuth.eqMask a (OpenResult.get a oneTimeKey 0) (a.const 5)])
  [ok] :: ([identity.drop 1, numberBytes a 1 (field 0), numberBytes a 4 (field 1), numberBytes a 4 (field 2),
      signedKey.drop 1, decode a (field 4), numberBytes a 4 (field (5 + shift)), kyberKey.drop 1,
      decode a (field (7 + shift))] ++
    optional (w.oneTime != 0) [numberBytes a 4 (field 5), oneTimeKey.drop 1]).map (ByteAuth.release a ok)

/-! ### Binding a bundle to the contact

A contact record (319 bytes, `Establish.session` followed by
`Establish.metadata`) holds the contact's identity key at 150, UUID at 262 and
access key at 278. -/

/-- The check byte for `Establish.establish`, then the contact's UUID (16) and
access key (16) for its `uuid` and `accessKey` inputs (zero unless the check is
255). The check is 255 exactly when the bundle parsed (`valid`), its two
signatures verified (`verified`), `record` is a live record (version 4), and
the bundle's identity key is the one the contact is known by. -/
def bind (a : ByteAuth.Ops B) (record valid verified identityKey : List B) : List (List B) :=
  let ok := all a [isSet a valid, isSet a verified, ByteAuth.eqMask a (OpenResult.get a record 0) (a.const 4),
    ByteAuth.equalMask a identityKey (part record 150 32)]
  [ok] :: [part record 262 16, part record 278 16].map (ByteAuth.release a ok)

/-- `bind` for a contact whose identity key may have changed (the contact registered again; such
a change is accepted by the owner's decision, PRODUCT_TODO.md section 1). The check does not
compare the bundle's identity key with the record's: it is 255 exactly when the bundle parsed
(`valid`), its two signatures verified under the identity key the bundle itself carries
(`verified`), and `record` is a live record (version 4). Then the UUID and access key as in
`bind`, and one more byte, `changed`: 255 when the check holds and the bundle's identity key is
not the one in `record`, otherwise 0. Like the others it is released by the check, so it is 0
for a bundle that did not parse or did not verify. -/
def rebind (a : ByteAuth.Ops B) (record valid verified identityKey : List B) : List (List B) :=
  let ok := all a [isSet a valid, isSet a verified, ByteAuth.eqMask a (OpenResult.get a record 0) (a.const 4)]
  [ok] :: [part record 262 16, part record 278 16,
    [a.not (ByteAuth.equalMask a identityKey (part record 150 32))]].map (ByteAuth.release a ok)

/-! ### Layout from the opened shape (public arithmetic) -/

def Piece.mask : Piece → List Bool
  | .text s => s.toUTF8.data.toList.map (fun c => punctuation.contains c.toNat)
  | .field n => List.replicate n false

/-- The punctuation flags of a body made of these pieces. -/
def maskOf (pieces : List Piece) : List Bool := pieces.flatMap Piece.mask

def items : List Widths → List Piece
  | [] => []
  | [w] => item w
  | w :: rest => item w ++ [.text ","] ++ items rest

/-- The whole body for the given devices. -/
def response (ws : List Widths) : List Piece := header ++ items ws ++ [.text "]}"]

/-- Where each device's item starts. -/
def starts : Nat → List Widths → List Nat
  | _, [] => []
  | start, w :: rest => start :: starts (start + size (item w) + 1) rest

/-- Number of consecutive bytes from `start` that are not punctuation. -/
def run (mask : List Bool) (start : Nat) : Nat := ((mask.drop start).takeWhile (!·)).length

/-- A guess at the widths of the item starting at `start`, read off the flags
(checked afterwards by `layout?`). -/
def widthsAt (mask : List Bool) (start : Nat) : Widths :=
  let d := run mask (start + 12)
  let registrationAt := start + 12 + d + 18
  let r := run mask registrationAt
  let signedAt := registrationAt + r + 25
  let s := run mask signedAt
  let preKeyAt := signedAt + s + 14 + 44 + 15 + 86 + 12
  let present := mask.getD preKeyAt false
  let p := if present then run mask (preKeyAt + 9) else 0
  let kyberAt := if present then preKeyAt + 9 + p + 14 + 44 + 2 + 21 else preKeyAt + 4 + 21
  ⟨d, r, s, p, run mask kyberAt⟩

def layoutFrom (mask : List Bool) : Nat → Nat → List Widths
  | 0, _ => []
  | fuel + 1, start =>
      let w := widthsAt mask start
      let next := start + size (item w)
      w :: (if mask.length ≤ next + 2 then [] else layoutFrom mask fuel (next + 1))

/-- The devices' widths, if the flags are exactly those of a response with
such devices (`layout?_sound` in `TlsMpc/BundleProofs.lean`). -/
def layout? (mask : List Bool) : Option (List Widths) :=
  let ws := layoutFrom mask (mask.length / 2465 + 1) firstItem
  if ws.all Widths.ok && maskOf (response ws) == mask then some ws else none

/-! ### From circuit to values -/

section Refinement
variable {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'}

theorem optional_map (g : α → β) (present : Bool) (xs : List α) :
    (optional present xs).map g = optional present (xs.map g) := by
  cases present <;> rfl

theorem fromBits_map (ha : ByteAuth.Hom a a' f) (bits : List B) (first : Nat) :
    f (fromBits a bits first) = fromBits a' (bits.map f) first := by
  rw [fromBits, ReceiveFirst.foldl_hom (f := f) _
    (fun acc k => a'.xor acc (a'.and (OpenResult.get a' (bits.map f) (first + k)) (a'.const (2 ^ k))))
    (fun acc x => by simp only [ha.xor, ha.and, ha.const, OpenResult.get_map ha]), ha.const]
  rfl

theorem add_map (ha : ByteAuth.Hom a a' f) (width : Nat) (x y : List B) :
    (add a width x y).map f = add a' width (x.map f) (y.map f) := by
  have h := congrArg Prod.fst (PrivateBuffer.addLoop_map ha x y (List.range width) (a.const 0))
  simpa only [add, ha.const] using h

theorem structural_map (ha : ByteAuth.Hom a a' f) (c : B) : f (structural a c) = structural a' (f c) := by
  simp only [structural, ReceiveFirst.any_map ha, List.map_map, Function.comp_def, ByteAuth.eqMask_map ha, ha.const]

theorem shape_map (ha : ByteAuth.Hom a a' f) (body : List B) :
    (shape a body).map (List.map f) = shape a' (body.map f) := by
  simp only [shape, List.map_cons, List.map_nil, List.map_map, Function.comp_def, structural_map ha]

theorem sextetValid_map (ha : ByteAuth.Hom a a' f) (c : B) : f (sextetValid a c) = sextetValid a' (f c) := by
  simp only [sextetValid, ReceiveFirst.either_map ha, ha.and, ha.not, ha.maskBit]

theorem sextetValue_map (ha : ByteAuth.Hom a a' f) (c : B) : f (sextetValue a c) = sextetValue a' (f c) := by
  simp only [sextetValue, fromBits_map ha, add_map ha, List.map_cons, List.map_nil, List.map_map, Function.comp_def,
    ha.xor, ha.and, ha.not, ha.maskBit]

theorem byteAt_map (ha : ByteAuth.Hom a a' f) (values : List B) (j : Nat) :
    f (byteAt a values j) = byteAt a' (values.map f) j := by
  unfold byteAt
  split
  · simp only [ha.xor, RelayEncoding.slice_map ha, OpenResult.get_map ha]
  · split <;> simp only [ha.xor, RelayEncoding.slice_map ha, OpenResult.get_map ha]

theorem decode_map (ha : ByteAuth.Hom a a' f) (chars : List B) : (decode a chars).map f = decode a' (chars.map f) := by
  simp only [decode, List.map_map, Function.comp_def, byteAt_map ha, sextetValue_map ha, List.length_map]

theorem decodeValid_map (ha : ByteAuth.Hom a a' f) (chars : List B) :
    f (decodeValid a chars) = decodeValid a' (chars.map f) := by
  rw [decodeValid, ha.and, ReceiveFirst.all_map ha, ReceiveFirst.foldl_hom (f := f) _
    (fun mask i => a'.and mask (a'.not (a'.maskBit
      (sextetValue a' (OpenResult.get a' (chars.map f) ((chars.map f).length - 1))) i)))
    (fun acc x => by simp only [ha.and, ha.not, ha.maskBit, sextetValue_map ha, OpenResult.get_map ha,
      List.length_map]), ha.const]
  simp only [decodeValid, List.map_map, Function.comp_def, sextetValid_map ha, List.length_map]

theorem digitValid_map (ha : ByteAuth.Hom a a' f) (c : B) : f (digitValid a c) = digitValid a' (f c) := by
  simp only [digitValid, ReceiveFirst.either_map ha, ha.and, ha.not, ha.maskBit]

theorem pushDigit_map (ha : ByteAuth.Hom a a' f) (width : Nat) (acc : List B) (c : B) :
    (pushDigit a width acc c).map f = pushDigit a' width (acc.map f) (f c) := by
  simp only [pushDigit, add_map ha, List.map_cons, List.map_map, Function.comp_def, ha.const, ha.maskBit]

theorem numberBits_map (ha : ByteAuth.Hom a a' f) (chars : List B) :
    (numberBits a chars).map f = numberBits a' (chars.map f) := by
  have step (width : Nat) (xs : List B) (z : List B) :
      (xs.foldl (pushDigit a width) z).map f = (xs.map f).foldl (pushDigit a' width) (z.map f) := by
    induction xs generalizing z with
    | nil => rfl
    | cons x xs ih => simp only [List.foldl_cons, List.map_cons, ih, pushDigit_map ha]
  simp only [numberBits, step, List.map_replicate, ha.const, List.length_map]

theorem numberValid_map (ha : ByteAuth.Hom a a' f) (limit : Nat) (chars : List B) :
    f (numberValid a limit chars) = numberValid a' limit (chars.map f) := by
  have tail : (List.drop limit (numberBits a chars)).map (fun x => a'.not (f x)) =
      ((numberBits a' (chars.map f)).drop limit).map a'.not := by
    simp only [← numberBits_map ha, List.map_drop, List.map_map, Function.comp_def]
  simp only [numberValid, ReceiveFirst.all_map ha, List.map_append, List.map_map, Function.comp_def, digitValid_map ha,
    optional_map, List.map_cons, List.map_nil, ha.not, ByteAuth.eqMask_map ha, OpenResult.get_map ha, ha.const,
    tail, List.length_map]

theorem numberBytes_map (ha : ByteAuth.Hom a a' f) (count : Nat) (chars : List B) :
    (numberBytes a count chars).map f = numberBytes a' count (chars.map f) := by
  simp only [numberBytes, List.map_map, Function.comp_def, fromBits_map ha, numberBits_map ha]

theorem literals_map (ha : ByteAuth.Hom a a' f) (body : List B) (start : Nat) (pieces : List Piece) :
    f (literals a body start pieces) = literals a' (body.map f) start pieces := by
  induction pieces generalizing start with
  | nil => exact ha.const 255
  | cons piece rest ih =>
      cases piece with
      | text s => simp only [literals, ha.and, ReceiveFirst.expect_map ha, RelayEncoding.literal_map ha, ih]
      | field n => simp only [literals, ih]

theorem fieldOf_map (body : List B) (start : Nat) (pieces : List Piece) (index : Nat) :
    (fieldOf body start pieces index).map f = fieldOf (body.map f) start pieces index := by
  induction pieces generalizing start index with
  | nil => rfl
  | cons piece rest ih =>
      cases piece with
      | text s => simp only [fieldOf, ih]
      | field n =>
          cases index with
          | zero => simp only [fieldOf, Establish.part_map]
          | succ index => simp only [fieldOf, ih]

theorem device_map (ha : ByteAuth.Hom a a' f) (total start : Nat) (w : Widths) (body : List B) :
    (device a total start w body).map (List.map f) = device a' total start w (body.map f) := by
  simp only [device, List.map_cons, List.map_nil, List.map_append, List.map_map, Function.comp_def,
    ByteAuth.release_map ha, ReceiveFirst.all_map ha, optional_map, literals_map ha, ReceiveFirst.expect_map ha,
    RelayEncoding.literal_map ha, decodeValid_map ha, decode_map ha, numberValid_map ha, numberBytes_map ha,
    ByteAuth.eqMask_map ha, OpenResult.get_map ha, ha.const, fieldOf_map, List.map_drop]

theorem bind_map (ha : ByteAuth.Hom a a' f) (record valid verified identityKey : List B) :
    (bind a record valid verified identityKey).map (List.map f) =
      bind a' (record.map f) (valid.map f) (verified.map f) (identityKey.map f) := by
  simp only [bind, List.map_cons, List.map_nil, List.map_map, Function.comp_def, ByteAuth.release_map ha,
    ReceiveFirst.all_map ha, ReceiveFirst.isSet_map ha, ByteAuth.eqMask_map ha, ByteAuth.equalMask_map ha,
    OpenResult.get_map ha, ha.const, Establish.part_map]

theorem rebind_map (ha : ByteAuth.Hom a a' f) (record valid verified identityKey : List B) :
    (rebind a record valid verified identityKey).map (List.map f) =
      rebind a' (record.map f) (valid.map f) (verified.map f) (identityKey.map f) := by
  simp only [rebind, List.map_cons, List.map_nil, ByteAuth.release_map ha,
    ReceiveFirst.all_map ha, ReceiveFirst.isSet_map ha, ByteAuth.eqMask_map ha, ByteAuth.equalMask_map ha,
    OpenResult.get_map ha, ha.const, ha.not, Establish.part_map]

end Refinement

#print axioms device_map
#print axioms bind_map
#print axioms rebind_map
#print axioms shape_map

end TlsMpc.Signal.BundleResponse
