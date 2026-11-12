import TlsMpc.Signal.Establish
import TlsMpc.Signal.CbcOpen
import TlsMpc.Signal.MessageMac
import TlsMpc.Signal.SpqrChain

/-!
Receiving a new contact's FIRST message: a sealed-sender v1 envelope whose
content is a PreKeySignalMessage, processed as the PQXDH responder. Functions
on bytes, generic in the circuit operations. With the symbolic operations they
are the bodies of the kernels in `TlsMpc/ReceiveKernels.lean`; with the concrete
operations they are the specification those kernels are proved against
(`TlsMpc/ReceiveProofs.lean`).

Reference: libsignal v0.106.1 (`.deps/libsignal-v0.106.1/rust`).

* `protocol/src/sealed_sender.rs`, `sealed_sender_decrypt_to_usmc` (v1 arm):
  version byte `0x11`, then a protobuf with `ephemeralPublic` (1),
  `encryptedStatic` (2), `encryptedMessage` (3). `EphemeralKeys::calculate`
  with `Direction::Receiving`: HKDF-SHA256, salt
  `"UnidentifiedDelivery" ‖ ourIdentity(33) ‖ ephemeral(33)`, input the
  agreement (our identity private key · ephemeral), no info, 96 bytes: chain
  key, cipher key, MAC key. `crypto.rs`, `aes256_ctr_hmacsha256_decrypt`:
  the last 10 bytes are the first 10 of HMAC-SHA256(MAC key, ciphertext);
  AES-256-CTR with a zero counter block. The decrypted static key must be a
  serialized public key (`05 ‖ key`). `StaticKeys::calculate`: salt
  `chain ‖ encryptedStatic`, input the agreement (our identity private key ·
  sender identity key), 96 bytes of which the first 32 are discarded. Finally
  the certificate's identity key must equal the decrypted static key.
* `UnidentifiedSenderMessageContent::deserialize` and
  `proto/sealed_sender.proto`: `type` (1), `senderCertificate` (2),
  `content` (3), `contentHint` (4), `groupId` (5).
* `SenderCertificate::deserialize` / `validate_with_trust_roots`: the server
  certificate must be signed by the trust root, the sender certificate by the
  server key (XEdDSA), and `validation_time > expires` rejects.
* `pqxdh.rs`, `pqxdh_accept` (the RESPONDER's order, which differs from the
  initiator's in who holds which private key):
  `0xFF×32 ‖ DH(signed prekey, their identity) ‖ DH(our identity, their base)
  ‖ DH(signed prekey, their base) [‖ DH(one-time prekey, their base)] ‖
  kemSecret`, same label and split as the initiator. The base key must be
  canonical (`curve.rs`, `is_canonical`: torsion free and below `2^255 − 19`).
* `ratchet.rs`, `initialize_recipient_session`: root key and a SENDER chain on
  the signed prekey; no receiver chain. `double_ratchet.rs`,
  `dh_ratchet_step`, run by the first decryption because the message's ratchet
  key is new: `root.create_chain(theirRatchet, signedPrekeyPrivate)` gives the
  receiving chain; a fresh ratchet key pair and
  `root'.create_chain(theirRatchet, fresh)` give the session root and the
  sending chain; `previous_counter = 0`.
* SPQR (`.deps/SparsePostQuantumRatchet-…/src/lib.rs`, `recv`): the message key
  is `chain.recv_key(epoch − 1, index)` on the chain started from the PQXDH
  post-quantum key with direction B2A (`chain.rs`): our receiving chain is the
  A2B half. In epoch 1 no ML-KEM operation is involved. A header chunk in the
  payload only changes the receiver's stored chunk set
  (`v1/chunked/states.rs`, `NoHeaderReceived`); it does not enter the key.
* `triple_ratchet.rs`, `decrypt`; `ratchet/keys.rs`; `protocol.rs`,
  `SignalMessage::try_from`, `verify_mac_with_addresses`,
  `PreKeySignalMessage::try_from`; `proto/wire.proto`.

## Layouts are public, contents are private

Every field length and varint width inside the encrypted data is treated as
PUBLIC shape: a kernel is specialised to one layout and computes a private mask
saying that the private bytes have exactly that layout (every tag, every
length prefix, every continuation bit). To learn the layout, the small `shape`
functions open, and only when the enclosing authentication has passed, nothing
but lengths and widths. What this reveals beyond the envelope's length: the
sender certificate's length and whether it carries a phone number (and that
number's length); whether a content hint is present; the widths of the varints
in the two messages (prekey ids — ours, the sender's registration id, the two
message counters), the ciphertext length, and whether addresses are present.

Stricter than libsignal (all rejections, none an acceptance): fields must
appear in tag order with nothing unknown between them (what prost, protobuf-java
and the Signal clients emit); the envelope version byte must be `0x11`; the
device id must be below 128 (libsignal's own bound); the post-quantum message
must be version 1, epoch 1, with a one-byte index; the PreKeySignalMessage's
identity key must equal the certificate's.

Proved here: every definition commutes with a homomorphism of the operations.
Not proved: agreement with the Rust code (tested by
`handshake_backend/EmpHybridWork/check_receive_kernels.py` against a real
libsignal sender), and any cryptographic property.
-/
namespace TlsMpc.Signal.ReceiveFirst
open Std.Tactic.BVDecide
open Establish (part)

/-! ### Small pieces -/

def lit (a : ByteAuth.Ops B) (ns : List Nat) : List B := ns.map a.const

/-- 255 exactly when the bytes at `offset` are `expected`. -/
def expect (a : ByteAuth.Ops B) (bytes : List B) (offset : Nat) (expected : List B) : B :=
  ByteAuth.equalMask a (part bytes offset expected.length) expected

def all (a : ByteAuth.Ops B) (masks : List B) : B := masks.foldl a.and (a.const 255)

def either (a : ByteAuth.Ops B) (x y : B) : B := a.not (a.and (a.not x) (a.not y))

def any (a : ByteAuth.Ops B) (masks : List B) : B := masks.foldl (either a) (a.const 0)

/-- The continuation bit of a varint byte, as a mask. -/
def top (a : ByteAuth.Ops B) (x : B) : B := a.maskBit x 7

def isSet (a : ByteAuth.Ops B) (flag : List B) : B :=
  ByteAuth.eqMask a (OpenResult.get a flag 0) (a.const 255)

/-- Sum of the values whose mask is set (the masks are one-hot or all zero). -/
def pick (a : ByteAuth.Ops B) (choices : List (B × B)) : B :=
  choices.foldl (fun acc choice => a.xor acc (a.and choice.1 choice.2)) (a.const 0)

/-- 255 exactly when the varint at `offset` occupies `width` bytes. -/
def varintShape (a : ByteAuth.Ops B) (bytes : List B) (offset width : Nat) : B :=
  (List.range (width - 1)).foldl (fun mask j => a.and mask (top a (OpenResult.get a bytes (offset + j))))
    (a.not (top a (OpenResult.get a bytes (offset + width - 1))))

/-- The value of a varint (its bytes given) as four big-endian bytes; bits
beyond 32 are dropped. No gates. -/
def varintValue (a : ByteAuth.Ops B) (bytes : List B) : List B :=
  (List.range 4).map (fun j => (List.range 8).foldl (fun acc k =>
    a.xor acc (a.and (a.maskBit (OpenResult.get a bytes ((8 * (3 - j) + k) / 7)) ((8 * (3 - j) + k) % 7))
      (a.const (2 ^ k)))) (a.const 0))

/-! ### Public layout arithmetic -/

def varintWidth (n : Nat) : Nat := if n < 128 then 1 else if n < 16384 then 2 else if n < 2097152 then 3 else 4

/-- The body length of a length-delimited field that occupies `total` bytes
including its one-byte tag and its length prefix. -/
def bodyOf (total : Nat) : Nat :=
  if total - 2 < 128 then total - 2 else if total - 3 < 16384 then total - 3 else total - 4

/-- `total` is the size of some length-delimited field. -/
def framed (total : Nat) : Bool := 2 ≤ total && 1 + varintWidth (bodyOf total) + bodyOf total == total

def fieldHeader (a : ByteAuth.Ops B) (tag total : Nat) : List B :=
  a.const tag :: Varint.publicNat a (bodyOf total)

/-- The value of a two-byte varint from its two opened bytes. -/
def decode2 (low high : Nat) : Nat := low % 128 + 128 * high

/-! ### Sealed sender v1, receiving side

Envelope (public size): `11 ‖ 0A 21 05 ephemeral(32) ‖ 12 2B encryptedStatic(43)
‖ 1A len encryptedMessage`. -/

def label (s : Sha256.Ops B W) : List B := (TlsKdf.ascii "UnidentifiedDelivery").map s.byteConst

/-- Offset of the encrypted message in an envelope of `size` bytes. -/
def messageAt (size : Nat) : Nat := 82 + varintWidth (bodyOf (size - 81))

def envelopeMask (a : ByteAuth.Ops B) (size : Nat) (envelope : List B) : B :=
  all a [expect a envelope 0 (lit a [17, 10, 33, 5]), expect a envelope 36 (lit a [18, 43]),
    expect a envelope 81 (fieldHeader a 26 (size - 81))]

/-- The inverse of `SealedSenderV1.encrypt`: the mask saying the truncated
HMAC matches, followed by the plaintext. -/
def openPart (o : Aes.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (cipher mac sealed : List B) : List B :=
  ByteAuth.equalMask a ((Sha256.hmac s mac (sealed.take (sealed.length - 10))).take 10)
      (sealed.drop (sealed.length - 10)) ::
    SealedSenderV1.ctr o cipher (sealed.take (sealed.length - 10))

/-- First half: validity (1), the sender's identity key (32), the chain key
(32). `agreement` is our identity private key · the envelope's ephemeral key.
Everything is zero unless the validity is 255. -/
def unsealStatic (o : Aes.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (size : Nat)
    (ourIdentity envelope agreement : List B) : List (List B) :=
  let first := SealedSenderV1.material s (label s ++ (a.const 5 :: ourIdentity) ++ part envelope 3 33) agreement
  let opened := openPart o s a (part first 32 32) (part first 64 32) (part envelope 38 43)
  let valid := all a [envelopeMask a size envelope, OpenResult.get a opened 0,
    DhRatchet.agreementMask a agreement, ByteAuth.eqMask a (OpenResult.get a opened 1) (a.const 5)]
  [[valid], ByteAuth.release a valid (opened.drop 2), ByteAuth.release a valid (first.take 32)]

/-- Second half: validity (1), the UnidentifiedSenderMessageContent, and the
two bytes of the certificate's length prefix (the only part meant to be
opened). `agreement` is our identity private key · the sender's identity key.
Content: `08 type ‖ 12 len certificate ‖ 1A len message [‖ 20 hint]`. -/
def unsealMessage (o : Aes.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (size : Nat)
    (envelope staticValid chain agreement : List B) : List (List B) :=
  let second := SealedSenderV1.material s (chain ++ part envelope 38 43) agreement
  let opened := openPart o s a (part second 32 32) (part second 64 32) (envelope.drop (messageAt size))
  let content := opened.drop 1
  let valid := all a [isSet a staticValid, OpenResult.get a opened 0, DhRatchet.agreementMask a agreement,
    expect a content 0 (lit a [8]), expect a content 2 (lit a [18]), varintShape a content 3 2]
  [[valid], ByteAuth.release a valid content, ByteAuth.release a valid (part content 3 2)]

/-! ### The content's layout

`cert` is the certificate's length (from the opened prefix). -/

/-- Offset of the certificate's body (the signed bytes) inside the certificate
`0A len body ‖ 12 40 signature(64)`. -/
def bodyAt (cert : Nat) : Nat := 1 + varintWidth (bodyOf (cert - 66))

/-- Opened shape: whether the message field runs to the end; whether it is
followed by a two-byte content hint; whether the certificate's first field is a
phone number; and that field's length byte. Zero unless `valid` is 255. -/
def contentShape (a : ByteAuth.Ops B) (size cert : Nat) (content valid : List B) : List (List B) :=
  let rest := size - (5 + cert)
  let present := ByteAuth.eqMask a (OpenResult.get a content (5 + bodyAt cert)) (a.const 10)
  [ByteAuth.release a (isSet a valid) [
    expect a content (5 + cert) (fieldHeader a 26 rest),
    a.and (expect a content (5 + cert) (fieldHeader a 26 (rest - 2))) (expect a content (size - 2) (lit a [32])),
    present, a.and present (OpenResult.get a content (5 + bodyAt cert + 1))]]

/-- Validity (1), message type (1), certificate (`cert`), inner message. -/
def contentParts (a : ByteAuth.Ops B) (size cert : Nat) (hint : Bool) (content valid : List B) : List (List B) :=
  let rest := size - (5 + cert) - (if hint then 2 else 0)
  let ok := all a [isSet a valid, expect a content 0 (lit a [8]),
    expect a content 2 (a.const 18 :: Varint.publicNat a cert),
    expect a content (5 + cert) (fieldHeader a 26 rest),
    if hint then expect a content (size - 2) (lit a [32]) else a.const 255]
  [[ok], ByteAuth.release a ok [OpenResult.get a content 1], ByteAuth.release a ok (part content 5 cert),
    ByteAuth.release a ok (part content (5 + cert + 1 + varintWidth (bodyOf rest)) (bodyOf rest))]

/-! ### From circuit to values -/

section Refinement
variable {o : Aes.Ops B} {o' : Aes.Ops B'} {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'}
  {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}

theorem foldl_map (g : B → B → B) (g' : B' → B' → B') (h : ∀ x y, f (g x y) = g' (f x) (f y)) (xs : List B) (z : B) :
    f (xs.foldl g z) = (xs.map f).foldl g' (f z) := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, List.map_cons, ih, h]

theorem foldl_hom {α : Type} (g : B → α → B) (g' : B' → α → B') (h : ∀ acc x, f (g acc x) = g' (f acc) x)
    (xs : List α) (z : B) : f (xs.foldl g z) = xs.foldl g' (f z) := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons, ih, h]

theorem lit_map (ha : ByteAuth.Hom a a' f) (ns : List Nat) : (lit a ns).map f = lit a' ns := by
  simp only [lit, List.map_map, Function.comp_def, ha.const]

theorem expect_map (ha : ByteAuth.Hom a a' f) (bytes : List B) (offset : Nat) (expected : List B) :
    f (expect a bytes offset expected) = expect a' (bytes.map f) offset (expected.map f) := by
  simp only [expect, ByteAuth.equalMask_map ha, Establish.part_map, List.length_map]

theorem all_map (ha : ByteAuth.Hom a a' f) (masks : List B) : f (all a masks) = all a' (masks.map f) := by
  rw [all, foldl_map a.and a'.and ha.and, ha.const]
  rfl

theorem either_map (ha : ByteAuth.Hom a a' f) (x y : B) : f (either a x y) = either a' (f x) (f y) := by
  simp only [either, ha.not, ha.and]

theorem any_map (ha : ByteAuth.Hom a a' f) (masks : List B) : f (any a masks) = any a' (masks.map f) := by
  rw [any, foldl_map (either a) (either a') (either_map ha), ha.const]
  rfl

theorem top_map (ha : ByteAuth.Hom a a' f) (x : B) : f (top a x) = top a' (f x) := ha.maskBit x 7

theorem isSet_map (ha : ByteAuth.Hom a a' f) (flag : List B) : f (isSet a flag) = isSet a' (flag.map f) := by
  simp only [isSet, ByteAuth.eqMask_map ha, OpenResult.get_map ha, ha.const]

theorem pick_map (ha : ByteAuth.Hom a a' f) (choices : List (B × B)) :
    f (pick a choices) = pick a' (choices.map (fun choice => (f choice.1, f choice.2))) := by
  have step (xs : List (B × B)) (z : B) :
      f (xs.foldl (fun acc choice => a.xor acc (a.and choice.1 choice.2)) z) =
        (xs.map (fun choice => (f choice.1, f choice.2))).foldl
          (fun acc choice => a'.xor acc (a'.and choice.1 choice.2)) (f z) := by
    induction xs generalizing z with
    | nil => rfl
    | cons x xs ih => simp only [List.foldl_cons, List.map_cons, ih, ha.xor, ha.and]
  rw [pick, step, ha.const]
  rfl

theorem varintShape_map (ha : ByteAuth.Hom a a' f) (bytes : List B) (offset width : Nat) :
    f (varintShape a bytes offset width) = varintShape a' (bytes.map f) offset width := by
  rw [varintShape, foldl_hom (f := f) _ (fun mask j => a'.and mask (top a' (OpenResult.get a' (bytes.map f) (offset + j))))
    (fun acc x => by simp only [ha.and, top_map ha, OpenResult.get_map ha])]
  simp only [ha.not, top_map ha, OpenResult.get_map ha]
  rfl

theorem varintValue_map (ha : ByteAuth.Hom a a' f) (bytes : List B) :
    (varintValue a bytes).map f = varintValue a' (bytes.map f) := by
  simp only [varintValue, List.map_map]
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_def]
  rw [foldl_hom (f := f) _ (fun acc k => a'.xor acc (a'.and (a'.maskBit (OpenResult.get a' (bytes.map f)
    ((8 * (3 - j) + k) / 7)) ((8 * (3 - j) + k) % 7)) (a'.const (2 ^ k))))
    (fun acc x => by simp only [ha.xor, ha.and, ha.maskBit, ha.const, OpenResult.get_map ha]), ha.const]

theorem fieldHeader_map (ha : ByteAuth.Hom a a' f) (tag total : Nat) :
    (fieldHeader a tag total).map f = fieldHeader a' tag total := by
  simp only [fieldHeader, List.map_cons, ha.const, Varint.publicNat_map ha]

theorem label_map (hs : Sha256.Hom s s' f fw) : (label s).map f = label s' := by
  simp only [label, List.map_map, Function.comp_def, hs.byteConst]

theorem envelopeMask_map (ha : ByteAuth.Hom a a' f) (size : Nat) (envelope : List B) :
    f (envelopeMask a size envelope) = envelopeMask a' size (envelope.map f) := by
  simp only [envelopeMask, all_map ha, List.map_cons, List.map_nil, expect_map ha, lit_map ha, fieldHeader_map ha]

theorem openPart_map (ho : Aes.Hom o o' f) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
    (cipher mac sealed : List B) :
    (openPart o s a cipher mac sealed).map f = openPart o' s' a' (cipher.map f) (mac.map f) (sealed.map f) := by
  simp only [openPart, List.map_cons, ByteAuth.equalMask_map ha, List.map_take, List.map_drop, Sha256.hmac_map hs,
    SealedSenderV1.ctr_map ho, List.length_map]

theorem unsealStatic_map (ho : Aes.Hom o o' f) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f) (size : Nat)
    (ourIdentity envelope agreement : List B) :
    (unsealStatic o s a size ourIdentity envelope agreement).map (List.map f) =
      unsealStatic o' s' a' size (ourIdentity.map f) (envelope.map f) (agreement.map f) := by
  simp only [unsealStatic, List.map_cons, List.map_nil, List.map_append, ByteAuth.release_map ha, all_map ha,
    envelopeMask_map ha, OpenResult.get_map ha, DhRatchet.agreementMask_map ha, ByteAuth.eqMask_map ha, ha.const,
    List.map_drop, List.map_take, openPart_map ho hs ha, Establish.part_map, SealedSenderV1.material_map hs,
    label_map hs]

theorem unsealMessage_map (ho : Aes.Hom o o' f) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f) (size : Nat)
    (envelope staticValid chain agreement : List B) :
    (unsealMessage o s a size envelope staticValid chain agreement).map (List.map f) =
      unsealMessage o' s' a' size (envelope.map f) (staticValid.map f) (chain.map f) (agreement.map f) := by
  simp only [unsealMessage, List.map_cons, List.map_nil, List.map_append, ByteAuth.release_map ha, all_map ha,
    isSet_map ha, OpenResult.get_map ha, DhRatchet.agreementMask_map ha, expect_map ha, lit_map ha,
    varintShape_map ha, List.map_drop, openPart_map ho hs ha, Establish.part_map, SealedSenderV1.material_map hs]

theorem contentShape_map (ha : ByteAuth.Hom a a' f) (size cert : Nat) (content valid : List B) :
    (contentShape a size cert content valid).map (List.map f) =
      contentShape a' size cert (content.map f) (valid.map f) := by
  simp only [contentShape, List.map_cons, List.map_nil, ByteAuth.release_map ha, isSet_map ha, expect_map ha,
    fieldHeader_map ha, lit_map ha, ha.and, ByteAuth.eqMask_map ha, OpenResult.get_map ha, ha.const]

theorem contentParts_map (ha : ByteAuth.Hom a a' f) (size cert : Nat) (hint : Bool) (content valid : List B) :
    (contentParts a size cert hint content valid).map (List.map f) =
      contentParts a' size cert hint (content.map f) (valid.map f) := by
  cases hint <;>
    simp only [contentParts, List.map_cons, List.map_nil, ByteAuth.release_map ha, all_map ha, isSet_map ha,
      expect_map ha, fieldHeader_map ha, lit_map ha, OpenResult.get_map ha, ha.const, Establish.part_map,
      Varint.publicNat_map ha, Bool.false_eq_true, if_false, if_true]

end Refinement

#print axioms unsealStatic_map
#print axioms unsealMessage_map
#print axioms contentParts_map

/-! ### More small pieces -/

/-- A check that applies only to some public shapes. -/
def whenever (a : ByteAuth.Ops B) (condition : Bool) (mask : B) : B := if condition then mask else a.const 255

def numberBytes (a : ByteAuth.Ops B) (n : Nat) : List B := (List.range 4).map (fun i => a.const (n / 256 ^ (3 - i) % 256))

/-- The bits of a byte string, most significant first, each as a mask. -/
def maskBits (a : ByteAuth.Ops B) : List B → List B
  | [] => []
  | x :: xs => [7, 6, 5, 4, 3, 2, 1, 0].map (a.maskBit x) ++ maskBits a xs

/-- (less, equal) after comparing two bit strings, most significant first. -/
def compareBits (a : ByteAuth.Ops B) : List B → List B → B → B → B × B
  | x :: xs, y :: ys, less, equal =>
      compareBits a xs ys (either a less (a.and equal (a.and (a.not x) y))) (a.and equal (a.not (a.xor x y)))
  | _, _, less, equal => (less, equal)

/-- 255 exactly when the big-endian number `x` is at most `y` (equal lengths). -/
def atMost (a : ByteAuth.Ops B) (x y : List B) : B :=
  either a (compareBits a (maskBits a x) (maskBits a y) (a.const 0) (a.const 255)).1
    (compareBits a (maskBits a x) (maskBits a y) (a.const 0) (a.const 255)).2

/-! ### Sender certificate

`0A len body ‖ 12 40 signature(64)`, where the body is, in tag order:
`[0A len e164] ‖ 10 device ‖ 19 expires(8, little endian) ‖ 22 21 05 identity(32)`
then either `2A len serverCertificate ‖ uuid` (embedded signer) or
`uuid ‖ 40 serverId` (signer by reference), with the uuid either
`32 24 text(36)` or `3A 10 bytes(16)`.

The signer is compared with a PUBLIC expected value instead of being verified
against the trust root inside the engines: the embedded server certificate
must equal `signer` (a certificate the runtime has validated in the clear
against the trust root, as libsignal's `ServerCertificate::validate` does), or
the referenced id must equal `signer` (the id's varint bytes), the runtime
holding that id's certificate as libsignal's `KNOWN_SERVER_CERTIFICATES` does.
The sender certificate's own signature is verified under that server key. -/

def hexDigits : List (Nat × Nat) :=
  (List.range 10).map (fun i => (48 + i, i)) ++ (List.range 6).map (fun i => (97 + i, 10 + i)) ++
    (List.range 6).map (fun i => (65 + i, 10 + i))

def hexValid (a : ByteAuth.Ops B) (c : B) : B :=
  any a (hexDigits.map (fun digit => ByteAuth.eqMask a c (a.const digit.1)))

def hexValue (a : ByteAuth.Ops B) (scale : Nat) (c : B) : B :=
  pick a (hexDigits.map (fun digit => (ByteAuth.eqMask a c (a.const digit.1), a.const (digit.2 * scale))))

def uuidDigits : List Nat := (List.range 36).filter (fun i => i != 8 && i != 13 && i != 18 && i != 23)

/-- Validity, then the 16 bytes of a UUID written as 36 characters. -/
def uuidFromText (a : ByteAuth.Ops B) (text : List B) : List B :=
  all a (uuidDigits.map (fun i => hexValid a (OpenResult.get a text i)) ++
      [8, 13, 18, 23].map (fun i => ByteAuth.eqMask a (OpenResult.get a text i) (a.const 45))) ::
    (List.range 16).map (fun j => a.xor (hexValue a 16 (OpenResult.get a text (uuidDigits.getD (2 * j) 0)))
      (hexValue a 1 (OpenResult.get a text (uuidDigits.getD (2 * j + 1) 0))))

structure CertShape where
  /-- Length of the phone-number field including its two header bytes; 0 if absent. -/
  e164 : Nat
  embedded : Bool
  idWidth : Nat
  text : Bool
  deriving DecidableEq

def CertShape.signerSize (c : CertShape) : Nat := if c.embedded then 104 + c.idWidth else c.idWidth
def CertShape.uuidSize (c : CertShape) : Nat := if c.text then 36 else 16
/-- Length of the signed body. -/
def CertShape.body (c : CertShape) : Nat :=
  c.e164 + 46 + (if c.embedded then 2 + c.signerSize else 1 + c.signerSize) + 2 + c.uuidSize

/-- The shape of a certificate of `cert` bytes whose phone-number field has `e164` bytes. -/
def certShape (cert e164 : Nat) : Option CertShape :=
  let rest := bodyOf (cert - 66) - e164 - 46
  let shape : Option CertShape :=
    if 145 ≤ rest ∧ rest ≤ 149 then some ⟨e164, true, rest - 144, true⟩
    else if 125 ≤ rest ∧ rest ≤ 129 then some ⟨e164, true, rest - 124, false⟩
    else if 40 ≤ rest ∧ rest ≤ 44 then some ⟨e164, false, rest - 39, true⟩
    else if 20 ≤ rest ∧ rest ≤ 24 then some ⟨e164, false, rest - 19, false⟩
    else none
  shape.filter (fun c => framed (cert - 66) && c.body == bodyOf (cert - 66) && (e164 == 0 || (3 ≤ e164 && e164 < 130)))

/-- Validity (1), sender UUID (16), device id (1), signature (64), then the
XEdDSA challenge of the signature over the body under the server key whose
Edwards coordinates are `serverX`, `serverY`: `flip` (1) and `h` (32).
`now` is the current time in milliseconds, 8 bytes big endian. The validity
covers the layout, the device id (1..127), `now ≤ expires`, the identity key
being `senderIdentity`, and the signer being `signer`; NOT the signature. -/
def certificate (a : ByteAuth.Ops B) (h : XEdDsaSha512.Ops B H) (r : XEdDsaScalar.Ops B R) (cert : Nat) (c : CertShape)
    (bytes valid senderIdentity signer now serverX serverY : List B) : List (List B) :=
  let start := bodyAt cert
  let k := start + c.e164
  let signerAt := if c.embedded then k + 48 else k + 46 + 2 + c.uuidSize + 1
  let uuidAt := if c.embedded then k + 48 + c.signerSize + 2 else k + 48
  let parsed := if c.text then uuidFromText a (part bytes uuidAt 36) else a.const 255 :: part bytes uuidAt 16
  let signature := part bytes (start + c.body + 2) 64
  let ok := all a [isSet a valid,
    expect a bytes 0 (fieldHeader a 10 (cert - 66)),
    whenever a (c.e164 != 0) (expect a bytes start (lit a [10, c.e164 - 2])),
    expect a bytes k (lit a [16]),
    a.not (top a (OpenResult.get a bytes (k + 1))),
    a.not (ByteAuth.zeroMask a (OpenResult.get a bytes (k + 1))),
    expect a bytes (k + 2) (lit a [25]),
    atMost a now (part bytes (k + 3) 8).reverse,
    expect a bytes (k + 11) (lit a [34, 33, 5]),
    ByteAuth.equalMask a (part bytes (k + 14) 32) senderIdentity,
    expect a bytes (if c.embedded then k + 46 else k + 48 + c.uuidSize)
      (lit a (if c.embedded then [42, c.signerSize] else [64])),
    ByteAuth.equalMask a (part bytes signerAt c.signerSize) signer,
    expect a bytes (uuidAt - 2) (lit a (if c.text then [50, 36] else [58, 16])),
    OpenResult.get a parsed 0,
    expect a bytes (start + c.body) (lit a [18, 64])]
  let challenge := XEdDsaBinding.prepare a h r signature serverX serverY (part bytes start c.body)
  [[ok], ByteAuth.release a ok (parsed.drop 1), ByteAuth.release a ok [OpenResult.get a bytes (k + 1)], signature,
    challenge.take 1, challenge.drop 1]

/-- The certificate is valid and its signature verifies: `serverValid`, `rx`,
`ry` are the field engine's results (`xeddsa-recover` on the server key and
`xeddsa-check` on the challenge). -/
def certificateVerified (a : ByteAuth.Ops B) (certificateValid signature serverValid rx ry : List B) : List (List B) :=
  [[a.and (isSet a certificateValid) (Establish.signatureMask a signature serverValid rx ry)]]

/-! ### PreKeySignalMessage

`version ‖ [08 oneTimeId] ‖ 12 21 05 base(32) ‖ 1A 21 05 identity(32) ‖
22 len SignalMessage ‖ 28 registrationId ‖ 30 signedId ‖ 38 kyberId ‖
42 A1 0C 08 ciphertext(1568)`. -/

structure PreKeyShape where
  /-- Varint widths; `oneTime = 0` when the message names no one-time prekey. -/
  oneTime : Nat
  registration : Nat
  signed : Nat
  kyber : Nat

def PreKeyShape.keysAt (p : PreKeyShape) : Nat := 1 + (if p.oneTime = 0 then 0 else 1 + p.oneTime)
def PreKeyShape.tail (p : PreKeyShape) : Nat := 3 + p.registration + p.signed + p.kyber + 1572
def PreKeyShape.signalSize (p : PreKeyShape) (size : Nat) : Nat := bodyOf (size - (p.keysAt + 70) - p.tail)
def PreKeyShape.signalAt (p : PreKeyShape) (size : Nat) : Nat := p.keysAt + 71 + varintWidth (p.signalSize size)
def PreKeyShape.idsAt (p : PreKeyShape) (size : Nat) : Nat := p.signalAt size + p.signalSize size

def prekeyMask (a : ByteAuth.Ops B) (p : PreKeyShape) (size : Nat) (m : List B) : B :=
  let k := p.keysAt
  let t := p.idsAt size
  all a [ByteAuth.eqMask a (a.and (OpenResult.get a m 0) (a.const 240)) (a.const 64),
    whenever a (p.oneTime != 0) (a.and (expect a m 1 (lit a [8])) (varintShape a m 2 p.oneTime)),
    expect a m k (lit a [18, 33, 5]), expect a m (k + 35) (lit a [26, 33, 5]),
    expect a m (k + 70) (fieldHeader a 34 (size - (k + 70) - p.tail)),
    expect a m t (lit a [40]), varintShape a m (t + 1) p.registration,
    expect a m (t + 1 + p.registration) (lit a [48]), varintShape a m (t + 2 + p.registration) p.signed,
    expect a m (t + 2 + p.registration + p.signed) (lit a [56]),
    varintShape a m (t + 3 + p.registration + p.signed) p.kyber,
    expect a m (t + 3 + p.registration + p.signed + p.kyber) (lit a [66, 161, 12, 8])]

/-- `scalar_is_in_range` of libsignal's `is_canonical`: the key, as a number,
is below `2^255 − 19`. -/
def canonicalRange (a : ByteAuth.Ops B) (key : List B) : B :=
  a.not (either a (top a (OpenResult.get a key 31))
    (all a [atMost a [a.const 237] [OpenResult.get a key 0],
      ByteAuth.equalMask a (part key 1 30) (List.replicate 30 (a.const 255)),
      ByteAuth.eqMask a (OpenResult.get a key 31) (a.const 127)]))

/-- Validity (1), base key (32), ratchet key (32), then what may be opened:
one-time prekey id (4, zero if none), signed prekey id (4), Kyber prekey id (4),
Kyber ciphertext (1568). Everything is zero unless the validity is 255, which
requires the content to be valid, of type PREKEY_MESSAGE, with this layout, an
identity key equal to `senderIdentity`, and a base key in range. -/
def prekeyOpen (a : ByteAuth.Ops B) (p : PreKeyShape) (size : Nat)
    (message valid messageType senderIdentity : List B) : List (List B) :=
  let k := p.keysAt
  let t := p.idsAt size
  let ok := all a [isSet a valid, ByteAuth.eqMask a (OpenResult.get a messageType 0) (a.const 1),
    prekeyMask a p size message, ByteAuth.equalMask a (part message (k + 38) 32) senderIdentity,
    canonicalRange a (part message (k + 3) 32), expect a message (p.signalAt size + 1) (lit a [10, 33, 5])]
  [[ok], ByteAuth.release a ok (part message (k + 3) 32), ByteAuth.release a ok (part message (p.signalAt size + 4) 32),
    ByteAuth.release a ok (varintValue a (part message 2 p.oneTime)),
    ByteAuth.release a ok (varintValue a (part message (t + 2 + p.registration) p.signed)),
    ByteAuth.release a ok (varintValue a (part message (t + 3 + p.registration + p.signed) p.kyber)),
    ByteAuth.release a ok (part message (t + 3 + p.registration + p.signed + p.kyber + 4) 1568)]

/-- A varint of `width` bytes ends just before `stop` and is preceded by a tag. -/
def backWidth (a : ByteAuth.Ops B) (m : List B) (stop width : Nat) : B :=
  a.and (varintShape a m (stop - width) width) (a.not (top a (OpenResult.get a m (stop - width - 1))))

/-- Opened widths (21 flags): whether a one-time prekey id is present and its
width (5 flags, width 1..5), then the widths of the registration id, the
signed prekey id and the Kyber prekey id (5 flags each). The last three are
found from the END of the message, where the Kyber ciphertext has a fixed
size. Zero unless `valid` is 255. -/
def prekeyShape (a : ByteAuth.Ops B) (size : Nat) (m valid : List B) : List (List B) :=
  let stop := size - 1572
  let joint := fun k s => a.and (backWidth a m stop (k + 1)) (backWidth a m (stop - k - 2) (s + 1))
  let present := expect a m 1 (lit a [8])
  [ByteAuth.release a (isSet a valid) (
    present :: (List.range 5).map (fun w => a.and present (varintShape a m 2 (w + 1))) ++
    (List.range 5).map (fun r => any a ((List.range 5).flatMap (fun k => (List.range 5).map (fun s =>
      a.and (joint k s) (backWidth a m (stop - k - s - 4) (r + 1)))))) ++
    (List.range 5).map (fun s => any a ((List.range 5).map (fun k => joint k s))) ++
    (List.range 5).map (fun k => backWidth a m stop (k + 1)))]

/-! ### SignalMessage

`version ‖ 0A 21 05 ratchet(32) ‖ 10 counter ‖ 18 previous ‖ 22 len ciphertext ‖
2A len pqRatchet ‖ [32 24 addresses(36)] ‖ mac(8)`; the post-quantum message
is `01 ‖ epoch ‖ index ‖ payload`. -/

structure SignalShape where
  counter : Nat
  previous : Nat
  ciphertext : Nat
  addresses : Bool

def SignalShape.cipherAt (q : SignalShape) : Nat := 39 + q.counter + q.previous + varintWidth q.ciphertext
def SignalShape.pqField (q : SignalShape) (size : Nat) : Nat :=
  size - (q.cipherAt + q.ciphertext) - 8 - (if q.addresses then 38 else 0)
def SignalShape.pqAt (q : SignalShape) (size : Nat) : Nat :=
  q.cipherAt + q.ciphertext + 1 + varintWidth (bodyOf (q.pqField size))

/-- Opened shape (13 bytes): the widths of the counter and of the previous
counter (5 flags each), the two bytes of the ciphertext's length prefix (the
second zero if the prefix has one byte), and whether the message ends with an
addresses field (judged by its two header bytes; the session function then
checks the whole layout). Zero unless `valid` is 255. -/
def signalShape (a : ByteAuth.Ops B) (p : PreKeyShape) (size : Nat) (m valid : List B) : List (List B) :=
  let start := p.signalAt size
  let joint := fun c q => a.and (varintShape a m (start + 37) (c + 1)) (varintShape a m (start + 39 + c) (q + 1))
  let low := pick a ((List.range 5).flatMap (fun c => (List.range 5).map (fun q =>
    (joint c q, OpenResult.get a m (start + 41 + c + q)))))
  let high := pick a ((List.range 5).flatMap (fun c => (List.range 5).map (fun q =>
    (joint c q, OpenResult.get a m (start + 42 + c + q)))))
  [ByteAuth.release a (isSet a valid) (
    (List.range 5).map (fun c => varintShape a m (start + 37) (c + 1)) ++
    (List.range 5).map (fun q => any a ((List.range 5).map (fun c => joint c q))) ++
    [low, a.and (top a low) high, expect a m (p.idsAt size - 46) (lit a [50, 36])])]

def signalMask (a : ByteAuth.Ops B) (q : SignalShape) (size : Nat) (w addresses : List B) : B :=
  all a [ByteAuth.eqMask a (a.and (OpenResult.get a w 0) (a.const 240)) (a.const 64),
    expect a w 1 (lit a [10, 33, 5]), expect a w 36 (lit a [16]), varintShape a w 37 q.counter,
    expect a w (37 + q.counter) (lit a [24]), varintShape a w (38 + q.counter) q.previous,
    expect a w (38 + q.counter + q.previous) (a.const 34 :: Varint.publicNat a q.ciphertext),
    expect a w (q.cipherAt + q.ciphertext) (fieldHeader a 42 (q.pqField size)),
    expect a w (q.pqAt size) (lit a [1, 1]),
    a.not (top a (OpenResult.get a w (q.pqAt size + 2))),
    whenever a q.addresses (a.and (expect a w (size - 46) (lit a [50, 36]))
      (ByteAuth.equalMask a (part w (size - 44) 36) addresses))]

/-! ### Keys -/

/-- Receiving step: root (32) ‖ receiving chain (32); sending step: session
root (32) ‖ sending chain (32); post-quantum: next root (32) ‖ A2B chain (32,
our receiving chain) ‖ B2A chain (32, our sending chain).

* `dh1` = our signed prekey · their identity key
* `dh2` = our identity key · their base key
* `dh3` = our signed prekey · their base key
* `oneTime` = our one-time prekey · their base key (empty if none)
* `receiveAgreement` = our signed prekey · their ratchet key
* `sendAgreement` = our new ratchet key · their ratchet key -/
def keys (s : Sha256.Ops B W) (dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement : List B) : List B :=
  let handshake := Pqxdh.deriveCore s dh1 dh2 dh3 oneTime kem
  let receive := DhRatchet.materialFast s (handshake.take 32) receiveAgreement
  receive ++ DhRatchet.materialFast s (receive.take 32) sendAgreement ++
    PrivateInitialSpqrV1.chainStart s (handshake.drop 64)

/-- The chain keys of message counters `0 .. count`. -/
def chainKeys (s : Sha256.Ops B W) : Nat → List B → List (List B)
  | 0, key => [key]
  | count + 1, key => key :: chainKeys s count (Symmetric.nextChainKey s key)

/-- The post-quantum chain outputs (next key 32 ‖ message key 32) of indices
`counter + 1 .. counter + count`. -/
def pqKeys (s : Sha256.Ops B W) (a : ByteAuth.Ops B) : Nat → Nat → List B → List (List B)
  | 0, _, _ => []
  | count + 1, counter, key =>
      SpqrChain.materialFast s a key (numberBytes a counter) ::
        pqKeys s a count (counter + 1) ((SpqrChain.materialFast s a key (numberBytes a counter)).take 32)

def candidates (a : ByteAuth.Ops B) (index : List B) : Nat → List (List B) → List (B × List B)
  | _, [] => []
  | n, value :: values => (ByteAuth.equalMask a index (numberBytes a n), value) :: candidates a index (n + 1) values

/-- Whether `index` (4 bytes) is one of `first, first + 1, …`, then the value
at that position (`width` bytes; zero if none). -/
def selectAt (a : ByteAuth.Ops B) (index : List B) (first : Nat) (values : List (List B)) (width : Nat) : List B :=
  any a ((candidates a index first values).map (fun c => c.1)) ::
    (List.range width).map (fun j => pick a ((candidates a index first values).map (fun c =>
      (c.1, OpenResult.get a c.2 j))))

/-- Next chain key (32) ‖ cipher key (32) ‖ MAC key (32) ‖ IV (16). -/
def messageKeys (s : Sha256.Ops B W) (chainKey salt : List B) : List B :=
  (Symmetric.deriveFast s chainKey salt).bytes

/-! ### The session

Results: status (1); the conversation record the send kernels consume; the
receiver record; the decrypted content as length (8, big endian) followed by
the padded plaintext. Everything is zero unless the status is 255.

Receiver record (236): session root 32, next receiving chain key 32, their
ratchet key 32, next receiving counter 4, post-quantum next root 32, next
post-quantum receiving chain key 32, post-quantum receiving index 4, their
base key 32.

`checks` are the validity bytes of the earlier stages (each must be 255);
`jump` bounds how many earlier messages of the same chain may have been lost
(their keys are not kept). `baseValid`, `torsionX`, `torsionY` are the field
engine's results for the base key (`xeddsa-recover` validity and the two
outputs of `receive-torsion`). -/
def session (o : AesInverse.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (p : PreKeyShape) (q : SignalShape)
    (size jump : Nat)
    (message checks senderIdentity ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement
      sendAgreement ratchetPublic baseValid torsionX torsionY certificate accessKey requestId : List B) :
    List (List B) :=
  let w := part message (p.signalAt size) (p.signalSize size)
  let k := keys s dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement
  let counter := varintValue a (part w 37 q.counter)
  let index := lit a [0, 0, 0] ++ [OpenResult.get a w (q.pqAt (p.signalSize size) + 2)]
  let chain := selectAt a counter 0 (chainKeys s jump (part k 32 32)) 32
  let pq := selectAt a index 1 (pqKeys s a (jump + 1) 0 (part k 160 32)) 64
  let mk := messageKeys s (chain.drop 1) (part pq 33 32)
  let checked := all a [
    Establish.accepted a checks [dh1, dh2, dh3, oneTime, receiveAgreement, sendAgreement],
    prekeyMask a p size message,
    ByteAuth.equalMask a (part message (p.keysAt + 38) 32) senderIdentity,
    ByteAuth.equalMask a baseValid (a.const 1 :: List.replicate 31 (a.const 0)),
    ByteAuth.equalMask a torsionX (List.replicate 32 (a.const 0)),
    ByteAuth.equalMask a torsionY (List.replicate 32 (a.const 0)),
    signalMask a q (p.signalSize size) w
      (Establish.addresses a (uuid ++ device) (localAddress.take 16) (OpenResult.get a localAddress 16)),
    OpenResult.get a chain 0, OpenResult.get a pq 0,
    MessageMac.verifyMask s a (part mk 64 32) senderIdentity ourIdentity w]
  let opened := OpenResult.finish a checked
    (CbcOpen.decryptCore o (part mk 32 32) (part mk 96 16) (part w q.cipherAt q.ciphertext))
  let status := OpenResult.get a opened 0
  [[status],
    ByteAuth.release a status (certificate ++
      Establish.session a 80 ratchetPublic (part k 96 32) (part k 192 32) ourIdentity senderIdentity ++
      Establish.metadata a uuid accessKey requestId device
        (varintValue a (part message (p.idsAt size + 1) p.registration))),
    ByteAuth.release a status (part k 64 32 ++ part mk 0 32 ++ part w 4 32 ++ ChainSend.nextCounter s a counter ++
      part k 128 32 ++ part pq 1 32 ++ index ++ part message (p.keysAt + 3) 32),
    opened.drop 1]

/-! ### The message text

The decrypted content is a Signal `Content` whose first field is a
`DataMessage` whose first field is the body: `0A len (0A len body …) …`. Only
the body is released (a data message also carries the sender's profile key). -/

/-- Status (1), body length (2, big endian), body (`capacity` bytes, zero
beyond the length), and three flags saying whether the body starts at offset
4, 5 or 6 of the content (the widths of the two length prefixes). `plain` is
the session's fourth result. Zero unless the content has that form and the
body fits. -/
def text (a : ByteAuth.Ops B) (capacity : Nat) (plain : List B) : List (List B) :=
  let c := plain.drop 8
  let wide := top a (OpenResult.get a c 1)
  let low := Unpad.chooseByte a wide (OpenResult.get a c 4) (OpenResult.get a c 3)
  let long := top a low
  let high := a.and long (Unpad.chooseByte a wide (OpenResult.get a c 5) (OpenResult.get a c 4))
  let length := [(List.range 7).foldl (fun acc k => a.xor acc (a.and (a.maskBit high (k + 1)) (a.const (2 ^ k)))) (a.const 0),
    a.xor (a.and low (a.const 127)) (a.and (a.maskBit high 0) (a.const 128))]
  let ok := all a [ByteAuth.eqMask a (OpenResult.get a c 0) (a.const 10),
    ByteAuth.eqMask a (Unpad.chooseByte a wide (OpenResult.get a c 3) (OpenResult.get a c 2)) (a.const 10),
    a.not (top a high), atMost a length (lit a [capacity / 256 % 256, capacity % 256])]
  [[ok], ByteAuth.release a ok length,
    (List.range capacity).map (fun i => all a [ok, a.not (atMost a length (lit a [i / 256 % 256, i % 256])),
      pick a [(a.and (a.not wide) (a.not long), OpenResult.get a c (4 + i)), (a.xor wide long, OpenResult.get a c (5 + i)),
        (a.and wide long, OpenResult.get a c (6 + i))]]),
    ByteAuth.release a ok [a.and (a.not wide) (a.not long), a.xor wide long, a.and wide long]]

/-! ### The contact's access key

A data message carries the sender's profile key (field 6: `32 20 key(32)`),
and the unidentified-access key that sealed-sender delivery to the contact
needs is derived from it (`rust/zkgroup/src/api/profiles/profile_key.rs`,
`derive_access_key`: AES-256 under the profile key of the block `0^15 ‖ 02`). -/

/-- The fields a Signal client may put between a data message's body (field 1)
and its profile key (field 6), each absent (0) or a varint of that many bytes:
`flags` (4, tag `20`), `expireTimer` (5, tag `28`) and `expireTimerVersion`
(23, tag `B8 01`). Signal-Android encodes with Wire, which writes fields in
DECLARATION order (`body, attachments, groupV2, flags, expireTimer,
expireTimerVersion, profileKey, timestamp, …`): a plain text is
`0A len body ‖ 28 timer ‖ B8 01 version ‖ 32 20 key ‖ 38 timestamp …`. A
tag-order encoder (protoc, prost) puts field 23 after the profile key, leaving
`28 timer` or nothing. -/
structure Gap where
  flags : Nat
  timer : Nat
  version : Nat

def Gap.size (g : Gap) : Nat :=
  (if g.flags = 0 then 0 else 1 + g.flags) + (if g.timer = 0 then 0 else 1 + g.timer) +
    (if g.version = 0 then 0 else 2 + g.version)

/-- Every accepted gap: flags absent or 1..2 bytes, timer absent or 1..5 bytes
(any `uint32`), version absent or 1..3 bytes. 72 layouts, at most 16 bytes.
Two of them never both match the same bytes (they first differ in a tag byte or
in a continuation bit), so at most one mask below is set. -/
def gaps : List Gap :=
  (List.range 3).flatMap (fun f => (List.range 6).flatMap (fun t => (List.range 4).map (fun v => ⟨f, t, v⟩)))

/-- 255 exactly when the content `c` has the fields of `g` at `offset`, then
the profile key's header `32 20`. -/
def gapMask (a : ByteAuth.Ops B) (c : List B) (offset : Nat) (g : Gap) : B :=
  let t := offset + (if g.flags = 0 then 0 else 1 + g.flags)
  let v := t + (if g.timer = 0 then 0 else 1 + g.timer)
  all a [whenever a (g.flags != 0) (a.and (ByteAuth.eqMask a (OpenResult.get a c offset) (a.const 32))
      (varintShape a c (offset + 1) g.flags)),
    whenever a (g.timer != 0) (a.and (ByteAuth.eqMask a (OpenResult.get a c t) (a.const 40))
      (varintShape a c (t + 1) g.timer)),
    whenever a (g.version != 0) (all a [ByteAuth.eqMask a (OpenResult.get a c v) (a.const 184),
      ByteAuth.eqMask a (OpenResult.get a c (v + 1)) (a.const 1), varintShape a c (v + 2) g.version]),
    ByteAuth.eqMask a (OpenResult.get a c (offset + g.size)) (a.const 50),
    ByteAuth.eqMask a (OpenResult.get a c (offset + g.size + 1)) (a.const 32)]

/-- For byte `j` of the profile key: each gap's mask with that byte under the gap. -/
def keyChoices (a : ByteAuth.Ops B) (c : List B) (offset j : Nat) : List Gap → List B → List (B × B)
  | g :: gs, m :: ms => (m, OpenResult.get a c (offset + g.size + 2 + j)) :: keyChoices a c offset j gs ms
  | _, _ => []

/-- Status (1) and the conversation record with the access key written into
its metadata; the record is unchanged unless the status is 255. `offset` is
the position in the content right after the body (public: the body's start
and length are opened by `text`); the profile-key field follows it after one
of the `gaps`, chosen inside the circuit, so the nodes learn nothing about
which (the status says only that one matched, as it did when only the empty
gap was accepted). `plain` is the session's fourth result. -/
def withAccessKey (o : Aes.Ops B) (a : ByteAuth.Ops B) (cert offset : Nat) (conversation plain : List B) :
    List (List B) :=
  let c := plain.drop 8
  let masks := gaps.map (gapMask a c offset)
  let found := any a masks
  let key := (List.range 32).map (fun j => pick a (keyChoices a c offset j gaps masks))
  [[found],
    conversation.take (cert + 278) ++
      ChainSend.selectState a found
        (Aes.encryptExpanded o 14 (Aes.expandKey o 8 14 key) (lit a (List.replicate 15 0 ++ [2])))
        (part conversation (cert + 278) 16) ++
      conversation.drop (cert + 294)]

section Refinement
variable {o : AesInverse.Ops B} {o' : AesInverse.Ops B'} {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'}
  {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}

theorem whenever_map (ha : ByteAuth.Hom a a' f) (condition : Bool) (mask : B) :
    f (whenever a condition mask) = whenever a' condition (f mask) := by
  cases condition <;> simp only [whenever, Bool.false_eq_true, if_false, if_true, ha.const]

theorem numberBytes_map (ha : ByteAuth.Hom a a' f) (n : Nat) : (numberBytes a n).map f = numberBytes a' n := by
  simp only [numberBytes, List.map_map, Function.comp_def, ha.const]

theorem maskBits_map (ha : ByteAuth.Hom a a' f) (bytes : List B) : (maskBits a bytes).map f = maskBits a' (bytes.map f) := by
  induction bytes with
  | nil => rfl
  | cons x xs ih => simp only [maskBits, List.map_append, List.map_cons, List.map_nil, ha.maskBit, ih]

theorem compareBits_map (ha : ByteAuth.Hom a a' f) (xs ys : List B) (less equal : B) :
    (f (compareBits a xs ys less equal).1, f (compareBits a xs ys less equal).2) =
      compareBits a' (xs.map f) (ys.map f) (f less) (f equal) := by
  induction xs generalizing ys less equal with
  | nil => rfl
  | cons x xs ih =>
      cases ys with
      | nil => rfl
      | cons y ys => simp only [compareBits, List.map_cons, ih, either_map ha, ha.and, ha.not, ha.xor]

theorem atMost_map (ha : ByteAuth.Hom a a' f) (x y : List B) : f (atMost a x y) = atMost a' (x.map f) (y.map f) := by
  have h := compareBits_map ha (maskBits a x) (maskBits a y) (a.const 0) (a.const 255)
  rw [maskBits_map ha, maskBits_map ha, ha.const, ha.const] at h
  simp only [atMost, either_map ha, ← h]

theorem hexValid_map (ha : ByteAuth.Hom a a' f) (c : B) : f (hexValid a c) = hexValid a' (f c) := by
  simp only [hexValid, any_map ha, List.map_map, Function.comp_def, ByteAuth.eqMask_map ha, ha.const]

theorem hexValue_map (ha : ByteAuth.Hom a a' f) (scale : Nat) (c : B) : f (hexValue a scale c) = hexValue a' scale (f c) := by
  simp only [hexValue, pick_map ha, List.map_map, Function.comp_def, ByteAuth.eqMask_map ha, ha.const]

theorem uuidFromText_map (ha : ByteAuth.Hom a a' f) (text : List B) :
    (uuidFromText a text).map f = uuidFromText a' (text.map f) := by
  simp only [uuidFromText, List.map_cons, all_map ha, List.map_append, List.map_map, Function.comp_def,
    hexValid_map ha, hexValue_map ha, OpenResult.get_map ha, ByteAuth.eqMask_map ha, ha.xor, ha.const, List.map_nil]

theorem certificate_map {h : XEdDsaSha512.Ops B H} {h' : XEdDsaSha512.Ops B' H'} {r : XEdDsaScalar.Ops B R}
    {r' : XEdDsaScalar.Ops B' R'} {fh : H → H'} {fr : R → R'} (ha : ByteAuth.Hom a a' f)
    (hh : XEdDsaSha512.Hom h h' f fh) (hr : XEdDsaScalar.Hom r r' f fr) (cert : Nat) (c : CertShape)
    (bytes valid senderIdentity signer now serverX serverY : List B) :
    (certificate a h r cert c bytes valid senderIdentity signer now serverX serverY).map (List.map f) =
      certificate a' h' r' cert c (bytes.map f) (valid.map f) (senderIdentity.map f) (signer.map f) (now.map f)
        (serverX.map f) (serverY.map f) := by
  cases htext : c.text <;>
    simp only [certificate, htext, List.map_cons, List.map_nil, ByteAuth.release_map ha, all_map ha, isSet_map ha,
      expect_map ha, fieldHeader_map ha, whenever_map ha, lit_map ha, ha.not, top_map ha, OpenResult.get_map ha,
      ByteAuth.zeroMask_map ha, atMost_map ha, List.map_reverse, Establish.part_map, ByteAuth.equalMask_map ha,
      uuidFromText_map ha, ha.const, List.map_drop, List.map_take, XEdDsaBinding.prepare_map ha hh hr,
      Bool.false_eq_true, if_false, if_true]

theorem certificateVerified_map (ha : ByteAuth.Hom a a' f) (certificateValid signature serverValid rx ry : List B) :
    (certificateVerified a certificateValid signature serverValid rx ry).map (List.map f) =
      certificateVerified a' (certificateValid.map f) (signature.map f) (serverValid.map f) (rx.map f) (ry.map f) := by
  simp only [certificateVerified, List.map_cons, List.map_nil, ha.and, isSet_map ha, Establish.signatureMask_map ha]

theorem prekeyMask_map (ha : ByteAuth.Hom a a' f) (p : PreKeyShape) (size : Nat) (m : List B) :
    f (prekeyMask a p size m) = prekeyMask a' p size (m.map f) := by
  simp only [prekeyMask, all_map ha, List.map_cons, List.map_nil, ByteAuth.eqMask_map ha, ha.and, OpenResult.get_map ha,
    ha.const, whenever_map ha, expect_map ha, lit_map ha, varintShape_map ha, fieldHeader_map ha]

theorem canonicalRange_map (ha : ByteAuth.Hom a a' f) (key : List B) :
    f (canonicalRange a key) = canonicalRange a' (key.map f) := by
  simp only [canonicalRange, ha.not, either_map ha, top_map ha, OpenResult.get_map ha, all_map ha, List.map_cons,
    List.map_nil, atMost_map ha, ha.const, ByteAuth.equalMask_map ha, Establish.part_map, List.map_replicate,
    ByteAuth.eqMask_map ha]

theorem prekeyOpen_map (ha : ByteAuth.Hom a a' f) (p : PreKeyShape) (size : Nat)
    (message valid messageType senderIdentity : List B) :
    (prekeyOpen a p size message valid messageType senderIdentity).map (List.map f) =
      prekeyOpen a' p size (message.map f) (valid.map f) (messageType.map f) (senderIdentity.map f) := by
  simp only [prekeyOpen, List.map_cons, List.map_nil, ByteAuth.release_map ha, all_map ha, isSet_map ha,
    ByteAuth.eqMask_map ha, OpenResult.get_map ha, ha.const, prekeyMask_map ha, ByteAuth.equalMask_map ha,
    Establish.part_map, canonicalRange_map ha, expect_map ha, lit_map ha, varintValue_map ha]

theorem backWidth_map (ha : ByteAuth.Hom a a' f) (m : List B) (stop width : Nat) :
    f (backWidth a m stop width) = backWidth a' (m.map f) stop width := by
  simp only [backWidth, ha.and, varintShape_map ha, ha.not, top_map ha, OpenResult.get_map ha]

theorem prekeyShape_map (ha : ByteAuth.Hom a a' f) (size : Nat) (m valid : List B) :
    (prekeyShape a size m valid).map (List.map f) = prekeyShape a' size (m.map f) (valid.map f) := by
  simp only [prekeyShape, List.map_cons, List.map_nil, ByteAuth.release_map ha, isSet_map ha, List.map_append,
    List.map_map, Function.comp_def, expect_map ha, lit_map ha, ha.and, varintShape_map ha, any_map ha,
    List.map_flatMap, backWidth_map ha]

theorem signalShape_map (ha : ByteAuth.Hom a a' f) (p : PreKeyShape) (size : Nat) (m valid : List B) :
    (signalShape a p size m valid).map (List.map f) = signalShape a' p size (m.map f) (valid.map f) := by
  simp only [signalShape, List.map_cons, List.map_nil, ByteAuth.release_map ha, isSet_map ha, List.map_append,
    List.map_map, Function.comp_def, expect_map ha, lit_map ha, ha.and, varintShape_map ha, any_map ha,
    List.map_flatMap, pick_map ha, top_map ha, OpenResult.get_map ha]

theorem signalMask_map (ha : ByteAuth.Hom a a' f) (q : SignalShape) (size : Nat) (w addresses : List B) :
    f (signalMask a q size w addresses) = signalMask a' q size (w.map f) (addresses.map f) := by
  simp only [signalMask, all_map ha, List.map_cons, List.map_nil, ByteAuth.eqMask_map ha, ha.and, OpenResult.get_map ha,
    ha.const, whenever_map ha, expect_map ha, lit_map ha, varintShape_map ha, fieldHeader_map ha,
    Varint.publicNat_map ha, ha.not, top_map ha, ByteAuth.equalMask_map ha, Establish.part_map]

theorem keys_map (hs : Sha256.Hom s s' f fw) (dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement : List B) :
    (keys s dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement).map f =
      keys s' (dh1.map f) (dh2.map f) (dh3.map f) (oneTime.map f) (kem.map f) (receiveAgreement.map f)
        (sendAgreement.map f) := by
  simp only [keys, List.map_append, DhRatchet.materialFast_map hs, List.map_take, List.map_drop,
    Pqxdh.deriveCore_map hs, Establish.chainStart_map hs]

theorem chainKeys_map (hs : Sha256.Hom s s' f fw) (count : Nat) (key : List B) :
    (chainKeys s count key).map (List.map f) = chainKeys s' count (key.map f) := by
  induction count generalizing key with
  | zero => rfl
  | succ count ih => simp only [chainKeys, List.map_cons, ih, Symmetric.nextChainKey_map hs]

theorem pqKeys_map (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f) (count counter : Nat) (key : List B) :
    (pqKeys s a count counter key).map (List.map f) = pqKeys s' a' count counter (key.map f) := by
  induction count generalizing counter key with
  | zero => rfl
  | succ count ih =>
      simp only [pqKeys, List.map_cons, ih, SpqrChain.materialFast_map hs ha, numberBytes_map ha, List.map_take]

theorem candidates_map (ha : ByteAuth.Hom a a' f) (index : List B) (n : Nat) (values : List (List B)) :
    (candidates a index n values).map (fun c => (f c.1, c.2.map f)) =
      candidates a' (index.map f) n (values.map (List.map f)) := by
  induction values generalizing n with
  | nil => rfl
  | cons value values ih =>
      simp only [candidates, List.map_cons, ih, ByteAuth.equalMask_map ha, numberBytes_map ha]

theorem selectAt_map (ha : ByteAuth.Hom a a' f) (index : List B) (first : Nat) (values : List (List B)) (width : Nat) :
    (selectAt a index first values width).map f =
      selectAt a' (index.map f) first (values.map (List.map f)) width := by
  rw [selectAt, selectAt, ← candidates_map ha]
  simp only [List.map_cons, any_map ha, List.map_map, Function.comp_def, pick_map ha, OpenResult.get_map ha]

theorem messageKeys_map (hs : Sha256.Hom s s' f fw) (chainKey salt : List B) :
    (messageKeys s chainKey salt).map f = messageKeys s' (chainKey.map f) (salt.map f) := by
  rw [messageKeys, messageKeys, Symmetric.deriveFast_correct, Symmetric.deriveFast_correct,
    Symmetric.derive_bytes_map hs]

theorem session_map (ho : AesInverse.Hom o o' f) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f)
    (p : PreKeyShape) (q : SignalShape) (size jump : Nat)
    (message checks senderIdentity ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement
      sendAgreement ratchetPublic baseValid torsionX torsionY certificate accessKey requestId : List B) :
    (session o s a p q size jump message checks senderIdentity ourIdentity localAddress uuid device dh1 dh2 dh3
      oneTime kem receiveAgreement sendAgreement ratchetPublic baseValid torsionX torsionY certificate accessKey
      requestId).map (List.map f) =
    session o' s' a' p q size jump (message.map f) (checks.map f) (senderIdentity.map f) (ourIdentity.map f)
      (localAddress.map f) (uuid.map f) (device.map f) (dh1.map f) (dh2.map f) (dh3.map f) (oneTime.map f)
      (kem.map f) (receiveAgreement.map f) (sendAgreement.map f) (ratchetPublic.map f) (baseValid.map f)
      (torsionX.map f) (torsionY.map f) (certificate.map f) (accessKey.map f) (requestId.map f) := by
  simp only [session, List.map_cons, List.map_nil, List.map_append, List.map_drop, List.map_take,
    ByteAuth.release_map ha, OpenResult.get_map ha, OpenResult.finish_map ha, CbcOpen.decryptCore_map ho,
    Establish.part_map, messageKeys_map hs, selectAt_map ha, chainKeys_map hs, pqKeys_map hs ha, keys_map hs,
    varintValue_map ha, lit_map ha, all_map ha, Establish.accepted_map ha, prekeyMask_map ha,
    ByteAuth.equalMask_map ha, List.map_replicate, ha.const, signalMask_map ha, Establish.addresses_map ha,
    MessageMac.verifyMask_map hs ha, Establish.session_map ha, Establish.metadata_map ha,
    ChainSend.nextCounter_map hs ha]

theorem text_map (ha : ByteAuth.Hom a a' f) (capacity : Nat) (plain : List B) :
    (text a capacity plain).map (List.map f) = text a' capacity (plain.map f) := by
  have length (high : B) :
      f ((List.range 7).foldl (fun acc k => a.xor acc (a.and (a.maskBit high (k + 1)) (a.const (2 ^ k)))) (a.const 0)) =
        (List.range 7).foldl (fun acc k => a'.xor acc (a'.and (a'.maskBit (f high) (k + 1)) (a'.const (2 ^ k))))
          (a'.const 0) := by
    rw [foldl_hom (f := f) _ (fun acc k => a'.xor acc (a'.and (a'.maskBit (f high) (k + 1)) (a'.const (2 ^ k))))
      (fun acc x => by simp only [ha.xor, ha.and, ha.maskBit, ha.const]), ha.const]
  simp only [text, List.map_cons, List.map_nil, List.map_map, Function.comp_def, ByteAuth.release_map ha, all_map ha,
    ByteAuth.eqMask_map ha, OpenResult.get_map ha, List.map_drop, ha.const, Unpad.chooseByte_map ha, top_map ha,
    ha.not, ha.and, ha.xor, ha.maskBit, atMost_map ha, lit_map ha, pick_map ha, length]

end Refinement

#print axioms certificate_map
#print axioms prekeyOpen_map
#print axioms prekeyShape_map
#print axioms signalShape_map
#print axioms session_map
#print axioms text_map

theorem gapMask_map {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a a' f)
    (c : List B) (offset : Nat) (g : Gap) : f (gapMask a c offset g) = gapMask a' (c.map f) offset g := by
  simp only [gapMask, all_map ha, List.map_cons, List.map_nil, whenever_map ha, ha.and, ByteAuth.eqMask_map ha,
    OpenResult.get_map ha, ha.const, varintShape_map ha]

theorem keyChoices_map {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a a' f)
    (c : List B) (offset j : Nat) (gs : List Gap) (ms : List B) :
    (keyChoices a c offset j gs ms).map (fun choice => (f choice.1, f choice.2)) =
      keyChoices a' (c.map f) offset j gs (ms.map f) := by
  induction gs generalizing ms with
  | nil => rfl
  | cons g gs ih =>
      cases ms with
      | nil => rfl
      | cons m ms => simp only [keyChoices, List.map_cons, ih, OpenResult.get_map ha]

theorem withAccessKey_map {o : Aes.Ops B} {o' : Aes.Ops B'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'}
    (ho : Aes.Hom o o' f) (ha : ByteAuth.Hom a a' f) (cert offset : Nat) (conversation plain : List B) :
    (withAccessKey o a cert offset conversation plain).map (List.map f) =
      withAccessKey o' a' cert offset (conversation.map f) (plain.map f) := by
  have masks : (gaps.map (gapMask a (plain.drop 8) offset)).map f =
      gaps.map (gapMask a' ((plain.map f).drop 8) offset) := by
    simp only [List.map_map, Function.comp_def, gapMask_map ha, List.map_drop]
  have key : ((List.range 32).map (fun j => pick a (keyChoices a (plain.drop 8) offset j gaps
      (gaps.map (gapMask a (plain.drop 8) offset))))).map f =
      (List.range 32).map (fun j => pick a' (keyChoices a' ((plain.map f).drop 8) offset j gaps
        (gaps.map (gapMask a' ((plain.map f).drop 8) offset)))) := by
    simp only [List.map_map, Function.comp_def, pick_map ha, keyChoices_map ha, ← masks, List.map_drop]
  simp only [withAccessKey, List.map_cons, List.map_nil, List.map_append, List.map_take, List.map_drop, any_map ha,
    lit_map ha, ChainSend.selectState_map ha, Aes.encryptExpanded_map ho, Aes.expandKey_map ho, Establish.part_map,
    key, masks]

#print axioms withAccessKey_map

end TlsMpc.Signal.ReceiveFirst
