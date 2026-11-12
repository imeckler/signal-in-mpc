import TlsMpc.KernelSpecs.SealSend
import TlsMpc.BundleProofs

/-!
# What `bundle-seal` sends to a device that has not answered (multi-device track, part 1)

New file; it changes no definition and no emitter imports it.

`bundle-seal` (`TlsMpc/BundleKernels.lean`, `BundleKernel.bundleSeal`) is the seal of every message
to a device whose session we started and that has not answered yet (kinds 1 and 2 of a device
list, MULTI_DEVICE.md section 5). Its body is `Establish.sealMessage`, for which only `_map`
lemmas existed (`BundleProofs.bundleSeal_spec` states the kernel against that body on concrete
operations). This file says WHAT BYTES it produces, against references:

* **Checked against libsignal's structure (transcriptions, libsignal v0.106.1 in
  `.deps/libsignal-v0.106.1`):**
  - `Reference.preKeySignalMessage`: `protocol.rs`, `PreKeySignalMessage::new`: the version byte
    `((message_version & 0xF) << 4) | CIPHERTEXT_MESSAGE_CURRENT_VERSION` (= 4), then the protobuf
    `proto/wire.proto` `PreKeySignalMessage`, fields in TAG order 1 … 8 (prost-derive 0.14.4,
    `src/lib.rs` line 91 sorts the fields by tag before encoding): `pre_key_id` (1, only with a
    one-time prekey), `base_key` (2, `05 ‖ key`), `identity_key` (3, `05 ‖ key`), `message` (4,
    the SignalMessage), `registration_id` (5), `signed_pre_key_id` (6), `kyber_pre_key_id` (7),
    `kyber_ciphertext` (8, `kem::SerializedCiphertext`: key type 8 ‖ ciphertext). The encoding of a
    `uint32` is a parameter: libsignal writes the canonical varint (`SealValue.Reference.varint`);
    the kernel writes `Reference.varint5`, the same value as five LEB128 groups (a deliberate
    difference, `TlsMpc/Signal/Establish.lean` header: the canonical form would make the envelope
    length depend on the contact's prekey ids). `varint5_decode` / `varint_decode` prove that the
    LEB128 value of both is the id (what a protobuf decoder such as prost's reads; prost is not
    modelled here).
  - `Reference.sealV1Typed`: sealed sender v1 (`SealValue.Reference.sealV1`, the transcription of
    `sealed_sender_encrypt_from_usmc`) with the `UnidentifiedSenderMessage.Message.type` as a
    parameter; `PREKEY_MESSAGE = 1` (`proto/sealed_sender.proto` line 44). `sealV1Typed 2` is
    `sealV1` by definition (`sealV1Typed_message`).
* **Checked against the repository's own reference:** the SignalMessage inside (field 4) is the
  `wire` of `SpqrSend.canonical` (textbook symmetric ratchet `Symmetric.derive`, SPQR chain
  `SpqrChain.material`, `Send.message`), on the send input `Establish.sendInput` read from the
  record, exactly as for the established path (`SealSend.lean`); with the two addresses
  (`Serialization.Shape.withAddresses = true`), as libsignal's `message_encrypt` does while the
  session is unacknowledged.

PROVED (standard axioms only; no `sorry`, `native_decide`, `bv_decide`):

* `encode_value`, `idField_value`: the kernel's `uint32` fields are `key ‖ varint5 (u32BE id)`.
* `varint5_decode`, `varint_decode`: both encodings decode (LEB128) to the value.
* `preKeyMessage_value`: `Establish.preKeyMessage` IS `Reference.preKeySignalMessage varint5`.
* `sealedSender_value`: `Establish.sealedSender` IS `Reference.sealV1Typed`.
* `sealMessage_value`: `Establish.sealMessage` on concrete operations is `sealMessageValue`: on
  accepted inputs (the send step accepts, both sealed-sender agreements nonzero, the computed
  sender key is the stored one, the built text's validity byte is 255) status 255, the advanced
  session block and the envelope `sealV1Typed 1 … (preKeySignalMessage varint5 …)`; otherwise
  status 0, the old ratchet state and an all-zero envelope of the same length.
* `bundleSeal_value`: the deployed kernel `bundle-seal` on every input assignment is
  `sealMessageValue` of its input fields (with `BundleProofs.bundleSeal_spec`).
* `bundleSeal_accepted`: when the opened status is 255, the opened envelope is the reference
  PreKey sealed-sender envelope and the stored record carries the advanced state.

NOT proved here: that libsignal's Rust is these transcriptions (they are read from the source, not
machine-linked), that the agreements are X25519 of the right keys (kernel inputs), the SignalMessage
against the Signal/SPQR specifications (it is the repository's `SpqrSend.canonical`), and any
cryptographic property. What the session record and `pending` hold after establishment (the keys
from the PQXDH agreements, the Kyber ciphertext) is `EstablishFirstMessage.lean`.
-/
namespace TlsMpc.KernelSpecs.EstablishSeal
open Std.Tactic.BVDecide
open TlsMpc TlsMpc.Signal
open TlsMpc.KernelSpecs.SealValue (Byte)
open TlsMpc.KernelSpecs.SealValue.Reference

/-! ## The reference -/
namespace Reference

/-- `UnidentifiedSenderMessage.Message` (sealed_sender.proto): `type` (1) = `msgType`,
`senderCertificate` (2), `content` (3); no content hint, no group id. -/
def messageContentTyped (msgType : Nat) (certificate content : List Byte) : List Byte :=
  varintField 1 msgType ++ lengthDelimited 2 certificate ++ lengthDelimited 3 content

/-- Sealed sender v1 (`sealed_sender_encrypt_from_usmc`, v1 arm) of a content of type `msgType`;
otherwise word for word `SealValue.Reference.sealV1`. -/
def sealV1Typed (msgType : Nat) (recipientIdentity ephemeralPublic senderIdentity ephemeralAgreement
    staticAgreement certificate content : List Byte) : List Byte :=
  let ephemeralKeys := hkdfSha256 (saltPrefix ++ djb recipientIdentity ++ djb ephemeralPublic)
    ephemeralAgreement [] 96
  let chainKey := ephemeralKeys.take 32
  let encryptedStatic := aes256CtrHmacSha256Encrypt (djb senderIdentity)
    ((ephemeralKeys.drop 32).take 32) ((ephemeralKeys.drop 64).take 32)
  let staticKeys := hkdfSha256 (chainKey ++ encryptedStatic) staticAgreement [] 96
  let encryptedMessage := aes256CtrHmacSha256Encrypt (messageContentTyped msgType certificate content)
    ((staticKeys.drop 32).take 32) ((staticKeys.drop 64).take 32)
  0x11 :: (lengthDelimited 1 (djb ephemeralPublic) ++ lengthDelimited 2 encryptedStatic ++
    lengthDelimited 3 encryptedMessage)

/-- `sealed_sender.proto`: `PREKEY_MESSAGE = 1`. -/
def prekeyMessage : Nat := 1

theorem sealV1Typed_message (r e s ea sa c m : List Byte) : sealV1Typed 2 r e s ea sa c m = sealV1 r e s ea sa c m :=
  rfl

/-- `((message_version & 0xF) << 4) | CIPHERTEXT_MESSAGE_CURRENT_VERSION` (= 4). -/
def versionByte (messageVersion : Byte) : Byte := ((messageVersion &&& 15) <<< 4) ||| 4

/-- A `uint32` as five LEB128 groups (continuation bit on the first four): the kernel's form. -/
def varint5 (n : Nat) : List Byte :=
  (List.range 5).map (fun i => BitVec.ofNat 8 (n / 128 ^ i % 128 + if i < 4 then 128 else 0))

/-- The value of a LEB128 byte string (low group first; continuation bits ignored). -/
def leb128 : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat % 128 + 128 * leb128 bs

/-- The big-endian value of four stored bytes. -/
def u32BE (bytes : List Byte) : Nat :=
  (bytes.getD 0 0).toNat * 2 ^ 24 + (bytes.getD 1 0).toNat * 2 ^ 16 + (bytes.getD 2 0).toNat * 2 ^ 8 +
    (bytes.getD 3 0).toNat

/-- A protobuf `uint32` field, with the varint encoding as a parameter. -/
def uint32Field (uint32 : Nat → List Byte) (field value : Nat) : List Byte := key field 0 ++ uint32 value

/-- `KeyType::Kyber1024`, the type byte of a serialized Kyber key or ciphertext. -/
def kyberType : Byte := 8

/-- **libsignal `PreKeySignalMessage::new`** (protocol.rs:341), serialized: version byte, then the
protobuf fields in tag order. `uint32` is the varint encoding of the four ids: libsignal's is
`varint`, the kernel's `varint5`. -/
def preKeySignalMessage (uint32 : Nat → List Byte) (messageVersion : Byte) (registrationId : Nat)
    (preKeyId : Option Nat) (signedPreKeyId kyberPreKeyId : Nat)
    (kyberCiphertext baseKey identityKey message : List Byte) : List Byte :=
  versionByte messageVersion ::
    ((match preKeyId with | some id => uint32Field uint32 1 id | none => []) ++
      lengthDelimited 2 (djb baseKey) ++ lengthDelimited 3 (djb identityKey) ++ lengthDelimited 4 message ++
      uint32Field uint32 5 registrationId ++ uint32Field uint32 6 signedPreKeyId ++
      uint32Field uint32 7 kyberPreKeyId ++ lengthDelimited 8 (kyberType :: kyberCiphertext))

end Reference

open Reference

/-! ## The `uint32` fields -/

theorem pack_toNat (b0 b1 b2 b3 : Byte) :
    (Sha256.concrete.pack b0 b1 b2 b3).toNat =
      b0.toNat * 2 ^ 24 + b1.toNat * 2 ^ 16 + b2.toNat * 2 ^ 8 + b3.toNat := by
  show ((b0 ++ b1) ++ (b2 ++ b3)).toNat = _
  have h1 := b1.isLt
  have h3 := b3.isLt
  have h01 : (b2 ++ b3).toNat < 2 ^ 16 := (b2 ++ b3).isLt
  rw [BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt h1, ← Nat.shiftLeft_add_eq_or_of_lt h3]
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt h3] at h01
  rw [← Nat.shiftLeft_add_eq_or_of_lt h01]
  simp only [Nat.shiftLeft_eq]
  omega

theorem pack_value (id : List Byte) :
    (Varint.pack Sha256.concrete ByteAuth.concrete id).toNat = u32BE id := by
  simp only [Varint.pack, OpenResult.get, pack_toNat, u32BE, List.getD_eq_getElem?_getD]
  rfl

theorem group_value (w : BitVec 32) (i : Nat) :
    ByteAuth.concrete.and (Sha256.concrete.unpack (Sha256.concrete.shr w (7 * i)) 3) (ByteAuth.concrete.const 127) =
      BitVec.ofNat 8 (w.toNat / 128 ^ i % 128) := by
  apply BitVec.eq_of_toNat_eq
  show ((w >>> (7 * i)).extractLsb' (8 * (3 - 3)) 8 &&& BitVec.ofNat 8 127).toNat = _
  rw [BitVec.toNat_and, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  have h127 : (127 : Nat) % 2 ^ 8 = 2 ^ 7 - 1 := by decide
  rw [h127, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 7 ∣ 2 ^ 8)]
  simp only [Nat.sub_self, Nat.mul_zero, Nat.shiftRight_zero, Nat.shiftRight_eq_div_pow]
  rw [Nat.pow_mul]
  simp only [Nat.reducePow]
  generalize w.toNat / 128 ^ i = x
  omega

theorem continuation_value (m : Nat) (hm : m < 128) (c : Bool) :
    BitVec.ofNat 8 m ^^^ BitVec.ofNat 8 (if c then 128 else 0) = BitVec.ofNat 8 (m + if c then 128 else 0) := by
  have all : ∀ m : Fin 128, BitVec.ofNat 8 m.val ^^^ (128 : BitVec 8) = BitVec.ofNat 8 (m.val + 128) := by decide
  cases c
  · simp only [Bool.false_eq_true, if_false, Nat.add_zero]
    exact BitVec.xor_zero
  · exact all ⟨m, hm⟩

theorem encode_value (w : BitVec 32) :
    Varint.encode Sha256.concrete ByteAuth.concrete w 5 = varint5 w.toNat := by
  simp only [Varint.encode, Varint.encodeGroups, Varint.groups, varint5]
  apply List.map_congr_left
  intro i hi
  have hi5 : i < 5 := List.mem_range.mp hi
  have hget : OpenResult.get ByteAuth.concrete ((List.range 5).map (fun i =>
      ByteAuth.concrete.and (Sha256.concrete.unpack (Sha256.concrete.shr w (7 * i)) 3) (ByteAuth.concrete.const 127))) i =
      BitVec.ofNat 8 (w.toNat / 128 ^ i % 128) := by
    simp only [OpenResult.get, List.getElem?_map, List.getElem?_range hi5, Option.map_some, Option.getD_some]
    exact group_value w i
  rw [hget]
  have hc : ByteAuth.concrete.const (if i + 1 < 5 then 128 else 0) = BitVec.ofNat 8 (if decide (i < 4) then 128 else 0) := by
    by_cases h : i < 4
    · simp only [show i + 1 < 5 by omega, if_true, decide_eq_true h]; rfl
    · simp only [show ¬ i + 1 < 5 by omega, if_false, decide_eq_false h]; rfl
  have hif : (if i < 4 then 128 else 0) = (if decide (i < 4) then 128 else 0) := by
    by_cases h : i < 4 <;> simp [h]
  change BitVec.ofNat 8 (w.toNat / 128 ^ i % 128) ^^^ ByteAuth.concrete.const (if i + 1 < 5 then 128 else 0) = _
  rw [hc, continuation_value _ (Nat.mod_lt _ (by decide)), hif]

theorem idField_value (tag : Nat) (htag : tag < 128) (id : List Byte) :
    Establish.idField Sha256.concrete ByteAuth.concrete tag id = BitVec.ofNat 8 tag :: varint5 (u32BE id) := by
  rw [Establish.idField, encode_value, pack_value]
  rfl

theorem uint32Field_varint5 (field : Nat) (hf : 8 * field < 128) (id : List Byte) :
    uint32Field varint5 field (u32BE id) = BitVec.ofNat 8 (8 * field) :: varint5 (u32BE id) := by
  simp only [uint32Field, key, Nat.add_zero, SealValue.varint_small _ hf]
  rfl

/-- The kernel's five groups decode to the value (`n < 2^35`, so every `uint32`). -/
theorem varint5_decode (n : Nat) (h : n < 2 ^ 35) : leb128 (varint5 n) = n := by
  simp only [varint5, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, leb128, BitVec.toNat_ofNat]
  simp only [Nat.reducePow, Nat.pow_zero, Nat.pow_one, Nat.div_one, Nat.reduceLT, if_true, if_false,
    Nat.lt_irrefl, Nat.add_zero]
  omega

/-- libsignal's canonical varint decodes to the value. -/
theorem varint_decode (n : Nat) : leb128 (varint n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
      by_cases h : n < 128
      · rw [SealValue.varint_small n h, leb128, leb128, BitVec.toNat_ofNat]
        omega
      · rw [SealValue.varint_large n h, leb128, ih (n / 128) (by omega), BitVec.toNat_ofNat]
        omega

theorem u32BE_lt (id : List Byte) : u32BE id < 2 ^ 32 := by
  have := (id.getD 0 0).isLt
  have := (id.getD 1 0).isLt
  have := (id.getD 2 0).isLt
  have := (id.getD 3 0).isLt
  simp only [u32BE]
  omega

/-! ## The PreKeySignalMessage -/

theorem preKeyMessage_value (withOneTime : Bool) (version : Byte) (pending identity signal : List Byte)
    (hp : pending.length < 2 ^ 32) (hi : identity.length < 2 ^ 32) (hs : signal.length < 2 ^ 32) :
    Establish.preKeyMessage Sha256.concrete ByteAuth.concrete withOneTime version pending identity signal =
      preKeySignalMessage varint5 version (u32BE (Establish.part pending 0 4))
        (if withOneTime then some (u32BE (Establish.part pending 4 4)) else none)
        (u32BE (Establish.part pending 8 4)) (u32BE (Establish.part pending 12 4))
        (pending.drop 48) (Establish.part pending 16 32) identity signal := by
  have b2 := SealValue.bytesField_value 2 (by decide)
  have b3 := SealValue.bytesField_value 3 (by decide)
  have b4 := SealValue.bytesField_value 4 (by decide)
  have b8 := SealValue.bytesField_value 8 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at b2 b3 b4 b8
  have hc5 : ByteAuth.concrete.const 5 = (5 : Byte) := rfl
  have hc8 : ByteAuth.concrete.const 8 = (8 : Byte) := rfl
  have hpart : (Establish.part pending 16 32).length ≤ 32 := by
    simp only [Establish.part, List.length_take]
    omega
  have hdrop : (pending.drop 48).length ≤ pending.length := by
    simp only [List.length_drop]
    omega
  have u1 := uint32Field_varint5 1 (by decide)
  have u5 := uint32Field_varint5 5 (by decide)
  have u6 := uint32Field_varint5 6 (by decide)
  have u7 := uint32Field_varint5 7 (by decide)
  simp only [Nat.reduceMul] at u1 u5 u6 u7
  simp only [Establish.preKeyMessage, hc5, hc8]
  rw [b2 _ (by simp only [List.length_cons]; omega), b3 _ (by simp only [List.length_cons]; omega),
    b4 _ (by omega), b8 _ (by simp only [List.length_cons]; omega)]
  cases withOneTime <;>
    simp only [preKeySignalMessage, Serialization.versionByte_value, versionByte, idField_value 8 (by decide),
      idField_value 40 (by decide), idField_value 48 (by decide), idField_value 56 (by decide), u1, u5, u6, u7,
      djb, kyberType, Bool.false_eq_true, if_true, if_false, List.append_assoc, List.cons_append,
      List.singleton_append, List.nil_append]

/-! ## Sealed sender with the message type -/

theorem usmc_value (kind : Nat) (hk : kind < 128) (certificate inner : List Byte) (hc : certificate.length < 2 ^ 32)
    (hi : inner.length < 2 ^ 32) :
    Establish.usmc ByteAuth.concrete kind certificate inner = messageContentTyped kind certificate inner := by
  have b2 := SealValue.bytesField_value 2 (by decide) certificate (by omega)
  have b3 := SealValue.bytesField_value 3 (by decide) inner (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd] at b2 b3
  simp only [Establish.usmc, b2, b3, messageContentTyped, varintField, key,
    SealValue.varint_small 8 (by decide), SealValue.varint_small kind hk]
  rfl

theorem usmc_length_le (kind : Nat) (certificate inner : List Byte) :
    (Establish.usmc ByteAuth.concrete kind certificate inner).length ≤ certificate.length + inner.length + 24 := by
  simp only [Establish.usmc, List.length_append, List.length_cons, List.length_nil]
  have := SealValue.bytesField_length_le 18 certificate
  have := SealValue.bytesField_length_le 26 inner
  omega

/-- **`Establish.sealedSender` is sealed sender v1 with message type `kind`.** -/
theorem sealedSender_value (kind : Nat) (hk : kind < 128)
    (recipient ephemeralPublic senderPublic ephemeralDh staticDh certificate inner : List Byte)
    (he : ephemeralPublic.length < 2 ^ 32) (hs : senderPublic.length < 2 ^ 32)
    (hc : certificate.length < 2 ^ 32) (hi : inner.length < 2 ^ 32) :
    Establish.sealedSender Aes.concrete Sha256.concrete ByteAuth.concrete kind recipient ephemeralPublic senderPublic
        ephemeralDh staticDh certificate inner =
      sealV1Typed kind recipient ephemeralPublic senderPublic ephemeralDh staticDh certificate inner := by
  have b1 := SealValue.bytesField_value 1 (by decide)
  have b2 := SealValue.bytesField_value 2 (by decide)
  have b3 := SealValue.bytesField_value 3 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at b1 b2 b3
  have hlabel : (TlsKdf.ascii "UnidentifiedDelivery").map Sha256.concrete.byteConst = saltPrefix := rfl
  have hc5 : ByteAuth.concrete.const 5 = (5 : Byte) := rfl
  have hc17 : ByteAuth.concrete.const 17 = (0x11 : Byte) := rfl
  have hu := usmc_length_le kind certificate inner
  rw [usmc_value _ hk _ _ hc hi] at hu
  simp only [Establish.sealedSender, sealV1Typed, hlabel, hc5, hc17, SealValue.material_value]
  rw [SealValue.encrypt_value _ _ _ (SealValue.key32 _ _ 32 (by omega)),
    SealValue.encrypt_value _ _ _ (SealValue.key32 _ _ 32 (by omega)), usmc_value _ hk _ _ hc hi]
  rw [b1 _ (by simp only [List.length_cons]; omega),
    b2 _ (Nat.lt_of_le_of_lt (SealValue.aes256CtrHmacSha256Encrypt_length_le _ _ _)
      (by simp only [List.length_cons]; omega)),
    b3 _ (Nat.lt_of_le_of_lt (SealValue.aes256CtrHmacSha256Encrypt_length_le _ _ _) (by omega))]
  rfl

/-! ## `sealMessage` on concrete values -/

/-- The send input `Establish.sendInput` on concrete values: session block, metadata (for the
recipient's UUID and device), own address, the built text's kind and plaintext. -/
abbrev inputOf (size : Nat) (session metadata localAddress text : List Byte) : SpqrSend.Input Byte :=
  Establish.sendInput ByteAuth.concrete session metadata localAddress (OpenResult.get ByteAuth.concrete text 1)
    (Establish.part text 2 size)

/-- **The reference PreKey sealed-sender envelope**: sealed sender v1 of type `PREKEY_MESSAGE` from
`senderPublic` to the stored recipient identity, of the PreKeySignalMessage (version and ids from the
record and `pending`, base key `pending[16..48]`, our identity key from the record, Kyber ciphertext
`pending[48..]`) carrying the SignalMessage of the reference send step. -/
def envelopeOf (withOneTime : Bool) (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape) (size : Nat)
    (session metadata pending certificate localAddress text ephemeralPublic senderPublic ephemeralAgreement
      staticAgreement : List Byte) : List Byte :=
  let i := inputOf size session metadata localAddress text
  sealV1Typed prekeyMessage i.receiver ephemeralPublic senderPublic ephemeralAgreement staticAgreement certificate
    (preKeySignalMessage varint5 i.version (u32BE (Establish.part pending 0 4))
      (if withOneTime then some (u32BE (Establish.part pending 4 4)) else none)
      (u32BE (Establish.part pending 8 4)) (u32BE (Establish.part pending 12 4))
      (pending.drop 48) (Establish.part pending 16 32) i.sender (SpqrSend.canonical shape pqShape i).wire)

/-- `Establish.sealMessage`, evaluated. -/
def sealMessageValue (withOneTime : Bool) (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape) (size : Nat)
    (session metadata pending certificate localAddress text ephemeralPublic senderPublic ephemeralAgreement
      staticAgreement : List Byte) : List (List Byte) :=
  let i := inputOf size session metadata localAddress text
  let p := SpqrSend.canonical shape pqShape i
  let envelope := envelopeOf withOneTime shape pqShape size session metadata pending certificate localAddress text
    ephemeralPublic senderPublic ephemeralAgreement staticAgreement
  let kind := OpenResult.get ByteAuth.concrete text 1
  let plaintext := Establish.part text 2 size
  if SpqrSend.accepted shape pqShape i ∧ boundAccepted ephemeralAgreement staticAgreement senderPublic i.sender ∧
      OpenResult.get ByteAuth.concrete text 0 = 255 then
    [[255], session.take 1 ++ p.nextCounter ++ Establish.part session 5 36 ++ p.nextChainKey ++ p.nextPqChainKey ++
      p.nextPqCounter ++ Establish.part session 109 8 ++ [kind] ++ Establish.part session 118 64 ++ plaintext,
      envelope]
  else
    [[0], session.take 1 ++ i.counter ++ Establish.part session 5 36 ++ i.chainKey ++ i.pqChainKey ++
      i.pqCounter ++ Establish.part session 109 8 ++ [kind] ++ Establish.part session 118 64 ++ plaintext,
      List.replicate envelope.length 0]

theorem wire_length_le (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape) (i : SpqrSend.Input Byte)
    (hchunk : pqShape.hasChunk = false) :
    (SpqrSend.canonical shape pqShape i).wire.length ≤ i.ratchet.length + i.plaintext.length + i.addresses.length +
      shape.counterWidth + shape.previousWidth + pqShape.epochWidth + pqShape.indexWidth + 110 := by
  simp only [SpqrSend.canonical]
  refine Nat.le_trans (SealSend.message_length_le _ _ _ _ _ _ _ _ _ _ _ _ _) ?_
  rw [SpqrMessage.content_length, hchunk]
  simp only [Bool.false_eq_true, if_false]
  omega

theorem canonical_lengths (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape) (i : SpqrSend.Input Byte)
    (hc : i.counter.length = 4) (hk : i.chainKey.length = 32) (hpk : i.pqChainKey.length = 32)
    (hpc : i.pqCounter.length = 4) :
    (SpqrSend.canonical shape pqShape i).nextChainKey.length = i.chainKey.length ∧
      (SpqrSend.canonical shape pqShape i).nextCounter.length = i.counter.length ∧
      (SpqrSend.canonical shape pqShape i).nextPqChainKey.length = i.pqChainKey.length ∧
      (SpqrSend.canonical shape pqShape i).nextPqCounter.length = i.pqCounter.length := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [SpqrSend.canonical, Symmetric.derive, Symmetric.nextChainKey, Sha256.hmac_length, hk]
  · simp [SpqrSend.canonical, ChainSend.nextCounter, hc]
  · simp [SpqrSend.canonical, SpqrChain.material_length, hpk]
  · simp [SpqrSend.canonical, ChainSend.nextCounter, hpc]

theorem lengthDelimited_length_le (field : Nat) (hf : 8 * field + 2 < 128) (bytes : List Byte)
    (h : bytes.length < 2 ^ 64) : (lengthDelimited field bytes).length ≤ bytes.length + 11 := by
  rw [← SealValue.bytesField_value field hf bytes h]
  exact SealValue.bytesField_length_le _ _

theorem preKeySignalMessage_length_le (v : Byte) (r : Nat) (pk : Option Nat) (s k : Nat)
    (ct base identity message : List Byte) (hct : ct.length < 2 ^ 32) (hb : base.length < 2 ^ 32)
    (hi : identity.length < 2 ^ 32) (hm : message.length < 2 ^ 32) :
    (preKeySignalMessage varint5 v r pk s k ct base identity message).length ≤
      ct.length + base.length + identity.length + message.length + 200 := by
  have l2 := lengthDelimited_length_le 2 (by decide) (djb base) (by simp only [djb, List.length_cons]; omega)
  have l3 := lengthDelimited_length_le 3 (by decide) (djb identity) (by simp only [djb, List.length_cons]; omega)
  have l4 := lengthDelimited_length_le 4 (by decide) message (by omega)
  have l8 := lengthDelimited_length_le 8 (by decide) (kyberType :: ct) (by simp only [List.length_cons]; omega)
  have v5 : ∀ n, (varint5 n).length = 5 := by intro n; simp [varint5]
  have u : ∀ f, 8 * f < 128 → ∀ n, (uint32Field varint5 f n).length = 6 := by
    intro f hf n
    simp only [uint32Field, key, List.length_append, v5, Nat.add_zero, SealValue.varint_small _ hf,
      List.length_cons, List.length_nil]
  simp only [djb, List.length_cons] at l2 l3 l8
  cases pk <;>
    simp only [preKeySignalMessage, djb, List.length_cons, List.length_append, u 1 (by decide), u 5 (by decide),
      u 6 (by decide), u 7 (by decide), List.length_nil] <;> omega

/-- **`Establish.sealMessage` on concrete values** (the body of `bundle-seal` and `establish-seal`). -/
theorem sealMessage_value (withOneTime : Bool) (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape)
    (size : Nat) (session metadata pending certificate localAddress text ephemeralPublic senderPublic
      ephemeralAgreement staticAgreement : List Byte)
    (hsession : session.length = 262) (hchunk : pqShape.hasChunk = false)
    (hbound : pending.length + certificate.length + localAddress.length + size + shape.counterWidth +
      shape.previousWidth + pqShape.epochWidth + pqShape.indexWidth < 2 ^ 31)
    (he : ephemeralPublic.length < 2 ^ 32) (hs : senderPublic.length < 2 ^ 32) :
    Establish.sealMessage Aes.concrete Varint64.concrete Sha256.concrete ByteAuth.concrete withOneTime shape pqShape
        size session metadata pending certificate localAddress text ephemeralPublic senderPublic ephemeralAgreement
        staticAgreement =
      sealMessageValue withOneTime shape pqShape size session metadata pending certificate localAddress text
        ephemeralPublic senderPublic ephemeralAgreement staticAgreement := by
  have hwire := wire_length_le shape pqShape (inputOf size session metadata localAddress text) hchunk
  have hratchet : (inputOf size session metadata localAddress text).ratchet.length ≤ 32 := by
    simp only [inputOf, Establish.sendInput, Establish.part, List.length_take]
    omega
  have hplain : (inputOf size session metadata localAddress text).plaintext.length ≤ size := by
    simp only [inputOf, Establish.sendInput, Establish.part, List.length_take]
    omega
  have haddr : (inputOf size session metadata localAddress text).addresses.length ≤ localAddress.length + 19 := by
    simp only [inputOf, Establish.sendInput, Establish.addresses, List.length_cons, List.length_append,
      List.length_take, List.length_nil]
    omega
  have hsender : (inputOf size session metadata localAddress text).sender.length ≤ 32 := by
    simp only [inputOf, Establish.sendInput, Establish.part, List.length_take]
    omega
  have hc : (inputOf size session metadata localAddress text).counter.length = 4 := by
    simp only [inputOf, Establish.sendInput, Establish.part, List.length_take, List.length_drop, hsession]
    omega
  have hk : (inputOf size session metadata localAddress text).chainKey.length = 32 := by
    simp only [inputOf, Establish.sendInput, Establish.part, List.length_take, List.length_drop, hsession]
    omega
  have hpk : (inputOf size session metadata localAddress text).pqChainKey.length = 32 := by
    simp only [inputOf, Establish.sendInput, Establish.part, List.length_take, List.length_drop, hsession]
    omega
  have hpc : (inputOf size session metadata localAddress text).pqCounter.length = 4 := by
    simp only [inputOf, Establish.sendInput, Establish.part, List.length_take, List.length_drop, hsession]
    omega
  have hdrop : (pending.drop 48).length ≤ pending.length := by
    simp only [List.length_drop]
    omega
  have hpart : (Establish.part pending 16 32).length ≤ 32 := by
    simp only [Establish.part, List.length_take]
    omega
  simp only [inputOf] at hwire hratchet hplain haddr hsender hc hk hpk hpc
  generalize hI : Establish.sendInput ByteAuth.concrete session metadata localAddress
    (OpenResult.get ByteAuth.concrete text 1) (Establish.part text 2 size) = I at hwire hratchet hplain haddr hsender hc hk hpk hpc
  obtain ⟨lk, lc, lpk, lpc⟩ := canonical_lengths shape pqShape I hc hk hpk hpc
  have hpre := preKeyMessage_value withOneTime I.version pending I.sender (SpqrSend.canonical shape pqShape I).wire
    (by omega) (by omega) (by omega)
  have hpreLen : (preKeySignalMessage varint5 I.version (u32BE (Establish.part pending 0 4))
      (if withOneTime then some (u32BE (Establish.part pending 4 4)) else none)
      (u32BE (Establish.part pending 8 4)) (u32BE (Establish.part pending 12 4))
      (pending.drop 48) (Establish.part pending 16 32) I.sender (SpqrSend.canonical shape pqShape I).wire).length <
        2 ^ 32 :=
    Nat.lt_of_le_of_lt (preKeySignalMessage_length_le _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
      (by omega)) (by omega)
  have hseal := sealedSender_value 1 (by decide) I.receiver ephemeralPublic senderPublic ephemeralAgreement
    staticAgreement certificate _ he hs (by omega) hpreLen
  have h0 : ((0 : Byte) = 255) = False := by decide
  simp only [Establish.sealMessage, sealMessageValue, envelopeOf, prekeyMessage, inputOf, hI]
  rw [SpqrSend.prepare_concrete_correct, SpqrSend.acceptedMask_value, SealValue.boundMask_value, hpre, hseal]
  by_cases hA : SpqrSend.accepted shape pqShape I <;>
    by_cases hB : boundAccepted ephemeralAgreement staticAgreement senderPublic I.sender <;>
    by_cases hT : OpenResult.get ByteAuth.concrete text 0 = 255 <;>
    simp only [hA, hB, hT, h0, if_true, if_false, and_true, and_false, and_self, false_and, true_and,
      TlsProviderGate.gate_value, ByteAuth.release_accept, ByteAuth.release_reject, ChainSend.selectState_reject,
      ChainSend.selectState_accept _ _ lk, ChainSend.selectState_accept _ _ lc, ChainSend.selectState_accept _ _ lpk,
      ChainSend.selectState_accept _ _ lpc]

/-! ## The kernel -/

open TlsMpc.HybridKernel (lookup) in
/-- **`bundle-seal` on every input assignment**: its four outputs (status, conversation record,
timestamp, envelope) are `sealMessageValue` of the values of its input fields, the record framed by
the stored certificate and metadata. The only hypothesis bounds the public parameters. -/
theorem bundleSeal_value (cert : Nat) (withOneTime : Bool) (content counterWidth previousWidth epochWidth indexWidth : Nat)
    (assign : BVExpr.Assignment)
    (hbound : cert + content + counterWidth + previousWidth + epochWidth + indexWidth < 2 ^ 30) :
    let get := fun name => (lookup (BundleKernel.sealInputs cert content) name).map (BVExpr.eval assign)
    let record := get "conversation"
    let out := sealMessageValue withOneTime ⟨counterWidth, previousWidth, true⟩ ⟨epochWidth, indexWidth, 0, false⟩
      content ((record.drop cert).take 262) ((record.drop (cert + 262)).take 57) (get "pending")
      ((record.drop 0).take cert) (get "localAddress") (get "text") (get "ephemeralPublic") (get "senderPublic")
      (get "ephemeralAgreement") (get "staticAgreement")
    ReceiveKernel.values (BundleKernel.bundleSeal cert withOneTime content counterWidth previousWidth epochWidth
        indexWidth) assign =
      [out.getD 0 [], (record.drop 0).take cert ++ (out.getD 1 []).take 262 ++ (record.drop (cert + 262)).take 57,
        ((get "text").drop (2 + content)).take 8, out.getD 2 []] := by
  dsimp only
  have hrecord : ((lookup (BundleKernel.sealInputs cert content) "conversation").map (BVExpr.eval assign)).length =
      HybridKernel.conversationBytes cert 80 := by
    simp [lookup, HybridKernel.lookupFrom, BundleKernel.sealInputs, ByteCircuit.inputBytes]
  have hpending : ((lookup (BundleKernel.sealInputs cert content) "pending").map (BVExpr.eval assign)).length =
      1616 := by
    simp [lookup, HybridKernel.lookupFrom, BundleKernel.sealInputs, ByteCircuit.inputBytes,
      EstablishKernel.pendingBytes]
  have hlocal : ((lookup (BundleKernel.sealInputs cert content) "localAddress").map (BVExpr.eval assign)).length =
      17 := by
    simp [lookup, HybridKernel.lookupFrom, BundleKernel.sealInputs, ByteCircuit.inputBytes]
  have hephemeral : ((lookup (BundleKernel.sealInputs cert content) "ephemeralPublic").map
      (BVExpr.eval assign)).length = 32 := by
    simp [lookup, HybridKernel.lookupFrom, BundleKernel.sealInputs, HybridKdf.wordBytes]
  have hsender : ((lookup (BundleKernel.sealInputs cert content) "senderPublic").map
      (BVExpr.eval assign)).length = 32 := by
    simp [lookup, HybridKernel.lookupFrom, BundleKernel.sealInputs, HybridKdf.wordBytes]
  have hsession : ((((lookup (BundleKernel.sealInputs cert content) "conversation").map
      (BVExpr.eval assign)).drop cert).take 262).length = 262 := by
    simp only [List.length_take, List.length_drop, hrecord, HybridKernel.conversationBytes]
    omega
  have hcert : ((((lookup (BundleKernel.sealInputs cert content) "conversation").map
      (BVExpr.eval assign)).drop 0).take cert).length ≤ cert := by
    simp only [List.length_take]
    omega
  have hv := BundleKernel.bundleSeal_spec cert withOneTime content counterWidth previousWidth epochWidth indexWidth
    assign
  simp only [HybridKernel.sl, List.map_take, List.map_drop] at hv
  rw [hv, sealMessage_value _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsession rfl (by dsimp only; omega) (by omega) (by omega)]

/-- **An opened status 255 of `bundle-seal`**: the send step accepted, the sealed-sender checks
passed, the text was valid, the opened envelope is the reference PreKey sealed-sender envelope
`envelopeOf`, and the stored record carries the advanced ratchet state. -/
theorem sealMessageValue_accepted (withOneTime : Bool) (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape)
    (size : Nat) (session metadata pending certificate localAddress text ephemeralPublic senderPublic
      ephemeralAgreement staticAgreement : List Byte)
    (opened : (sealMessageValue withOneTime shape pqShape size session metadata pending certificate localAddress text
      ephemeralPublic senderPublic ephemeralAgreement staticAgreement).getD 0 [] = [255]) :
    let i := inputOf size session metadata localAddress text
    let p := SpqrSend.canonical shape pqShape i
    let out := sealMessageValue withOneTime shape pqShape size session metadata pending certificate localAddress text
      ephemeralPublic senderPublic ephemeralAgreement staticAgreement
    SpqrSend.accepted shape pqShape i ∧ boundAccepted ephemeralAgreement staticAgreement senderPublic i.sender ∧
      OpenResult.get ByteAuth.concrete text 0 = 255 ∧
      out.getD 1 [] = session.take 1 ++ p.nextCounter ++ Establish.part session 5 36 ++ p.nextChainKey ++
        p.nextPqChainKey ++ p.nextPqCounter ++ Establish.part session 109 8 ++
        [OpenResult.get ByteAuth.concrete text 1] ++ Establish.part session 118 64 ++ Establish.part text 2 size ∧
      out.getD 2 [] = envelopeOf withOneTime shape pqShape size session metadata pending certificate localAddress
        text ephemeralPublic senderPublic ephemeralAgreement staticAgreement := by
  intro i p out
  simp only [out, sealMessageValue] at opened ⊢
  split at opened
  · rename_i h
    simp only [if_pos h, List.getD_cons_succ, List.getD_cons_zero, and_true]
    exact ⟨h.1, h.2.1, h.2.2, rfl⟩
  · simp only [List.getD_cons_zero, List.cons.injEq, and_true] at opened
    exact absurd opened (by decide)

open TlsMpc.HybridKernel (lookup) in
/-- **`bundle-seal`, opened status 255**: the opened envelope (output 3) is the reference PreKey
sealed-sender envelope `envelopeOf` of the kernel's inputs, and the send was accepted. -/
theorem bundleSeal_accepted (cert : Nat) (withOneTime : Bool)
    (content counterWidth previousWidth epochWidth indexWidth : Nat) (assign : BVExpr.Assignment)
    (hbound : cert + content + counterWidth + previousWidth + epochWidth + indexWidth < 2 ^ 30)
    (opened : (ReceiveKernel.values (BundleKernel.bundleSeal cert withOneTime content counterWidth previousWidth
      epochWidth indexWidth) assign).getD 0 [] = [255]) :
    let get := fun name => (lookup (BundleKernel.sealInputs cert content) name).map (BVExpr.eval assign)
    let record := get "conversation"
    let session := (record.drop cert).take 262
    let metadata := (record.drop (cert + 262)).take 57
    let shape : Serialization.Shape := ⟨counterWidth, previousWidth, true⟩
    let pqShape : SpqrMessage.Shape := ⟨epochWidth, indexWidth, 0, false⟩
    let i := inputOf content session metadata (get "localAddress") (get "text")
    SpqrSend.accepted shape pqShape i ∧
      boundAccepted (get "ephemeralAgreement") (get "staticAgreement") (get "senderPublic") i.sender ∧
      OpenResult.get ByteAuth.concrete (get "text") 0 = 255 ∧
      (ReceiveKernel.values (BundleKernel.bundleSeal cert withOneTime content counterWidth previousWidth epochWidth
        indexWidth) assign).getD 3 [] =
        envelopeOf withOneTime shape pqShape content session metadata (get "pending") ((record.drop 0).take cert)
          (get "localAddress") (get "text") (get "ephemeralPublic") (get "senderPublic") (get "ephemeralAgreement")
          (get "staticAgreement") := by
  intro get record session metadata shape pqShape i
  have hv := bundleSeal_value cert withOneTime content counterWidth previousWidth epochWidth indexWidth assign hbound
  simp only at hv
  rw [hv] at opened ⊢
  simp only [List.getD_cons_zero, List.getD_cons_succ] at opened ⊢
  have facts := sealMessageValue_accepted _ _ _ _ _ _ _ _ _ _ _ _ _ _ opened
  exact ⟨facts.1, facts.2.1, facts.2.2.1, facts.2.2.2.2⟩

#print axioms bundleSeal_accepted
#print axioms encode_value
#print axioms varint5_decode
#print axioms varint_decode
#print axioms preKeyMessage_value
#print axioms sealedSender_value
#print axioms sealMessage_value
#print axioms bundleSeal_value
#print axioms sealMessageValue_accepted

end TlsMpc.KernelSpecs.EstablishSeal
