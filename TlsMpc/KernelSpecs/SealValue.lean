import TlsMpc.KernelSpecs.SealFixed

/-!
# What the seal kernels' sealed-sender envelope is (T7(b), part 1: `boundSeal`)

New file; it changes no definition and no emitter imports it.

`SealedSenderV1.boundSeal` is the sealed-sender v1 step of `signal-seal-official` /
`signal-seal-built` (HybridKernels.lean:456). This file states, on concrete bytes, WHAT BYTES it
produces, against `Reference.sealV1`: libsignal's sealed-sender v1 encryption of a
`UnidentifiedSenderMessageContent` of type MESSAGE, written here step by step in libsignal's own
terms (libsignal v0.106.1, `rust/protocol/src/sealed_sender.rs`, `sealed_sender_encrypt_from_usmc`,
v1 arm; `EphemeralKeys::calculate` with `Direction::Sending`; `StaticKeys::calculate`;
`crypto.rs`, `aes256_ctr_hmacsha256_encrypt`; `proto/sealed_sender.proto`):

* HKDF-SHA256 (RFC 5869: `TlsKdf.extract` / `TlsKdf.expandCore`, the textbook HKDF of the repo),
  HMAC-SHA256 (`Sha256.hmac`, RFC 2104 over `Sha256.hash`), AES-256 (`Aes.encryptCore … 8 14`,
  FIPS 197 transcription);
* AES-256-CTR as libsignal's `Aes256Ctr32` with a 12-byte zero nonce and initial counter 0: the
  plaintext XOR the keystream AES(key, 0¹² ‖ BE32(i)), i = 0, 1, …, where BE32(i) is the
  big-endian encoding of `BitVec.ofNat 32 i` (`Reference.aes256Ctr`);
* `aes256_ctr_hmacsha256_encrypt`: ciphertext ‖ the first 10 bytes of HMAC(mac key, ciphertext);
* protobuf: LEB128 varints for every key and length (no fuel), field key `8·field + wireType`.

The definition under test (`SealedSenderV1.sealCore`) instead uses a fuelled public varint
(`Varint.publicNat`), a loop over counter blocks with a shared expanded key, the prepared
(fast) HKDF expansion and pre-encoded one-byte tags.

PROVED (standard axioms only; no `sorry`, `native_decide`, `bv_decide`):

* `sealCore_value`: `SealedSenderV1.sealCore` on concrete operations IS `Reference.sealV1`
  (lengths of the public keys, certificate and inner message below 2³²).
* `boundSeal_value`: `boundSeal` outputs status 255 followed by `Reference.sealV1 …` when both
  agreements are nonzero (as 32-byte strings) and the computed sender key equals the stored one;
  otherwise status 0 followed by zeros of the same length. Nothing else.
* The pieces: `ctr_value` (AES-256-CTR), `encrypt_value`, `material_value` (HKDF),
  `bytesField_value` / `publicNat_value` (protobuf varint), `usmc_value`.

NOT proved here: that libsignal's Rust is this reference (the reference is a transcription; the
SignalReference/SealedSenderReferenceWork extraction proves only libsignal's
`aes256_ctr_hmacsha256_encrypt` = `SealedSenderV1.encrypt`, in another Lake project, under its
primitive models), that the agreements are X25519 of the right keys (kernel inputs
`ephemeralAgreement`, `staticAgreement`), and any cryptographic property.
-/
namespace TlsMpc.KernelSpecs.SealValue
open Std.Tactic.BVDecide
open TlsMpc TlsMpc.Signal

abbrev Byte := BitVec 8

/-! ## The reference -/
namespace Reference

/-- Protobuf base-128 varint (LEB128), any size. -/
def varint (n : Nat) : List Byte :=
  if h : n < 128 then [BitVec.ofNat 8 n] else BitVec.ofNat 8 (n % 128 + 128) :: varint (n / 128)
termination_by n
decreasing_by omega

/-- Protobuf field key: `field << 3 | wireType`. -/
def key (field wireType : Nat) : List Byte := varint (8 * field + wireType)

/-- A protobuf varint field. -/
def varintField (field value : Nat) : List Byte := key field 0 ++ varint value

/-- A protobuf length-delimited (`bytes`) field. -/
def lengthDelimited (field : Nat) (bytes : List Byte) : List Byte :=
  key field 2 ++ varint bytes.length ++ bytes

def hmacSha256 (key message : List Byte) : List Byte := Sha256.hmac Sha256.concrete key message

/-- RFC 5869 HKDF-SHA256: extract with `salt`, expand with `info` to `length` bytes. -/
def hkdfSha256 (salt ikm info : List Byte) (length : Nat) : List Byte :=
  TlsKdf.expandCore Sha256.concrete (TlsKdf.extract Sha256.concrete salt ikm) info length

def aes256 (key block : List Byte) : List Byte := Aes.encryptCore Aes.concrete 8 14 key block

/-- The big-endian bytes of a 32-bit word. -/
def be32 (w : BitVec 32) : List Byte :=
  [w.extractLsb' 24 8, w.extractLsb' 16 8, w.extractLsb' 8 8, w.extractLsb' 0 8]

/-- `Aes256Ctr32` counter block `i`: nonce 0¹² ‖ BE32(i). -/
def counterBlock (i : Nat) : List Byte := List.replicate 12 0 ++ be32 (BitVec.ofNat 32 i)

def keystream (key : List Byte) (blocks : Nat) : List Byte :=
  (List.range blocks).flatMap (fun i => aes256 key (counterBlock i))

/-- AES-256-CTR (`Aes256Ctr32::from_key(key, &[0; 12], 0)`): plaintext XOR keystream. -/
def aes256Ctr (key plain : List Byte) : List Byte :=
  List.zipWith (· ^^^ ·) plain (keystream key ((plain.length + 15) / 16))

/-- libsignal `crypto::aes256_ctr_hmacsha256_encrypt`. -/
def aes256CtrHmacSha256Encrypt (plain cipherKey macKey : List Byte) : List Byte :=
  let ciphertext := aes256Ctr cipherKey plain
  ciphertext ++ (hmacSha256 macKey ciphertext).take 10

/-- A serialized Curve25519 public key: type byte 0x05 ‖ key. -/
def djb (key : List Byte) : List Byte := 5 :: key

/-- `UnidentifiedSenderMessage.Message` (sealed_sender.proto): `type` (1) = MESSAGE (2),
`senderCertificate` (2), `content` (3); no content hint, no group id. -/
def messageContent (certificate content : List Byte) : List Byte :=
  varintField 1 2 ++ lengthDelimited 2 certificate ++ lengthDelimited 3 content

/-- The salt prefix of `EphemeralKeys::calculate`. -/
def saltPrefix : List Byte := (TlsKdf.ascii "UnidentifiedDelivery").map (BitVec.ofNat 8)

/-- **Sealed sender v1 encryption** (`sealed_sender_encrypt_from_usmc`, v1 arm) of a MESSAGE
content to `recipientIdentity` from `senderIdentity` with ephemeral key `ephemeralPublic`.
`ephemeralAgreement` = ephemeral private · recipient identity, `staticAgreement` = sender identity
private · recipient identity (computed by other kernels). -/
def sealV1 (recipientIdentity ephemeralPublic senderIdentity ephemeralAgreement staticAgreement
    certificate content : List Byte) : List Byte :=
  -- EphemeralKeys::calculate, Direction::Sending: salt = prefix ‖ their identity ‖ our ephemeral
  let ephemeralKeys := hkdfSha256 (saltPrefix ++ djb recipientIdentity ++ djb ephemeralPublic)
    ephemeralAgreement [] 96
  let chainKey := ephemeralKeys.take 32
  let encryptedStatic := aes256CtrHmacSha256Encrypt (djb senderIdentity)
    ((ephemeralKeys.drop 32).take 32) ((ephemeralKeys.drop 64).take 32)
  -- StaticKeys::calculate: salt = chain key ‖ encrypted static key
  let staticKeys := hkdfSha256 (chainKey ++ encryptedStatic) staticAgreement [] 96
  let encryptedMessage := aes256CtrHmacSha256Encrypt (messageContent certificate content)
    ((staticKeys.drop 32).take 32) ((staticKeys.drop 64).take 32)
  -- SEALED_SENDER_V1_FULL_VERSION ‖ UnidentifiedSenderMessage
  0x11 :: (lengthDelimited 1 (djb ephemeralPublic) ++ lengthDelimited 2 encryptedStatic ++
    lengthDelimited 3 encryptedMessage)

/-- What `boundSeal` checks: both agreements nonzero, the computed sender key the stored one. -/
def boundAccepted (ephemeralAgreement staticAgreement senderPublic expectedSender : List Byte) : Prop :=
  ephemeralAgreement ≠ List.replicate 32 0 ∧ staticAgreement ≠ List.replicate 32 0 ∧
    senderPublic = expectedSender

instance (e s p q : List Byte) : Decidable (boundAccepted e s p q) := inferInstanceAs (Decidable (_ ∧ _))

end Reference

open Reference

/-! ## Protobuf varints -/

theorem varint_small (n : Nat) (h : n < 128) : varint n = [BitVec.ofNat 8 n] := by
  rw [varint]; simp [h]

theorem varint_large (n : Nat) (h : ¬ n < 128) :
    varint n = BitVec.ofNat 8 (n % 128 + 128) :: varint (n / 128) := by
  rw [varint]; simp [h]

theorem publicNatLoop_value (fuel : Nat) : ∀ v, v < 128 ^ (fuel + 1) →
    Varint.publicNatLoop ByteAuth.concrete (fuel + 1) v = varint v := by
  induction fuel with
  | zero =>
      intro v hv
      have h : v < 128 := by simpa using hv
      simp only [Varint.publicNatLoop, h, if_true, varint_small v h]
      rfl
  | succ fuel ih =>
      intro v hv
      by_cases h : v < 128
      · simp only [Varint.publicNatLoop, h, if_true, varint_small v h]
        rfl
      · have hp : 128 ^ (fuel + 1 + 1) = 128 ^ (fuel + 1) * 128 := Nat.pow_succ (n := 128) (m := fuel + 1)
        have hdiv : v / 128 < 128 ^ (fuel + 1) := by
          rw [hp] at hv
          generalize 128 ^ (fuel + 1) = X at hv ⊢
          omega
        rw [Varint.publicNatLoop, if_neg h, ih _ hdiv, varint_large v h]
        rfl

theorem publicNat_value (v : Nat) (h : v < 2 ^ 64) : Varint.publicNat ByteAuth.concrete v = varint v := by
  apply publicNatLoop_value 9
  have : (2 : Nat) ^ 64 < 128 ^ (9 + 1) := by decide
  omega

theorem publicNatLoop_length_le (fuel v : Nat) :
    (Varint.publicNatLoop ByteAuth.concrete fuel v).length ≤ fuel := by
  induction fuel generalizing v with
  | zero => simp [Varint.publicNatLoop]
  | succ fuel ih =>
      simp only [Varint.publicNatLoop]
      split
      · simp
      · simp only [List.length_cons]
        have := ih (v / 128)
        omega

theorem publicNat_length_le (v : Nat) : (Varint.publicNat ByteAuth.concrete v).length ≤ 10 :=
  publicNatLoop_length_le 10 v

theorem bytesField_value (field : Nat) (hf : 8 * field + 2 < 128) (bytes : List Byte)
    (h : bytes.length < 2 ^ 64) :
    Serialization.bytesField ByteAuth.concrete (8 * field + 2) bytes = lengthDelimited field bytes := by
  simp only [Serialization.bytesField, lengthDelimited, key, varint_small _ hf, publicNat_value _ h]
  rfl

theorem bytesField_length_le (tag : Nat) (bytes : List Byte) :
    (Serialization.bytesField ByteAuth.concrete tag bytes).length ≤ bytes.length + 11 := by
  simp only [Serialization.bytesField, List.length_cons, List.length_append]
  have := publicNat_length_le bytes.length
  omega

/-! ## AES-256-CTR -/

theorem zipWith_append_split (f : Byte → Byte → Byte) (s t : List Byte) : ∀ l : List Byte,
    List.zipWith f l (s ++ t) = List.zipWith f (l.take s.length) s ++ List.zipWith f (l.drop s.length) t := by
  induction s with
  | nil => intro l; simp
  | cons x s ih =>
      intro l
      cases l with
      | nil => simp
      | cons y l => simp [ih]

theorem ctrLoop_value (expanded : List Byte) (he : expanded.length = 16 * (14 + 1)) :
    ∀ n index plain, SealedSenderV1.ctrLoop Aes.concrete expanded n index plain =
      List.zipWith (· ^^^ ·) plain ((List.range' index n).flatMap
        (fun i => Aes.encryptExpanded Aes.concrete 14 expanded (SealedSenderV1.counter Aes.concrete i))) := by
  intro n
  induction n with
  | zero => intro index plain; simp [SealedSenderV1.ctrLoop]
  | succ n ih =>
      intro index plain
      have hl := Aes.encryptExpanded_length Aes.concrete 14 expanded
        (SealedSenderV1.counter Aes.concrete index) he
      rw [SealedSenderV1.ctrLoop, ih, List.range'_succ, List.flatMap_cons, zipWith_append_split, hl]
      rfl

theorem counter_value (i : Nat) : SealedSenderV1.counter Aes.concrete i = counterBlock i := by
  simp only [SealedSenderV1.counter, counterBlock, be32]
  have hr : List.range 4 = [0, 1, 2, 3] := rfl
  rw [hr]
  simp only [List.map_cons, List.map_nil]
  have h0 : Aes.concrete.const 0 = (0 : Byte) := rfl
  rw [h0]
  congr 1
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [Aes.concrete, BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.reduceSub, Nat.reduceMul,
      Nat.reducePow, Nat.pow_zero, Nat.div_one, Nat.shiftRight_eq_div_pow] <;> omega

theorem ctr_value (key plain : List Byte) (hk : key.length = 32) :
    SealedSenderV1.ctr Aes.concrete key plain = aes256Ctr key plain := by
  have he : (Aes.expandKey Aes.concrete 8 14 key).length = 16 * (14 + 1) :=
    Aes.expandKey_length Aes.concrete 8 14 key (by omega) (by omega)
  rw [SealedSenderV1.ctr, ctrLoop_value _ he, aes256Ctr, keystream, List.range_eq_range']
  simp only [counter_value]
  rfl

theorem aes256Ctr_length_le (key plain : List Byte) : (aes256Ctr key plain).length ≤ plain.length := by
  simp only [aes256Ctr, List.length_zipWith]
  omega

theorem encrypt_value (cipher mac plain : List Byte) (hk : cipher.length = 32) :
    SealedSenderV1.encrypt Aes.concrete Sha256.concrete cipher mac plain =
      aes256CtrHmacSha256Encrypt plain cipher mac := by
  rw [SealedSenderV1.encrypt, ctr_value _ _ hk]
  rfl

theorem aes256CtrHmacSha256Encrypt_length_le (plain cipher mac : List Byte) :
    (aes256CtrHmacSha256Encrypt plain cipher mac).length ≤ plain.length + 10 := by
  simp only [aes256CtrHmacSha256Encrypt, List.length_append, List.length_take]
  have := aes256Ctr_length_le cipher plain
  omega

/-! ## HKDF and the content -/

theorem material_value (salt dh : List Byte) :
    SealedSenderV1.material Sha256.concrete salt dh = hkdfSha256 salt dh [] 96 := by
  rw [SealedSenderV1.material, TlsKdf.expandFast_correct]
  rfl

theorem hkdf_length (salt ikm info : List Byte) (length : Nat) :
    (hkdfSha256 salt ikm info length).length = length :=
  TlsKdf.expandCore_length _ _ _ _

theorem key32 (salt ikm : List Byte) (k : Nat) (hk : k + 32 ≤ 96) :
    (((hkdfSha256 salt ikm [] 96).drop k).take 32).length = 32 := by
  simp only [List.length_take, List.length_drop, hkdf_length]
  omega

theorem usmc_value (certificate inner : List Byte) (hc : certificate.length < 2 ^ 32)
    (hi : inner.length < 2 ^ 32) :
    SealedSenderV1.usmc ByteAuth.concrete certificate inner = messageContent certificate inner := by
  have b2 := bytesField_value 2 (by decide) certificate (by omega)
  have b3 := bytesField_value 3 (by decide) inner (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd] at b2 b3
  simp only [SealedSenderV1.usmc, b2, b3, messageContent, varintField, key, varint_small 8 (by decide),
    varint_small 2 (by decide)]
  rfl

theorem usmc_length_le (certificate inner : List Byte) :
    (SealedSenderV1.usmc ByteAuth.concrete certificate inner).length ≤ certificate.length + inner.length + 24 := by
  simp only [SealedSenderV1.usmc, List.length_append, List.length_cons, List.length_nil]
  have := bytesField_length_le 18 certificate
  have := bytesField_length_le 26 inner
  omega

/-! ## `sealCore` and `boundSeal` -/

/-- **`SealedSenderV1.sealCore` is sealed sender v1** (`Reference.sealV1`) on concrete values. -/
theorem sealCore_value (recipient ephemeralPublic senderPublic ephemeralDh staticDh certificate inner : List Byte)
    (he : ephemeralPublic.length < 2 ^ 32) (hs : senderPublic.length < 2 ^ 32)
    (hc : certificate.length < 2 ^ 32) (hi : inner.length < 2 ^ 32) :
    SealedSenderV1.sealCore Aes.concrete Sha256.concrete ByteAuth.concrete recipient ephemeralPublic senderPublic
        ephemeralDh staticDh certificate inner =
      sealV1 recipient ephemeralPublic senderPublic ephemeralDh staticDh certificate inner := by
  have b1 := bytesField_value 1 (by decide)
  have b2 := bytesField_value 2 (by decide)
  have b3 := bytesField_value 3 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at b1 b2 b3
  have hlabel : (TlsKdf.ascii "UnidentifiedDelivery").map Sha256.concrete.byteConst = saltPrefix := rfl
  have hc5 : ByteAuth.concrete.const 5 = (5 : Byte) := rfl
  have hc17 : ByteAuth.concrete.const 17 = (0x11 : Byte) := rfl
  -- the inner encryption's plaintext length
  have hu := usmc_length_le certificate inner
  rw [usmc_value _ _ hc hi] at hu
  simp only [SealedSenderV1.sealCore, sealV1, hlabel, hc5, hc17, material_value]
  rw [encrypt_value _ _ _ (key32 _ _ 32 (by omega)), encrypt_value _ _ _ (key32 _ _ 32 (by omega)),
    usmc_value _ _ hc hi]
  rw [b1 _ (by simp only [List.length_cons]; omega),
    b2 _ (Nat.lt_of_le_of_lt (aes256CtrHmacSha256Encrypt_length_le _ _ _) (by simp only [List.length_cons]; omega)),
    b3 _ (Nat.lt_of_le_of_lt (aes256CtrHmacSha256Encrypt_length_le _ _ _) (by omega))]
  rfl

theorem boundMask_value (ephemeralDh staticDh senderPublic expectedSender : List Byte) :
    ByteAuth.concrete.and (SealedSenderV1.agreementMask ByteAuth.concrete ephemeralDh staticDh)
        (ByteAuth.equalMask ByteAuth.concrete senderPublic expectedSender) =
      if boundAccepted ephemeralDh staticDh senderPublic expectedSender then 255 else 0 := by
  have hz : List.replicate 32 (ByteAuth.concrete.const 0) = List.replicate 32 (0 : Byte) := rfl
  simp only [SealedSenderV1.agreementMask, hz, ByteAuth.equalMask_value, boundAccepted]
  by_cases h1 : ephemeralDh = List.replicate 32 0 <;> by_cases h2 : staticDh = List.replicate 32 0 <;>
    by_cases h3 : senderPublic = expectedSender <;>
    simp only [h1, h2, h3, if_true, if_false, ne_eq, not_true_eq_false, not_false_eq_true,
      and_true, and_false] <;> first | rfl | decide

/-- **What `boundSeal` produces.** Status 255 and the sealed-sender v1 encryption
(`Reference.sealV1`) of `inner` when both agreements are nonzero and the computed sender key is
the stored one; otherwise status 0 and zeros, the same number of bytes. -/
theorem boundSeal_value (recipient ephemeralPublic senderPublic ephemeralDh staticDh certificate inner
    expectedSender : List Byte)
    (he : ephemeralPublic.length < 2 ^ 32) (hs : senderPublic.length < 2 ^ 32)
    (hc : certificate.length < 2 ^ 32) (hi : inner.length < 2 ^ 32) :
    SealedSenderV1.boundSeal Aes.concrete Sha256.concrete ByteAuth.concrete recipient ephemeralPublic senderPublic
        ephemeralDh staticDh certificate inner expectedSender =
      if boundAccepted ephemeralDh staticDh senderPublic expectedSender then
        255 :: sealV1 recipient ephemeralPublic senderPublic ephemeralDh staticDh certificate inner
      else 0 :: List.replicate
        (sealV1 recipient ephemeralPublic senderPublic ephemeralDh staticDh certificate inner).length 0 := by
  rw [SealedSenderV1.boundSeal, boundMask_value, sealCore_value _ _ _ _ _ _ _ he hs hc hi]
  split
  · rw [ByteAuth.release_accept]
  · rw [ByteAuth.release_reject]

#print axioms sealCore_value
#print axioms boundSeal_value

end TlsMpc.KernelSpecs.SealValue
