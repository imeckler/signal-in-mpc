import TlsMpc.KernelSpecs.EstablishSealValue
import TlsMpc.EstablishProofs

/-!
# The first message to a new device, from the key agreements (multi-device track, part 1)

New file; it changes no definition and no emitter imports it.

On a device refresh (MULTI_DEVICE.md section 3) `establish-session` turns the key agreements of
PQXDH into the device's records, and every message until the device answers is sealed by
`bundle-seal` from those records (section 5). `EstablishSealValue.lean` says what `bundle-seal`
produces from any record. This file composes the two for the FIRST message on a new session: the
envelope as a function of the key-agreement inputs as `establish-session` takes them (`dh1`, `dh2`,
`dh3`, `dh4`, `kemSecret`, `ratchetAgreement`, `kemCiphertext`, `basePublic`, `ratchetPublic`, …).

**The reference** (`Reference`, transcribed from libsignal v0.106.1 and SPQR, all HKDF-SHA256 as
`SealValue.Reference.hkdfSha256`, RFC 5869):

* `handshakeKeys`: `pqxdh.rs`, `pqxdh_initiate` + `HandshakeKeys::derive`: HKDF with no salt over
  `0xFF×32 ‖ DH1 ‖ DH2 ‖ DH3 [‖ DH4] ‖ kem shared secret`, info
  `WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024`, 96 bytes = root ‖ chain ‖ PQR key.
* `createChain`: `ratchet/keys.rs`, `RootKey::create_chain`: HKDF(salt = root, ikm = agreement,
  info `WhisperRatchet`), 64 bytes = new root ‖ sending chain key (`ratchet.rs`,
  `initialize_initiator_session`: our fresh sending ratchet key with their signed prekey).
* `spqrChainStart`: SPQR `src/chain.rs`, `Chain::new`: HKDF(salt = 0³², ikm = PQR key, info
  `Signal PQ Ratchet V1 Chain  Start`), 96 bytes; the A2B (initiator's sending) chain is bytes
  32..64 (`ced_for_direction`).
* `firstInput`: the send state of a fresh initiator session: version 4, counters 0, our ratchet
  public key, the sending chain key, SPQR sending chain, SPQR counter 0, epoch 1, both identity keys,
  and the two addresses (ours, theirs with the device id).
* `firstEnvelope`: `EstablishSeal.Reference.sealV1Typed PREKEY_MESSAGE` of
  `preKeySignalMessage varint5` (version 4, our registration id, the one-time / signed / Kyber
  prekey ids, the Kyber ciphertext, base key, our identity key) of the SignalMessage of
  `SpqrSend.canonical` on `firstInput` (the repository's reference send step, as in
  `SealSend.lean`).

PROVED (standard axioms only; no `sorry`, `native_decide`, `bv_decide`):

* `keys_value`: the key derivation of `establish-session` (`Establish.keys`) is
  `createChain ‖ handshake[32..] ‖ spqrChainStart` of `handshakeKeys`.
* `sendInput_first`: the send input `bundle-seal` reads from the record `establish-session` wrote
  is `firstInput`.
* `firstMessage_envelope`: when `establish-session` opened status 255, `bundle-seal` reads that
  session's `conversation` and `pending` outputs, and `bundle-seal` opened status 255, the opened
  envelope is `firstEnvelope` of the key agreements and ids `establish-session` was given and of
  `bundle-seal`'s own sealed-sender inputs.

NOT proved: that the agreements are X25519 of the right keys and `kemSecret`/`kemCiphertext` the
Kyber-1024 encapsulation (inputs here; the `kem-*` kernels are proved piecewise only,
`TlsMpc/MlKemFastProofs.lean`, not composed into `Signal.MlKem.encapsulate`), that the worker wires
`establish-session`'s outputs into `bundle-seal` (the hypotheses `hconversation`, `hpending`), the
SignalMessage against the Signal/SPQR specifications, and any cryptographic property.
-/
namespace TlsMpc.KernelSpecs.EstablishFirst
open Std.Tactic.BVDecide
open TlsMpc TlsMpc.Signal
open TlsMpc.KernelSpecs.SealValue (Byte)
open TlsMpc.KernelSpecs.SealValue.Reference (hkdfSha256)
open TlsMpc.KernelSpecs.EstablishSeal.Reference (sealV1Typed prekeyMessage preKeySignalMessage varint5 u32BE)

namespace Reference

def ascii (s : String) : List Byte := (TlsKdf.ascii s).map (BitVec.ofNat 8)

/-- `pqxdh_initiate` + `HandshakeKeys::derive`: root 32 ‖ chain 32 ‖ PQR key 32. `oneTime` is
empty without a one-time prekey. -/
def handshakeKeys (dh1 dh2 dh3 oneTime kemSecret : List Byte) : List Byte :=
  hkdfSha256 [] (List.replicate 32 0xFF ++ dh1 ++ dh2 ++ dh3 ++ oneTime ++ kemSecret)
    (ascii "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024") 96

/-- `RootKey::create_chain`: new root 32 ‖ chain key 32. -/
def createChain (root agreement : List Byte) : List Byte := hkdfSha256 root agreement (ascii "WhisperRatchet") 64

/-- SPQR `Chain::new`: next root 32 ‖ A2B 32 ‖ B2A 32. -/
def spqrChainStart (initialKey : List Byte) : List Byte :=
  hkdfSha256 (List.replicate 32 0) initialKey (ascii "Signal PQ Ratchet V1 Chain  Start") 96

/-- The initiator's sending chain key. -/
def sendingChain (dh1 dh2 dh3 oneTime kemSecret ratchetAgreement : List Byte) : List Byte :=
  (((createChain ((handshakeKeys dh1 dh2 dh3 oneTime kemSecret).take 32) ratchetAgreement).drop 32).take 32)

/-- The initiator's SPQR sending (A2B) chain key. -/
def pqSendingChain (dh1 dh2 dh3 oneTime kemSecret : List Byte) : List Byte :=
  ((spqrChainStart ((handshakeKeys dh1 dh2 dh3 oneTime kemSecret).drop 64)).drop 32).take 32

/-- The send input of the first message on a fresh initiator session. -/
def firstInput (ratchetPublic sendChain pqSend ourIdentity theirIdentity uuid : List Byte) (device : Byte)
    (localAddress : List Byte) (kind : Byte) (plaintext : List Byte) : SpqrSend.Input Byte :=
  { version := 4, counter := List.replicate 4 0, previous := List.replicate 4 0, ratchet := ratchetPublic,
    chainKey := sendChain, pqChainKey := pqSend, pqCounter := List.replicate 4 0,
    epoch := List.replicate 7 0 ++ [1], kind := kind,
    chunkIndex := [], chunkData := [], sender := ourIdentity, receiver := theirIdentity, plaintext := plaintext,
    addresses := Establish.addresses ByteAuth.concrete localAddress uuid device }

/-- **The first message to a new device**: sealed sender v1 (type PREKEY_MESSAGE) of the
PreKeySignalMessage carrying the first SignalMessage of the session PQXDH establishes. -/
def firstEnvelope (withOneTime : Bool) (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape) (size : Nat)
    (dh1 dh2 dh3 oneTime kemSecret ratchetAgreement kemCiphertext basePublic ratchetPublic ourIdentity
      theirIdentity certificate uuid device localRegistrationId oneTimePrekeyId signedPrekeyId kyberPrekeyId
      localAddress text ephemeralPublic sealSender ephemeralAgreement staticAgreement : List Byte) : List Byte :=
  let i := firstInput ratchetPublic (sendingChain dh1 dh2 dh3 oneTime kemSecret ratchetAgreement)
    (pqSendingChain dh1 dh2 dh3 oneTime kemSecret) ourIdentity theirIdentity uuid (device.getD 0 0) localAddress
    (text.getD 1 0) ((text.drop 2).take size)
  sealV1Typed prekeyMessage theirIdentity ephemeralPublic sealSender ephemeralAgreement staticAgreement certificate
    (preKeySignalMessage varint5 4 (u32BE localRegistrationId)
      (if withOneTime then some (u32BE oneTimePrekeyId) else none) (u32BE signedPrekeyId) (u32BE kyberPrekeyId)
      kemCiphertext basePublic ourIdentity (SpqrSend.canonical shape pqShape i).wire)

end Reference

open Reference

/-! ## The keys -/

theorem keys_value (dh1 dh2 dh3 oneTime kem ratchetAgreement : List Byte) :
    Establish.keys Sha256.concrete dh1 dh2 dh3 oneTime kem ratchetAgreement =
      createChain ((handshakeKeys dh1 dh2 dh3 oneTime kem).take 32) ratchetAgreement ++
        (handshakeKeys dh1 dh2 dh3 oneTime kem).drop 32 ++
        spqrChainStart ((handshakeKeys dh1 dh2 dh3 oneTime kem).drop 64) := by
  simp only [Establish.keys, Pqxdh.deriveCore, DhRatchet.materialFast_correct, DhRatchet.material,
    PrivateInitialSpqrV1.chainStart, TlsKdf.expandFast_correct, handshakeKeys, createChain, spqrChainStart,
    hkdfSha256, Pqxdh.secretInput, Pqxdh.label, TlsKdf.zeros]
  rfl

theorem keys_slices (dh1 dh2 dh3 oneTime kem ratchetAgreement : List Byte) :
    Establish.part (Establish.keys Sha256.concrete dh1 dh2 dh3 oneTime kem ratchetAgreement) 32 32 =
        sendingChain dh1 dh2 dh3 oneTime kem ratchetAgreement ∧
      Establish.part (Establish.keys Sha256.concrete dh1 dh2 dh3 oneTime kem ratchetAgreement) 160 32 =
        pqSendingChain dh1 dh2 dh3 oneTime kem := by
  have l1 : (createChain ((handshakeKeys dh1 dh2 dh3 oneTime kem).take 32) ratchetAgreement).length = 64 :=
    SealValue.hkdf_length _ _ _ _
  have l2 : ((handshakeKeys dh1 dh2 dh3 oneTime kem).drop 32).length = 64 := by
    simp only [List.length_drop, handshakeKeys, SealValue.hkdf_length]
  have l3 : (handshakeKeys dh1 dh2 dh3 oneTime kem).length = 96 := SealValue.hkdf_length _ _ _ _
  rw [keys_value]
  constructor
  · simp only [Establish.part, sendingChain, List.append_assoc]
    rw [List.drop_append_of_le_length (by omega),
      List.take_append_of_le_length (by simp only [List.length_drop, l1]; omega)]
  · simp only [Establish.part, pqSendingChain, List.append_assoc]
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append, l1, List.drop_append,
      List.drop_eq_nil_of_le (by omega), List.nil_append, l2]

/-! ## The records `establish-session` writes, read back -/

theorem sendInput_first (ratchetPublic sendChain pqSend ourIdentity theirIdentity uuid accessKey requestId device
      registration localAddress : List Byte) (kind : Byte) (plaintext : List Byte)
    (h1 : ratchetPublic.length = 32) (h2 : sendChain.length = 32) (h3 : pqSend.length = 32)
    (h4 : ourIdentity.length = 32) (h5 : theirIdentity.length = 32) (h6 : uuid.length = 16)
    (h7 : accessKey.length = 16) (h8 : requestId.length = 8) (h9 : device.length = 1) :
    Establish.sendInput ByteAuth.concrete
        (Establish.session ByteAuth.concrete 80 ratchetPublic sendChain pqSend ourIdentity theirIdentity)
        (Establish.metadata ByteAuth.concrete uuid accessKey requestId device registration) localAddress kind plaintext =
      firstInput ratchetPublic sendChain pqSend ourIdentity theirIdentity uuid (device.getD 0 0) localAddress kind
        plaintext := by
  obtain ⟨d, rfl⟩ : ∃ d, device = [d] := by
    match device, h9 with
    | [d], _ => exact ⟨d, rfl⟩
  have hdev : OpenResult.get ByteAuth.concrete
      (Establish.metadata ByteAuth.concrete uuid accessKey requestId [d] registration) 48 = d := by
    simp [OpenResult.get, Establish.metadata, Establish.zeros, List.getElem?_append_right, List.getElem?_append_left,
      h6, h7, h8]
  simp only [Establish.sendInput]
  rw [hdev]
  simp [firstInput, Establish.session, Establish.metadata, Establish.part, Establish.zeros,
    OpenResult.get, List.drop_append, List.take_append, h1, h2, h3, h4, h5, h6, h7, h8, ByteAuth.concrete,
    List.take_of_length_le, List.drop_eq_nil_of_le]

theorem record_slices (cert : Nat) (certificate session metadata : List Byte) (hc : certificate.length = cert)
    (hs : session.length = 262) (hm : metadata.length = 57) :
    ((certificate ++ session ++ metadata).drop cert).take 262 = session ∧
      ((certificate ++ session ++ metadata).drop (cert + 262)).take 57 = metadata ∧
      ((certificate ++ session ++ metadata).drop 0).take cert = certificate := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.append_assoc, List.drop_left' hc, List.take_left' hs]
  · rw [List.drop_left' (by simp only [List.length_append, hc, hs]), List.take_of_length_le (by omega)]
  · rw [List.drop_zero, List.append_assoc, List.take_left' hc]

theorem pending_slices (r o s k b c : List Byte) (hr : r.length = 4) (ho : o.length = 4) (hs : s.length = 4)
    (hk : k.length = 4) (hb : b.length = 32) :
    Establish.part (Establish.pending r o s k b c) 0 4 = r ∧ Establish.part (Establish.pending r o s k b c) 4 4 = o ∧
      Establish.part (Establish.pending r o s k b c) 8 4 = s ∧
      Establish.part (Establish.pending r o s k b c) 12 4 = k ∧
      Establish.part (Establish.pending r o s k b c) 16 32 = b ∧ (Establish.pending r o s k b c).drop 48 = c := by
  simp [Establish.pending, Establish.part, List.drop_append, List.take_append, hr, ho, hs, hk, hb,
    List.take_of_length_le, List.drop_eq_nil_of_le]

theorem session_length (ratchetPublic sendChain pqSend ourIdentity theirIdentity : List Byte)
    (h1 : ratchetPublic.length = 32) (h2 : sendChain.length = 32) (h3 : pqSend.length = 32)
    (h4 : ourIdentity.length = 32) (h5 : theirIdentity.length = 32) :
    (Establish.session ByteAuth.concrete 80 ratchetPublic sendChain pqSend ourIdentity theirIdentity).length = 262 := by
  simp [Establish.session, Establish.zeros, h1, h2, h3, h4, h5]

theorem metadata_length (uuid accessKey requestId device registration : List Byte) (h6 : uuid.length = 16)
    (h7 : accessKey.length = 16) (h8 : requestId.length = 8) (h9 : device.length = 1)
    (h10 : registration.length = 4) :
    (Establish.metadata ByteAuth.concrete uuid accessKey requestId device registration).length = 57 := by
  simp [Establish.metadata, Establish.zeros, h6, h7, h8, h9, h10]

theorem sendingChain_length (dh1 dh2 dh3 oneTime kem ratchetAgreement : List Byte) :
    (sendingChain dh1 dh2 dh3 oneTime kem ratchetAgreement).length = 32 := by
  simp only [sendingChain, createChain, List.length_take, List.length_drop, SealValue.hkdf_length]
  omega

theorem pqSendingChain_length (dh1 dh2 dh3 oneTime kem : List Byte) :
    (pqSendingChain dh1 dh2 dh3 oneTime kem).length = 32 := by
  simp only [pqSendingChain, spqrChainStart, List.length_take, List.length_drop, SealValue.hkdf_length]
  omega

/-- **The first message, on values**: `bundle-seal`'s reference envelope (`envelopeOf`) on the
records an accepted `establish-session` (`Establish.establish`, status 255) wrote is `firstEnvelope`
of the agreements, ids and keys it was given. -/
theorem envelopeOf_first (withOneTime : Bool) (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape)
    (size cert : Nat) (checks dh1 dh2 dh3 oneTime kem ratchetAgreement basePublic ratchetPublic senderPublic identityKey
      signedPrekey certificate uuid accessKey requestId device registration localRegistration oneTimeId signedId
      kyberId ciphertext localAddress text ephemeralPublic sealSender ephemeralAgreement staticAgreement : List Byte)
    (hc : certificate.length = cert) (h1 : ratchetPublic.length = 32) (h4 : senderPublic.length = 32)
    (h5 : identityKey.length = 32) (h6 : uuid.length = 16) (h7 : accessKey.length = 16) (h8 : requestId.length = 8)
    (h9 : device.length = 1) (h10 : registration.length = 4) (p1 : localRegistration.length = 4)
    (p2 : oneTimeId.length = 4) (p3 : signedId.length = 4) (p4 : kyberId.length = 4) (p5 : basePublic.length = 32)
    (hstatus : Establish.accepted ByteAuth.concrete checks
      ([dh1, dh2, dh3] ++ (if oneTime.length = 0 then [] else [oneTime]) ++ [ratchetAgreement]) = 255) :
    let out := Establish.establish Sha256.concrete ByteAuth.concrete 80 checks dh1 dh2 dh3 oneTime kem ratchetAgreement
      basePublic ratchetPublic senderPublic identityKey signedPrekey certificate uuid accessKey requestId device
      registration localRegistration oneTimeId signedId kyberId ciphertext
    let record := out.getD 1 []
    EstablishSeal.envelopeOf withOneTime shape pqShape size ((record.drop cert).take 262)
        ((record.drop (cert + 262)).take 57) (out.getD 2 []) ((record.drop 0).take cert) localAddress text
        ephemeralPublic sealSender ephemeralAgreement staticAgreement =
      firstEnvelope withOneTime shape pqShape size dh1 dh2 dh3 oneTime kem ratchetAgreement ciphertext basePublic
        ratchetPublic senderPublic identityKey certificate uuid device localRegistration oneTimeId signedId kyberId
        localAddress text ephemeralPublic sealSender ephemeralAgreement staticAgreement := by
  intro out record
  obtain ⟨ks1, ks2⟩ := keys_slices dh1 dh2 dh3 oneTime kem ratchetAgreement
  have hrecord : record = certificate ++ Establish.session ByteAuth.concrete 80 ratchetPublic
      (sendingChain dh1 dh2 dh3 oneTime kem ratchetAgreement) (pqSendingChain dh1 dh2 dh3 oneTime kem) senderPublic
      identityKey ++ Establish.metadata ByteAuth.concrete uuid accessKey requestId device registration := by
    simp only [record, out, Establish.establish, hstatus, List.getD_cons_succ, List.getD_cons_zero,
      ByteAuth.release_accept, ks1, ks2]
  have hpend : out.getD 2 [] = Establish.pending localRegistration oneTimeId signedId kyberId basePublic ciphertext := by
    simp only [out, Establish.establish, hstatus, List.getD_cons_succ, List.getD_cons_zero, ByteAuth.release_accept]
  obtain ⟨r1, r2, r3⟩ := record_slices cert certificate _ _ hc
    (session_length _ _ _ _ _ h1 (sendingChain_length _ _ _ _ _ _) (pqSendingChain_length _ _ _ _ _) h4 h5)
    (metadata_length _ _ _ _ _ h6 h7 h8 h9 h10)
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := pending_slices localRegistration oneTimeId signedId kyberId basePublic ciphertext
    p1 p2 p3 p4 p5
  rw [hrecord, hpend, r1, r2, r3]
  simp only [EstablishSeal.envelopeOf, EstablishSeal.inputOf, q1, q2, q3, q4, q5, q6]
  rw [sendInput_first _ _ _ _ _ _ _ _ _ _ _ _ _ h1 (sendingChain_length _ _ _ _ _ _) (pqSendingChain_length _ _ _ _ _)
    h4 h5 h6 h7 h8 h9]
  have hget : OpenResult.get ByteAuth.concrete text 1 = text.getD 1 0 := by
    simp only [OpenResult.get, List.getD_eq_getElem?_getD]
    rfl
  simp only [firstEnvelope, hget, Establish.part]
  rfl

/-! ## The kernels -/

open TlsMpc.HybridKernel (lookup) in
theorem sessionInputs_lengths (cert : Nat) (withOneTime : Bool) (assign : BVExpr.Assignment) :
    let len := fun name =>
      ((lookup (EstablishKernel.sessionInputs cert withOneTime) name).map (BVExpr.eval assign)).length
    len "certificate" = cert ∧ len "ratchetPublic" = 32 ∧ len "senderPublic" = 32 ∧ len "identityKey" = 32 ∧
      len "uuid" = 16 ∧ len "accessKey" = 16 ∧ len "requestId" = 8 ∧ len "deviceId" = 1 ∧
      len "registrationId" = 4 ∧ len "localRegistrationId" = 4 ∧ len "signedPrekeyId" = 4 ∧
      len "kyberPrekeyId" = 4 ∧ len "basePublic" = 32 ∧
      (withOneTime = true → len "oneTimePrekeyId" = 4) := by
  cases withOneTime <;>
    simp [lookup, HybridKernel.lookupFrom, EstablishKernel.sessionInputs, ByteCircuit.inputBytes,
      HybridKdf.wordBytes]

open TlsMpc.HybridKernel (lookup) in
/-- **The first message to a new device, end to end over the two kernels.** When
`establish-session` opened status 255, `bundle-seal`'s `conversation` and `pending` inputs are that
run's `conversation` and `pending` outputs (the worker's wiring, a hypothesis), and `bundle-seal`
opened status 255, the opened envelope is `firstEnvelope` of the key agreements (`dh1` … `dh4`,
`kemSecret`, `ratchetAgreement`), the Kyber ciphertext, the public keys and ids
`establish-session` was given, and `bundle-seal`'s own text and sealed-sender inputs. -/
theorem firstMessage_envelope (cert : Nat) (withOneTime : Bool)
    (content counterWidth previousWidth epochWidth indexWidth : Nat) (sessionAssign sealAssign : BVExpr.Assignment)
    (hbound : cert + content + counterWidth + previousWidth + epochWidth + indexWidth < 2 ^ 30)
    (established : (EstablishKernel.Kernel.values (EstablishKernel.establishSession cert withOneTime)
      sessionAssign).getD 0 [] = [255])
    (hconversation : (lookup (BundleKernel.sealInputs cert content) "conversation").map (BVExpr.eval sealAssign) =
      (EstablishKernel.Kernel.values (EstablishKernel.establishSession cert withOneTime) sessionAssign).getD 1 [])
    (hpending : (lookup (BundleKernel.sealInputs cert content) "pending").map (BVExpr.eval sealAssign) =
      (EstablishKernel.Kernel.values (EstablishKernel.establishSession cert withOneTime) sessionAssign).getD 2 [])
    (opened : (ReceiveKernel.values (BundleKernel.bundleSeal cert withOneTime content counterWidth previousWidth
      epochWidth indexWidth) sealAssign).getD 0 [] = [255]) :
    let est := fun name =>
      (lookup (EstablishKernel.sessionInputs cert withOneTime) name).map (BVExpr.eval sessionAssign)
    let sealIn := fun name => (lookup (BundleKernel.sealInputs cert content) name).map (BVExpr.eval sealAssign)
    (ReceiveKernel.values (BundleKernel.bundleSeal cert withOneTime content counterWidth previousWidth epochWidth
        indexWidth) sealAssign).getD 3 [] =
      firstEnvelope withOneTime ⟨counterWidth, previousWidth, true⟩ ⟨epochWidth, indexWidth, 0, false⟩ content
        (est "dh1") (est "dh2") (est "dh3") (est "dh4") (est "kemSecret") (est "ratchetAgreement")
        (est "kemCiphertext") (est "basePublic") (est "ratchetPublic") (est "senderPublic") (est "identityKey")
        (est "certificate") (est "uuid") (est "deviceId") (est "localRegistrationId") (est "oneTimePrekeyId")
        (est "signedPrekeyId") (est "kyberPrekeyId") (sealIn "localAddress") (sealIn "text")
        (sealIn "ephemeralPublic") (sealIn "senderPublic") (sealIn "ephemeralAgreement") (sealIn "staticAgreement") := by
  dsimp only
  have facts := EstablishSeal.bundleSeal_accepted cert withOneTime content counterWidth previousWidth epochWidth
    indexWidth sealAssign hbound opened
  simp only at facts
  rw [facts.2.2.2, hconversation, hpending]
  have hs := EstablishKernel.establishSession_spec cert withOneTime sessionAssign
  simp only at hs
  rw [hs] at established ⊢
  simp only [Establish.establish, List.getD_cons_zero, List.cons.injEq, and_true] at established
  obtain ⟨hc, h1, h4, h5, h6, h7, h8, h9, h10, p1, p3, p4, p5, p2⟩ :=
    sessionInputs_lengths cert withOneTime sessionAssign
  simp only at hc h1 h4 h5 h6 h7 h8 h9 h10 p1 p3 p4 p5 p2
  cases withOneTime
  · refine Eq.trans (envelopeOf_first _ _ _ _ cert
      _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _
      hc h1 h4 h5 h6 h7 h8 h9 h10 p1 (by simp [HybridKernel.zeros]) p3 p4 p5 established) ?_
    rfl
  · simp only [↓reduceIte] at established ⊢
    refine Eq.trans (envelopeOf_first _ _ _ _ cert
      _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _
      hc h1 h4 h5 h6 h7 h8 h9 h10 p1 (p2 rfl) p3 p4 p5 established) ?_
    rfl

#print axioms keys_value
#print axioms keys_slices
#print axioms sendInput_first
#print axioms envelopeOf_first
#print axioms firstMessage_envelope

end TlsMpc.KernelSpecs.EstablishFirst
