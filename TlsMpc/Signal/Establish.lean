import TlsMpc.Signal.Pqxdh
import TlsMpc.Signal.DhRatchet
import TlsMpc.Signal.PrivateInitialSpqrV1
import TlsMpc.Signal.SpqrSend
import TlsMpc.Signal.SealedSenderV1
import TlsMpc.Signal.XEdDsaBinding
import TlsMpc.TlsProviderGate

/-!
Sender-side session establishment from a recipient's prekey bundle (PQXDH),
as functions on bytes that are generic in the circuit operations. Instantiated
with the symbolic operations they are the bodies of the kernels in
`TlsMpc/EstablishKernels.lean`; instantiated with the concrete operations they
are the specification those kernels are proved against
(`TlsMpc/EstablishProofs.lean`).

Reference: libsignal v0.106.1 (`.deps/libsignal-v0.106.1/rust/protocol/src`).

* `session.rs`, `process_prekey_bundle`: trust check, then XEdDSA verification
  of the signed prekey over its serialization `05 ‖ key`, then of the Kyber
  prekey over `08 ‖ key`; a fresh base key pair; `initialize_alice_session`
  with `their_ratchet_key = their_signed_prekey`.
* `pqxdh.rs`, `pqxdh_initiate`: HKDF-SHA256 (no salt) over
  `0xFF×32 ‖ DH1 ‖ DH2 ‖ DH3 [‖ DH4] ‖ kemSecret` with info
  `WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024`, 96 bytes split into root
  key, chain key and the post-quantum ratchet key. This is `Pqxdh.deriveCore`.
* `ratchet.rs`, `initialize_initiator_session`: a fresh sending ratchet key;
  `root_key.create_chain(their_ratchet_key, sending_ratchet_private)` gives the
  session root key and the sending chain key (`ratchet/keys.rs`: HKDF with the
  root key as salt, info `WhisperRatchet`, 64 bytes); the PQXDH chain key
  becomes the receiver chain for the signed prekey; the post-quantum ratchet
  starts in direction A2B from the third key.
* SPQR `src/chain.rs`, `Chain::new`: HKDF with a 32-byte zero salt and info
  `Signal PQ Ratchet V1 Chain  Start`, 96 bytes: next root, A2B chain, B2A chain.
* `session_management.rs`, `message_encrypt`: while the session is
  unacknowledged, the SignalMessage carries the two addresses and is wrapped in
  a PreKeySignalMessage (`protocol.rs`, `PreKeySignalMessage::new`; fields in
  `proto/wire.proto`). In sealed sender its type is `PREKEY_MESSAGE = 1`
  (`proto/sealed_sender.proto`).
* `rust/core/src/curve.rs`, `calculate_agreement`: an all-zero X25519 result is
  an error. Every agreement used here is therefore required to be nonzero.

Two deliberate differences from what libsignal itself would send, both chosen
so that nothing about the contact shows in a public length:

* The four `uint32` fields of the PreKeySignalMessage are written as five-byte
  varints (zero-padded with continuation bytes). The decoder libsignal uses
  (`prost` 0.14.4, `encoding/varint.rs`) accepts them; the canonical encoding
  would make the envelope length depend on the contact's prekey ids.
* The post-quantum ratchet message carries no key-header chunk (payload kind 0)
  in epoch 1, exactly like the established send path. A libsignal sender would
  start sending its ML-KEM-768 header in chunks here. The SPQR receiver keeps
  its state on such a message and derives the same epoch-0 chain key
  (`src/v1/chunked/states.rs`, `NoHeaderReceived`, equal epoch, payload not a
  header), so the message decrypts, but the post-quantum ratchet does not
  advance until that is implemented.

Proved in this file: every definition commutes with a homomorphism of the
operations (the step from circuit to values), and the key derivation equals the
explicit HMAC recurrence. Not proved: agreement with the Rust code, which is
only tested (see `check_establish_kernels.py`), and any cryptographic property.
-/
namespace TlsMpc.Signal.Establish
open Std.Tactic.BVDecide

def part (xs : List B) (offset count : Nat) : List B := (xs.drop offset).take count
def zeros (a : ByteAuth.Ops B) (count : Nat) : List B := List.replicate count (a.const 0)

/-! ### Signed-prekey verification (XEdDSA), Boolean parts

Field parts (`TlsMpc/EstablishField.lean`): `recover` turns the identity key's
Montgomery `u` into `valid, x, y`; `check` computes `[s]B − [h]A`. -/

/-- `flip` (one byte, 0 or 1) followed by the challenge `h` (32 bytes, little
endian, reduced modulo the group order) for a signature over `tag ‖ key`. -/
def challenge (a : ByteAuth.Ops B) (h : XEdDsaSha512.Ops B H) (r : XEdDsaScalar.Ops B R)
    (tag : Nat) (signature x y key : List B) : List B :=
  XEdDsaBinding.prepare a h r signature x y (a.const tag :: key)

/-- 255 exactly when the identity key decoded to a curve point and the
recomputed point compresses to the signature's `R` (with `s < 2^253`). -/
def signatureMask (a : ByteAuth.Ops B) (signature validity rx ry : List B) : B :=
  a.and (ByteAuth.equalMask a validity (a.const 1 :: List.replicate 31 (a.const 0)))
    (XEdDsa.matchR a signature rx ry)

theorem signatureMask_finish (a : ByteAuth.Ops B) (signature validity rx ry : List B) :
    XEdDsaBinding.finish a signature validity rx ry = [signatureMask a signature validity rx ry] := rfl

/-- Both bundle signatures. -/
def verified (a : ByteAuth.Ops B) (ecSignature pqSignature validity ecRx ecRy pqRx pqRy : List B) : B :=
  a.and (signatureMask a ecSignature validity ecRx ecRy) (signatureMask a pqSignature validity pqRx pqRy)

/-! ### Keys -/

/-- root 32 ‖ sending chain 32 ‖ receiving chain 32 ‖ post-quantum ratchet key 32 ‖
post-quantum next root 32 ‖ post-quantum sending chain 32 ‖ post-quantum receiving chain 32.

`oneTime` is empty when the bundle has no one-time prekey. -/
def keys (s : Sha256.Ops B W) (dh1 dh2 dh3 oneTime kem ratchetAgreement : List B) : List B :=
  let handshake := Pqxdh.deriveCore s dh1 dh2 dh3 oneTime kem
  DhRatchet.materialFast s (handshake.take 32) ratchetAgreement ++ handshake.drop 32 ++
    PrivateInitialSpqrV1.chainStart s (handshake.drop 64)

/-- All checks are 255 and no agreement is all zero. -/
def accepted (a : ByteAuth.Ops B) (checks : List B) (agreements : List (List B)) : B :=
  agreements.foldl (fun mask agreement => a.and mask (DhRatchet.agreementMask a agreement))
    (checks.foldl (fun mask check => a.and mask (ByteAuth.eqMask a check (a.const 255))) (a.const 255))

/-! ### Records

The session block is the one the established send kernels read
(`HybridKernel.signalSealFixed`): version 1, counter 4, previous counter 4,
sending ratchet public key 32, sending chain key 32, post-quantum chain key 32,
post-quantum counter 4, post-quantum epoch 8, kind 1, own identity key 32,
recipient identity key 32, plaintext buffer. -/

def session (a : ByteAuth.Ops B) (size : Nat) (ratchetPublic sendChain pqSend sender receiver : List B) : List B :=
  [a.const 4] ++ zeros a 8 ++ ratchetPublic ++ sendChain ++ pqSend ++ zeros a 4 ++
    (zeros a 7 ++ [a.const 1]) ++ [a.const 0] ++ sender ++ receiver ++ zeros a size

/-- Recipient UUID 16, access key 16, timestamp 8, request id 8, device 1,
registration id 4, mask 4. -/
def metadata (a : ByteAuth.Ops B) (uuid accessKey requestId device registration : List B) : List B :=
  uuid ++ accessKey ++ zeros a 8 ++ requestId ++ device ++ registration ++ zeros a 4

/-- What every message needs until the recipient answers: own registration id 4,
one-time prekey id 4 (zero if none), signed prekey id 4, Kyber prekey id 4, base
public key 32, KEM ciphertext 1568. -/
def pending (localRegistration oneTimeId signedId kyberId basePublic ciphertext : List B) : List B :=
  localRegistration ++ oneTimeId ++ signedId ++ kyberId ++ basePublic ++ ciphertext

/-- The four results of establishment: status (1), conversation record, pending
record (1616), and what a later receive path needs (192): root 32, receiving
chain 32, the recipient's ratchet key (its signed prekey) 32, post-quantum
ratchet key 32, post-quantum next root 32, post-quantum receiving chain 32.
Everything is zero unless the status is 255. -/
def establish (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (size : Nat) (checks : List B)
    (dh1 dh2 dh3 oneTime kem ratchetAgreement basePublic ratchetPublic senderPublic identityKey signedPrekey
      certificate uuid accessKey requestId device registration localRegistration oneTimeId signedId kyberId
      ciphertext : List B) : List (List B) :=
  let status := accepted a checks
    ([dh1, dh2, dh3] ++ (if oneTime.length = 0 then [] else [oneTime]) ++ [ratchetAgreement])
  let k := keys s dh1 dh2 dh3 oneTime kem ratchetAgreement
  let record := certificate ++ session a size ratchetPublic (part k 32 32) (part k 160 32) senderPublic identityKey ++
    metadata a uuid accessKey requestId device registration
  [[status], ByteAuth.release a status record,
    ByteAuth.release a status (pending localRegistration oneTimeId signedId kyberId basePublic ciphertext),
    ByteAuth.release a status (part k 0 32 ++ part k 64 32 ++ signedPrekey ++ part k 96 64 ++ part k 192 32)]

/-! ### First message -/

/-- A `uint32` field as a one-byte key and a five-byte varint. -/
def idField (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (tag : Nat) (id : List B) : List B :=
  a.const tag :: Varint.encode s a (Varint.pack s a id) 5

/-- PreKeySignalMessage: version byte, then fields 1 (one-time prekey id, if
any), 2 (base key), 3 (identity key), 4 (message), 5 (registration id),
6 (signed prekey id), 7 (Kyber prekey id), 8 (Kyber ciphertext). -/
def preKeyMessage (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (withOneTime : Bool) (version : B)
    (pending identity signal : List B) : List B :=
  [Serialization.versionByte a version] ++
    (if withOneTime then idField s a 8 (part pending 4 4) else []) ++
    Serialization.bytesField a 18 (a.const 5 :: part pending 16 32) ++
    Serialization.bytesField a 26 (a.const 5 :: identity) ++
    Serialization.bytesField a 34 signal ++
    idField s a 40 (part pending 0 4) ++ idField s a 48 (part pending 8 4) ++ idField s a 56 (part pending 12 4) ++
    Serialization.bytesField a 66 (a.const 8 :: pending.drop 48)

/-- Sender then recipient, each as service-id kind (0: ACI), UUID, device.
`localAddress` is the client's own UUID and device (17 bytes). -/
def addresses (a : ByteAuth.Ops B) (localAddress uuid : List B) (device : B) : List B :=
  a.const 0 :: (localAddress ++ [a.const 0] ++ uuid ++ [device])

def usmc (a : ByteAuth.Ops B) (kind : Nat) (certificate inner : List B) : List B :=
  [a.const 8, a.const kind] ++ Serialization.bytesField a 18 certificate ++ Serialization.bytesField a 26 inner

/-- `SealedSenderV1.sealCore` with the message type as a parameter. -/
def sealedSender (o : Aes.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (kind : Nat)
    (recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner : List B) : List B :=
  let recipient := a.const 5 :: recipientPublic
  let ephemeral := a.const 5 :: ephemeralPublic
  let sender := a.const 5 :: senderPublic
  let first := SealedSenderV1.material s
    ((TlsKdf.ascii "UnidentifiedDelivery").map s.byteConst ++ recipient ++ ephemeral) ephemeralDh
  let encryptedStatic := SealedSenderV1.encrypt o s ((first.drop 32).take 32) ((first.drop 64).take 32) sender
  let second := SealedSenderV1.material s (first.take 32 ++ encryptedStatic) staticDh
  let encryptedMessage := SealedSenderV1.encrypt o s ((second.drop 32).take 32) ((second.drop 64).take 32)
    (usmc a kind certificate inner)
  a.const 17 :: (Serialization.bytesField a 10 ephemeral ++
    Serialization.bytesField a 18 encryptedStatic ++ Serialization.bytesField a 26 encryptedMessage)

theorem sealedSender_message (o : Aes.Ops B) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner : List B) :
    sealedSender o s a 2 recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner =
      SealedSenderV1.sealCore o s a recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner :=
  rfl

/-- The send input read from a session block, with the message's kind and
plaintext and both addresses. -/
def sendInput (a : ByteAuth.Ops B) (session metadata localAddress : List B) (kind : B) (plaintext : List B) :
    SpqrSend.Input B :=
  { version := OpenResult.get a session 0, counter := part session 1 4, previous := part session 5 4,
    ratchet := part session 9 32, chainKey := part session 41 32, pqChainKey := part session 73 32,
    pqCounter := part session 105 4, epoch := part session 109 8, kind := kind, chunkIndex := [], chunkData := [],
    sender := part session 118 32, receiver := part session 150 32, plaintext := plaintext,
    addresses := addresses a localAddress (metadata.take 16) (OpenResult.get a metadata 48) }

/-- One message on an unacknowledged session: status (1), next session block,
sealed-sender envelope (zero unless the status is 255). `text` is the output of
the text builder: validity, kind, plaintext. -/
def sealMessage (o : Aes.Ops B) (v : Varint64.Ops B V) (s : Sha256.Ops B W) (a : ByteAuth.Ops B) (withOneTime : Bool)
    (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape) (size : Nat)
    (session metadata pending certificate localAddress text
      ephemeralPublic senderPublic ephemeralDh staticDh : List B) : List (List B) :=
  let kind := OpenResult.get a text 1
  let plaintext := part text 2 size
  let i := sendInput a session metadata localAddress kind plaintext
  let p := SpqrSend.prepare o v s a shape pqShape i
  let wire := preKeyMessage s a withOneTime i.version pending i.sender p.wire
  let envelope := sealedSender o s a 1 i.receiver ephemeralPublic senderPublic ephemeralDh staticDh certificate wire
  let bound := a.and (SealedSenderV1.agreementMask a ephemeralDh staticDh) (ByteAuth.equalMask a senderPublic i.sender)
  let status := TlsProviderGate.gate a
    (TlsProviderGate.gate a (SpqrSend.acceptedMask v s a shape pqShape i) bound) (OpenResult.get a text 0)
  let choose := fun next old => ChainSend.selectState a status next old
  [[status],
    session.take 1 ++ choose p.nextCounter i.counter ++ part session 5 36 ++ choose p.nextChainKey i.chainKey ++
      choose p.nextPqChainKey i.pqChainKey ++ choose p.nextPqCounter i.pqCounter ++ part session 109 8 ++ [kind] ++
      part session 118 64 ++ plaintext,
    ByteAuth.release a status envelope]

/-! ### From circuit to values -/

section Refinement
variable {o : Aes.Ops B} {o' : Aes.Ops B'} {v : Varint64.Ops B V} {v' : Varint64.Ops B' V'}
  {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fw : W → W'} {fv : V → V'}

theorem part_map (xs : List B) (offset count : Nat) : (part xs offset count).map f = part (xs.map f) offset count := by
  simp only [part, List.map_take, List.map_drop]

theorem zeros_map (ha : ByteAuth.Hom a a' f) (count : Nat) : (zeros a count).map f = zeros a' count := by
  simp only [zeros, List.map_replicate, ha.const]

theorem challenge_map {h : XEdDsaSha512.Ops B H} {h' : XEdDsaSha512.Ops B' H'} {r : XEdDsaScalar.Ops B R}
    {r' : XEdDsaScalar.Ops B' R'} {fh : H → H'} {fr : R → R'} (ha : ByteAuth.Hom a a' f)
    (hh : XEdDsaSha512.Hom h h' f fh) (hr : XEdDsaScalar.Hom r r' f fr) (tag : Nat) (signature x y key : List B) :
    (challenge a h r tag signature x y key).map f =
      challenge a' h' r' tag (signature.map f) (x.map f) (y.map f) (key.map f) := by
  simp only [challenge, XEdDsaBinding.prepare_map ha hh hr, List.map_cons, ha.const]

theorem signatureMask_map (ha : ByteAuth.Hom a a' f) (signature validity rx ry : List B) :
    f (signatureMask a signature validity rx ry) =
      signatureMask a' (signature.map f) (validity.map f) (rx.map f) (ry.map f) := by
  simp only [signatureMask, ha.and, ByteAuth.equalMask_map ha, XEdDsa.matchR_map ha, List.map_cons,
    List.map_replicate, ha.const]

theorem verified_map (ha : ByteAuth.Hom a a' f) (ecSignature pqSignature validity ecRx ecRy pqRx pqRy : List B) :
    f (verified a ecSignature pqSignature validity ecRx ecRy pqRx pqRy) =
      verified a' (ecSignature.map f) (pqSignature.map f) (validity.map f) (ecRx.map f) (ecRy.map f)
        (pqRx.map f) (pqRy.map f) := by
  simp only [verified, ha.and, signatureMask_map ha]

theorem chainStart_map (hs : Sha256.Hom s s' f fw) (auth : List B) :
    (PrivateInitialSpqrV1.chainStart s auth).map f = PrivateInitialSpqrV1.chainStart s' (auth.map f) := by
  simp only [PrivateInitialSpqrV1.chainStart, TlsKdf.expandFast_correct, TlsKdf.expandCore_map hs,
    TlsKdf.extract_map hs, TlsKdf.zeros, List.map_replicate, List.map_map, Function.comp_def, hs.byteConst]

theorem keys_map (hs : Sha256.Hom s s' f fw) (dh1 dh2 dh3 oneTime kem ratchetAgreement : List B) :
    (keys s dh1 dh2 dh3 oneTime kem ratchetAgreement).map f =
      keys s' (dh1.map f) (dh2.map f) (dh3.map f) (oneTime.map f) (kem.map f) (ratchetAgreement.map f) := by
  simp only [keys, List.map_append, DhRatchet.materialFast_map hs, List.map_take, List.map_drop,
    Pqxdh.deriveCore_map hs, chainStart_map hs]

theorem accepted_map (ha : ByteAuth.Hom a a' f) (checks : List B) (agreements : List (List B)) :
    f (accepted a checks agreements) = accepted a' (checks.map f) (agreements.map (List.map f)) := by
  have first (xs : List B) (z : B) :
      f (xs.foldl (fun mask check => a.and mask (ByteAuth.eqMask a check (a.const 255))) z) =
        (xs.map f).foldl (fun mask check => a'.and mask (ByteAuth.eqMask a' check (a'.const 255))) (f z) := by
    induction xs generalizing z with
    | nil => rfl
    | cons x xs ih => simp only [List.foldl_cons, List.map_cons, ih, ha.and, ByteAuth.eqMask_map ha, ha.const]
  have second (xs : List (List B)) (z : B) :
      f (xs.foldl (fun mask agreement => a.and mask (DhRatchet.agreementMask a agreement)) z) =
        (xs.map (List.map f)).foldl (fun mask agreement => a'.and mask (DhRatchet.agreementMask a' agreement)) (f z) := by
    induction xs generalizing z with
    | nil => rfl
    | cons x xs ih => simp only [List.foldl_cons, List.map_cons, ih, ha.and, DhRatchet.agreementMask_map ha]
  simp only [accepted, second, first, ha.const]

theorem session_map (ha : ByteAuth.Hom a a' f) (size : Nat) (ratchetPublic sendChain pqSend sender receiver : List B) :
    (session a size ratchetPublic sendChain pqSend sender receiver).map f =
      session a' size (ratchetPublic.map f) (sendChain.map f) (pqSend.map f) (sender.map f) (receiver.map f) := by
  simp only [session, List.map_append, List.map_cons, List.map_nil, zeros_map ha, ha.const]

theorem metadata_map (ha : ByteAuth.Hom a a' f) (uuid accessKey requestId device registration : List B) :
    (metadata a uuid accessKey requestId device registration).map f =
      metadata a' (uuid.map f) (accessKey.map f) (requestId.map f) (device.map f) (registration.map f) := by
  simp only [metadata, List.map_append, zeros_map ha]

theorem pending_map (localRegistration oneTimeId signedId kyberId basePublic ciphertext : List B) :
    (pending localRegistration oneTimeId signedId kyberId basePublic ciphertext).map f =
      pending (localRegistration.map f) (oneTimeId.map f) (signedId.map f) (kyberId.map f) (basePublic.map f)
        (ciphertext.map f) := by
  simp only [pending, List.map_append]

theorem establish_map (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f) (size : Nat) (checks : List B)
    (dh1 dh2 dh3 oneTime kem ratchetAgreement basePublic ratchetPublic senderPublic identityKey signedPrekey
      certificate uuid accessKey requestId device registration localRegistration oneTimeId signedId kyberId
      ciphertext : List B) :
    (establish s a size checks dh1 dh2 dh3 oneTime kem ratchetAgreement basePublic ratchetPublic senderPublic
      identityKey signedPrekey certificate uuid accessKey requestId device registration localRegistration
      oneTimeId signedId kyberId ciphertext).map (List.map f) =
    establish s' a' size (checks.map f) (dh1.map f) (dh2.map f) (dh3.map f) (oneTime.map f) (kem.map f)
      (ratchetAgreement.map f) (basePublic.map f) (ratchetPublic.map f) (senderPublic.map f) (identityKey.map f)
      (signedPrekey.map f) (certificate.map f) (uuid.map f) (accessKey.map f) (requestId.map f) (device.map f)
      (registration.map f) (localRegistration.map f) (oneTimeId.map f) (signedId.map f) (kyberId.map f)
      (ciphertext.map f) := by
  simp only [establish, List.length_map]
  split <;> simp only [List.map_cons, List.map_nil, List.map_append, ByteAuth.release_map ha, accepted_map ha,
    session_map ha, metadata_map ha, pending_map, part_map, keys_map hs, List.append_nil]

theorem idField_map (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f) (tag : Nat) (id : List B) :
    (idField s a tag id).map f = idField s' a' tag (id.map f) := by
  simp only [idField, List.map_cons, ha.const, Varint.encode_map hs ha, Varint.pack_map hs ha]

theorem preKeyMessage_map (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f) (withOneTime : Bool) (version : B)
    (pending identity signal : List B) :
    (preKeyMessage s a withOneTime version pending identity signal).map f =
      preKeyMessage s' a' withOneTime (f version) (pending.map f) (identity.map f) (signal.map f) := by
  cases withOneTime <;>
    simp only [preKeyMessage, List.map_append, List.map_cons, List.map_nil, Serialization.versionByte_map ha,
      Serialization.bytesField_map ha, idField_map hs ha, part_map, ha.const, List.map_drop, Bool.false_eq_true,
      if_false, if_true]

theorem addresses_map (ha : ByteAuth.Hom a a' f) (localAddress uuid : List B) (device : B) :
    (addresses a localAddress uuid device).map f = addresses a' (localAddress.map f) (uuid.map f) (f device) := by
  simp only [addresses, List.map_cons, List.map_append, List.map_nil, ha.const]

theorem usmc_map (ha : ByteAuth.Hom a a' f) (kind : Nat) (certificate inner : List B) :
    (usmc a kind certificate inner).map f = usmc a' kind (certificate.map f) (inner.map f) := by
  simp only [usmc, List.map_append, List.map_cons, List.map_nil, Serialization.bytesField_map ha, ha.const]

theorem sealedSender_map (ho : Aes.Hom o o' f) (hs : Sha256.Hom s s' f fw) (ha : ByteAuth.Hom a a' f) (kind : Nat)
    (recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner : List B) :
    (sealedSender o s a kind recipientPublic ephemeralPublic senderPublic ephemeralDh staticDh certificate inner).map f =
      sealedSender o' s' a' kind (recipientPublic.map f) (ephemeralPublic.map f) (senderPublic.map f)
        (ephemeralDh.map f) (staticDh.map f) (certificate.map f) (inner.map f) := by
  simp only [sealedSender, List.map_cons, List.map_append, ha.const, Serialization.bytesField_map ha,
    SealedSenderV1.encrypt_map ho hs, List.map_take, List.map_drop, SealedSenderV1.material_map hs, usmc_map ha,
    List.map_map, Function.comp_def, hs.byteConst]

theorem sendInput_map (ha : ByteAuth.Hom a a' f) (session metadata localAddress : List B) (kind : B)
    (plaintext : List B) :
    (sendInput a session metadata localAddress kind plaintext).map f =
      sendInput a' (session.map f) (metadata.map f) (localAddress.map f) (f kind) (plaintext.map f) := by
  simp only [sendInput, SpqrSend.Input.map, OpenResult.get_map ha, part_map, addresses_map ha, List.map_take,
    List.map_nil]

theorem sealMessage_map (ho : Aes.Hom o o' f) (hv : Varint64.Hom v v' f fv) (hs : Sha256.Hom s s' f fw)
    (ha : ByteAuth.Hom a a' f) (withOneTime : Bool) (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape)
    (size : Nat) (session metadata pending certificate localAddress text
      ephemeralPublic senderPublic ephemeralDh staticDh : List B) :
    (sealMessage o v s a withOneTime shape pqShape size session metadata pending certificate localAddress text
      ephemeralPublic senderPublic ephemeralDh staticDh).map (List.map f) =
    sealMessage o' v' s' a' withOneTime shape pqShape size (session.map f) (metadata.map f) (pending.map f)
      (certificate.map f) (localAddress.map f) (text.map f) (ephemeralPublic.map f) (senderPublic.map f)
      (ephemeralDh.map f) (staticDh.map f) := by
  have hp := SpqrSend.prepare_map ho hv hs ha shape pqShape
    (sendInput a session metadata localAddress (OpenResult.get a text 1) (part text 2 size))
  rw [sendInput_map ha] at hp
  have hk := congrArg SpqrSend.Prepared.nextChainKey hp
  have hc := congrArg SpqrSend.Prepared.nextCounter hp
  have hpk := congrArg SpqrSend.Prepared.nextPqChainKey hp
  have hpc := congrArg SpqrSend.Prepared.nextPqCounter hp
  have hw := congrArg SpqrSend.Prepared.wire hp
  have hm := SpqrSend.acceptedMask_map hv hs ha shape pqShape
    (sendInput a session metadata localAddress (OpenResult.get a text 1) (part text 2 size))
  rw [sendInput_map ha] at hm
  simp only [SpqrSend.Prepared.map, OpenResult.get_map ha, part_map] at hk hc hpk hpc hw hm
  simp only [sealMessage, List.map_cons, List.map_nil, List.map_append, List.map_take, ChainSend.selectState_map ha,
    ByteAuth.release_map ha, TlsProviderGate.gate_map ha, ha.and, SealedSenderV1.agreementMask_map ha,
    ByteAuth.equalMask_map ha, sealedSender_map ho hs ha, preKeyMessage_map hs ha, OpenResult.get_map ha, part_map,
    hk, hc, hpk, hpc, hw, hm]
  simp only [sendInput, part_map, OpenResult.get_map ha]

end Refinement

/-! ### The key derivation as explicit HMAC steps -/

/-- The session keys, written out: PQXDH (`Pqxdh.specification`), then the
first sending ratchet step, then the start of the post-quantum chain. -/
def keysSpecification (dh1 dh2 dh3 oneTime kem ratchetAgreement : List (BitVec 8)) : List (BitVec 8) :=
  let handshake := Pqxdh.specification dh1 dh2 dh3 oneTime kem
  DhRatchet.material Sha256.concrete (handshake.take 32) ratchetAgreement ++ handshake.drop 32 ++
    TlsKdf.expandCore Sha256.concrete (TlsKdf.extract Sha256.concrete (List.replicate 32 0) (handshake.drop 64))
      ((TlsKdf.ascii "Signal PQ Ratchet V1 Chain  Start").map (BitVec.ofNat 8)) 96

theorem keys_specification (dh1 dh2 dh3 oneTime kem ratchetAgreement : List (BitVec 8)) :
    keys Sha256.concrete dh1 dh2 dh3 oneTime kem ratchetAgreement =
      keysSpecification dh1 dh2 dh3 oneTime kem ratchetAgreement := by
  simp only [keys, keysSpecification, Pqxdh.deriveCore_specification, DhRatchet.materialFast_correct,
    PrivateInitialSpqrV1.chainStart, TlsKdf.expandFast_correct, TlsKdf.zeros]
  rfl

#print axioms establish_map
#print axioms sealMessage_map
#print axioms keys_specification

end TlsMpc.Signal.Establish
