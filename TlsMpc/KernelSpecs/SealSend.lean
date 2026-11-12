import TlsMpc.KernelSpecs.SealValue

/-!
# What `signal-seal-official` / `signal-seal-built` compute (T7(b), parts 2 and 3)

New file; it changes no definition and no emitter imports it.

`TlsMpc/KernelSpecs/SealFixed.lean` proves that the kernel computes `sealFixedWith` (its own
composition of `SpqrSend.acceptedMask`, `SpqrSend.prepare`, `SealedSenderV1.boundSeal`,
`TlsProviderGate.gate` and `ChainSend.selectState`) on concrete values, through
`Sha256Ripple.evaluationHom` for the kernel's SHA-256 instance. This file evaluates that
composition, so the kernel's outputs are stated in terms of the references:

* the Signal send step `SpqrSend.canonical` (textbook symmetric ratchet `Symmetric.derive`, SPQR
  chain `SpqrChain.material`, `Send.message`: AES-256-CBC, the SignalMessage protobuf and its MAC)
  and its acceptance predicate `SpqrSend.accepted`;
* sealed sender v1, `SealValue.Reference.sealV1` (TlsMpc/KernelSpecs/SealValue.lean), and the
  sealed-sender checks `Reference.boundAccepted`.

PROVED (standard axioms only; no `sorry`, `native_decide`, `bv_decide`):

* `sealFixedWith_value`: on accepted inputs (the SPQR/chain send accepts, both agreements nonzero,
  the computed sender key is the stored one, the built text's validity byte is 255) the outputs
  are `[255]`, the record with the advanced counter, chain key, SPQR chain key and SPQR counter,
  the timestamp, and the envelope `sealV1 receiver ephemeralPublic senderPublic … certificate wire`
  where `wire` is the Signal message of `SpqrSend.canonical`; otherwise `[0]`, the record with the
  OLD ratchet state, the timestamp and an all-zero envelope of the same length.
* `signalSeal_value`: the same for the deployed kernels on every input assignment (both
  `official` values), combining `SealFixed.signalSealBuilt_spec`.
* `message_length_le`, `canonical_wire_length_le`: the Signal message is at most the plaintext
  plus the public widths plus 150 bytes (used to discharge the protobuf varint bound).

Observed (not a defect of the proof, reported): on refusal the stored record is NOT byte-for-byte
the old one: the ratchet state (counter, chain key, SPQR chain key, SPQR counter) is the old one,
but the staged block always takes the built text's kind byte (record byte `cert + 117`) and its
first 80 content bytes (`cert + 182 …`), refused or not (`stagedOf`; HybridKernels.lean:446).
-/
namespace TlsMpc.KernelSpecs.SealSend
open Std.Tactic.BVDecide
open TlsMpc TlsMpc.Signal
open TlsMpc.KernelSpecs.SealFixed (stagedOf inputOf sealFixedWith contentBytes sealInputs)
open TlsMpc.KernelSpecs.SealValue (Byte)
open TlsMpc.KernelSpecs.SealValue.Reference

/-! ## Lengths -/

theorem encryptExpanded_length_le (expanded block : List Byte) :
    (Aes.encryptExpanded Aes.concrete 14 expanded block).length ≤ 16 := by
  simp only [Aes.encryptExpanded, Aes.addRoundKey, List.length_zipWith, List.length_take]
  omega

theorem encryptBlocks_length_le (expanded : List Byte) (n : Nat) :
    ∀ iv plain, (Cbc.encryptBlocks Aes.concrete expanded n iv plain).length ≤ 16 * n := by
  induction n with
  | zero => intro iv plain; simp [Cbc.encryptBlocks]
  | succ n ih =>
      intro iv plain
      simp only [Cbc.encryptBlocks, List.length_append]
      have := encryptExpanded_length_le expanded
        (Aes.addRoundKey Aes.concrete (plain.take 16) iv)
      have := ih (Aes.encryptExpanded Aes.concrete 14 expanded (Aes.addRoundKey Aes.concrete (plain.take 16) iv))
        (plain.drop 16)
      omega

theorem cbc_length_le (key iv plain : List Byte) :
    (Cbc.encryptCore Aes.concrete key iv plain).length ≤ plain.length + 16 := by
  have := encryptBlocks_length_le (Aes.expandKey Aes.concrete 8 14 key) (plain.length / 16 + 1) iv
    (Cbc.pad Aes.concrete plain)
  simp only [Cbc.encryptCore]
  omega

theorem message_length_le (shape : Serialization.Shape) (version : Byte)
    (counter previous ratchet cipherKey iv macKey sender receiver plaintext pq addresses : List Byte) :
    (Send.message Aes.concrete Sha256.concrete ByteAuth.concrete shape version counter previous ratchet
      cipherKey iv macKey sender receiver plaintext pq addresses).length ≤
      ratchet.length + plaintext.length + pq.length + addresses.length + shape.counterWidth +
        shape.previousWidth + 100 := by
  simp only [Send.message, Serialization.content, List.length_append, List.length_cons, List.length_nil,
    MessageMac.tag_length, Varint.encode_length]
  have h1 := SealValue.bytesField_length_le 10 (ByteAuth.concrete.const 5 :: ratchet)
  have h2 := SealValue.bytesField_length_le 34 (Cbc.encryptCore Aes.concrete cipherKey iv plaintext)
  have h3 := cbc_length_le cipherKey iv plaintext
  have h4 : (Serialization.pqField ByteAuth.concrete pq).length ≤ pq.length + 11 := by
    simp only [Serialization.pqField]
    split
    · simp
    · exact SealValue.bytesField_length_le 42 pq
  have h5 : (Serialization.addressField ByteAuth.concrete shape addresses).length ≤ addresses.length + 11 := by
    simp only [Serialization.addressField]
    split
    · exact SealValue.bytesField_length_le 50 addresses
    · simp
  simp only [List.length_cons] at h1
  omega

theorem canonical_wire_length_le (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape)
    (i : SpqrSend.Input Byte) (hratchet : i.ratchet.length ≤ 32) (haddresses : i.addresses = [])
    (hchunk : pqShape.hasChunk = false) :
    (SpqrSend.canonical shape pqShape i).wire.length ≤
      i.plaintext.length + shape.counterWidth + shape.previousWidth + pqShape.epochWidth +
        pqShape.indexWidth + 150 := by
  simp only [SpqrSend.canonical]
  have := message_length_le shape i.version i.counter i.previous i.ratchet
    (Symmetric.derive Sha256.concrete i.chainKey
      ((SpqrChain.material Sha256.concrete ByteAuth.concrete i.pqChainKey i.pqCounter).drop 32)).material.cipherKey
    (Symmetric.derive Sha256.concrete i.chainKey
      ((SpqrChain.material Sha256.concrete ByteAuth.concrete i.pqChainKey i.pqCounter).drop 32)).material.iv
    (Symmetric.derive Sha256.concrete i.chainKey
      ((SpqrChain.material Sha256.concrete ByteAuth.concrete i.pqChainKey i.pqCounter).drop 32)).material.macKey
    i.sender i.receiver i.plaintext
    (SpqrMessage.content Varint64.concrete Sha256.concrete ByteAuth.concrete pqShape
      (Varint64.pack Varint64.concrete ByteAuth.concrete i.epoch)
      (Varint.pack Sha256.concrete ByteAuth.concrete
        (ChainSend.nextCounter Sha256.concrete ByteAuth.concrete i.pqCounter)) i.kind i.chunkIndex i.chunkData)
    i.addresses
  rw [SpqrMessage.content_length, hchunk] at this
  have hnil : i.addresses.length = 0 := by rw [haddresses]; rfl
  simp only [Bool.false_eq_true, if_false] at this
  omega

/-! ## The staged block -/

theorem restage (l : List Byte) :
    (l.drop 0).take 1 ++ (l.drop 1).take 4 ++ (l.drop 5).take 36 ++ (l.drop 41).take 32 ++
      (l.drop 73).take 32 ++ (l.drop 105).take 4 ++ l.drop 109 = l := by
  have step : ∀ (k m : Nat), (l.drop k).take m ++ l.drop (k + m) = l.drop k := by
    intro k m
    rw [← List.drop_drop]
    exact List.take_append_drop m (l.drop k)
  have e6 := step 105 4
  have e5 := step 73 32
  have e4 := step 41 32
  have e3 := step 5 36
  have e2 := step 1 4
  have e1 := step 0 1
  simp only [Nat.reduceAdd] at e1 e2 e3 e4 e5 e6
  simp only [List.append_assoc]
  rw [e6, e5, e4, e3, e2, e1, List.drop_zero]

theorem stagedOf_length (session text : List Byte) (h : session.length = 182 + 80) :
    117 ≤ (stagedOf session text).length := by
  simp only [stagedOf, List.length_append, List.length_take, List.length_drop, h]
  omega

/-! ## The composition on concrete values -/

/-- The conversation record the kernel stores on acceptance: the certificate, the staged block
with the advanced counter, chain key, SPQR chain key and SPQR counter of the Signal send step,
and the metadata. -/
def advancedRecord (cert : Nat) (record staged : List Byte) (p : SpqrSend.Prepared Byte) : List Byte :=
  (record.drop 0).take cert ++
    ((staged.drop 0).take 1 ++ p.nextCounter ++ (staged.drop 5).take 36 ++ p.nextChainKey ++
      p.nextPqChainKey ++ p.nextPqCounter ++ staged.drop 109) ++
    (record.drop (cert + 182 + 80)).take 57

/-- **The seal kernels' composition, evaluated.** On accepted inputs: status 255, the record with
the advanced ratchet state, the timestamp, and the sealed-sender v1 envelope of the Signal message
of the reference send step. Otherwise: status 0, the record with the old ratchet state (and the
built text staged, see the module note), the timestamp, and zeros. -/
def sealValue (cert counterWidth previousWidth epochWidth indexWidth content : Nat)
    (record text ephemeralPublic senderPublic ephemeralAgreement staticAgreement : List Byte) :
    List (List Byte) :=
    let shape : Serialization.Shape := ⟨counterWidth, previousWidth, false⟩
    let pqShape : SpqrMessage.Shape := ⟨epochWidth, indexWidth, 1, false⟩
    let certificate := (record.drop 0).take cert
    let session := (record.drop cert).take (182 + 80)
    let metadata := (record.drop (cert + 182 + 80)).take 57
    let staged := stagedOf session text
    let i := inputOf 0 staged text content
    let p := SpqrSend.canonical shape pqShape i
    let envelope := sealV1 i.receiver ephemeralPublic senderPublic ephemeralAgreement staticAgreement
      certificate p.wire
    if SpqrSend.accepted shape pqShape i ∧
        boundAccepted ephemeralAgreement staticAgreement senderPublic i.sender ∧ text.getD 0 0 = 255 then
      [[255], advancedRecord cert record staged p, (text.drop (2 + content)).take 8, envelope]
    else
      [[0], certificate ++ staged ++ metadata, (text.drop (2 + content)).take 8,
        List.replicate envelope.length 0]

theorem canonical_lengths (shape : Serialization.Shape) (pqShape : SpqrMessage.Shape)
    (staged text : List Byte) (content : Nat) (h : 117 ≤ staged.length) :
    (SpqrSend.canonical shape pqShape (inputOf 0 staged text content)).nextChainKey.length =
        (inputOf 0 staged text content).chainKey.length ∧
      (SpqrSend.canonical shape pqShape (inputOf 0 staged text content)).nextCounter.length =
        (inputOf 0 staged text content).counter.length ∧
      (SpqrSend.canonical shape pqShape (inputOf 0 staged text content)).nextPqChainKey.length =
        (inputOf 0 staged text content).pqChainKey.length ∧
      (SpqrSend.canonical shape pqShape (inputOf 0 staged text content)).nextPqCounter.length =
        (inputOf 0 staged text content).pqCounter.length := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [SpqrSend.canonical, Symmetric.derive, Symmetric.nextChainKey, Sha256.hmac_length, inputOf]
    omega
  · simp [SpqrSend.canonical, ChainSend.nextCounter, inputOf]
    omega
  · simp [SpqrSend.canonical, SpqrChain.material_length, inputOf]
    omega
  · simp [SpqrSend.canonical, ChainSend.nextCounter, inputOf]
    omega

theorem sealFixedWith_value (cert counterWidth previousWidth epochWidth indexWidth content : Nat)
    (record text ephemeralPublic senderPublic ephemeralAgreement staticAgreement : List Byte)
    (hrecord : record.length = HybridKernel.conversationBytes cert 80)
    (hbound : cert + content + counterWidth + previousWidth + epochWidth + indexWidth < 2 ^ 31)
    (hephemeral : ephemeralPublic.length < 2 ^ 32) (hsender : senderPublic.length < 2 ^ 32) :
    sealFixedWith Aes.concrete Varint64.concrete Sha256.concrete ByteAuth.concrete 0
        cert counterWidth previousWidth epochWidth indexWidth content
        record text ephemeralPublic senderPublic ephemeralAgreement staticAgreement =
      sealValue cert counterWidth previousWidth epochWidth indexWidth content
        record text ephemeralPublic senderPublic ephemeralAgreement staticAgreement := by
  have hsession : ((record.drop cert).take (182 + 80)).length = 182 + 80 := by
    simp only [List.length_take, List.length_drop, hrecord, HybridKernel.conversationBytes]
    omega
  have hstaged := stagedOf_length _ text hsession
  have hcert : ((record.drop 0).take cert).length < 2 ^ 32 := by
    simp only [List.length_take, List.length_drop]
    omega
  simp only [sealFixedWith, sealValue]
  generalize stagedOf ((record.drop cert).take (182 + 80)) text = staged at hstaged ⊢
  have hratchet : (inputOf 0 staged text content).ratchet.length ≤ 32 := by
    simp only [inputOf, List.length_take]
    omega
  have hplain : (inputOf 0 staged text content).plaintext.length ≤ content := by
    simp only [inputOf, List.length_take]
    omega
  have hwire := canonical_wire_length_le ⟨counterWidth, previousWidth, false⟩ ⟨epochWidth, indexWidth, 1, false⟩
    (inputOf 0 staged text content) hratchet rfl rfl
  simp only at hwire
  obtain ⟨hk, hc, hpk, hpc⟩ := canonical_lengths ⟨counterWidth, previousWidth, false⟩
    ⟨epochWidth, indexWidth, 1, false⟩ staged text content hstaged
  have e1 : (inputOf 0 staged text content).counter = (staged.drop 1).take 4 := rfl
  have e2 : (inputOf 0 staged text content).chainKey = (staged.drop 41).take 32 := rfl
  have e3 : (inputOf 0 staged text content).pqChainKey = (staged.drop 73).take 32 := rfl
  have e4 : (inputOf 0 staged text content).pqCounter = (staged.drop 105).take 4 := rfl
  have h0 : ((0 : Byte) = 255) = False := by decide
  have hre := restage staged
  rw [List.drop_zero] at hre
  rw [SpqrSend.prepare_concrete_correct, SpqrSend.acceptedMask_value,
    SealValue.boundSeal_value _ _ _ _ _ _ _ _ hephemeral hsender hcert (by omega)]
  by_cases hA : SpqrSend.accepted ⟨counterWidth, previousWidth, false⟩ ⟨epochWidth, indexWidth, 1, false⟩
      (inputOf 0 staged text content) <;>
    by_cases hB : boundAccepted ephemeralAgreement staticAgreement senderPublic
      (inputOf 0 staged text content).sender <;>
    by_cases hT : text.getD 0 0 = 255 <;>
    simp only [hA, hB, hT, h0, if_true, if_false, and_true, and_false, and_self,
      List.getD_cons_zero, TlsProviderGate.gate_value, List.drop_succ_cons, List.drop_zero,
      ByteAuth.release_accept, ByteAuth.release_reject, List.length_replicate, ChainSend.selectState_reject,
      ChainSend.selectState_accept _ _ hk, ChainSend.selectState_accept _ _ hc,
      ChainSend.selectState_accept _ _ hpk, ChainSend.selectState_accept _ _ hpc, advancedRecord]
  all_goals simp only [e1, e2, e3, e4, hre]

open TlsMpc.HybridKernel (lookup) in
/-- **`signal-seal-official` / `signal-seal-built` on every input assignment** (both deployed
names): the kernel's four outputs (status, conversation record, timestamp, envelope) are
`sealValue` of the values of its input fields. So on accepted inputs the opened envelope is
`Reference.sealV1` (sealed sender v1) of the Signal message of the reference send step
`SpqrSend.canonical` on the stored state, and the stored record carries the advanced ratchet
state; otherwise the status is 0, the envelope all zero and the ratchet state the old one. The
only hypothesis bounds the kernel's public parameters (deployed values are far below it). -/
theorem signalSeal_value (cert counterWidth previousWidth epochWidth indexWidth classes : Nat) (official : Bool)
    (assign : BVExpr.Assignment)
    (hbound : cert + contentBytes classes official + counterWidth + previousWidth + epochWidth + indexWidth < 2 ^ 31) :
    let get := fun name => (lookup (sealInputs cert classes official) name).map (BVExpr.eval assign)
    (HybridKernel.signalSealFixed cert counterWidth previousWidth epochWidth indexWidth true classes official).outputs.map
        (fun field => field.value.map (BVExpr.eval assign)) =
      sealValue cert counterWidth previousWidth epochWidth indexWidth (contentBytes classes official)
        (get "conversation") (get "text") (get "ephemeralPublic") (get "senderPublic") (get "ephemeralAgreement")
        (get "staticAgreement") := by
  intro get
  rw [SealFixed.signalSealBuilt_spec]
  have hrecord : (get "conversation").length = HybridKernel.conversationBytes cert 80 := by
    simp [get, lookup, HybridKernel.lookupFrom, sealInputs, ByteCircuit.inputBytes]
  have hephemeral : (get "ephemeralPublic").length = 32 := by
    simp [get, lookup, HybridKernel.lookupFrom, sealInputs, HybridKdf.wordBytes]
  have hsender : (get "senderPublic").length = 32 := by
    simp [get, lookup, HybridKernel.lookupFrom, sealInputs, HybridKdf.wordBytes]
  exact sealFixedWith_value _ _ _ _ _ _ _ _ _ _ _ _ hrecord hbound
    (by show (get "ephemeralPublic").length < 2 ^ 32; omega)
    (by show (get "senderPublic").length < 2 ^ 32; omega)

/-- The opened envelope of an ACCEPTED seal (opened status 255) is sealed sender v1 of the
reference send step's Signal message; the stored record carries the advanced ratchet state. -/
theorem sealValue_accepted (cert counterWidth previousWidth epochWidth indexWidth content : Nat)
    (record text ephemeralPublic senderPublic ephemeralAgreement staticAgreement : List Byte)
    (opened : (sealValue cert counterWidth previousWidth epochWidth indexWidth content record text ephemeralPublic
      senderPublic ephemeralAgreement staticAgreement).getD 0 [] = [255]) :
    let shape : Serialization.Shape := ⟨counterWidth, previousWidth, false⟩
    let pqShape : SpqrMessage.Shape := ⟨epochWidth, indexWidth, 1, false⟩
    let certificate := (record.drop 0).take cert
    let staged := stagedOf ((record.drop cert).take (182 + 80)) text
    let i := inputOf 0 staged text content
    let p := SpqrSend.canonical shape pqShape i
    SpqrSend.accepted shape pqShape i ∧
      boundAccepted ephemeralAgreement staticAgreement senderPublic i.sender ∧ text.getD 0 0 = 255 ∧
      (sealValue cert counterWidth previousWidth epochWidth indexWidth content record text ephemeralPublic
        senderPublic ephemeralAgreement staticAgreement).getD 1 [] = advancedRecord cert record staged p ∧
      (sealValue cert counterWidth previousWidth epochWidth indexWidth content record text ephemeralPublic
        senderPublic ephemeralAgreement staticAgreement).getD 3 [] =
        sealV1 i.receiver ephemeralPublic senderPublic ephemeralAgreement staticAgreement certificate p.wire := by
  intro shape pqShape certificate staged i p
  simp only [sealValue] at opened ⊢
  split at opened
  · rename_i h
    simp only [if_pos h, List.getD_cons_succ, List.getD_cons_zero]
    exact ⟨h.1, h.2.1, h.2.2, rfl, rfl⟩
  · simp only [List.getD_cons_zero, List.cons.injEq, and_true] at opened
    exact absurd opened (by decide)

#print axioms sealFixedWith_value
#print axioms signalSeal_value
#print axioms sealValue_accepted

end TlsMpc.KernelSpecs.SealSend
