import TlsMpc.ReceiveKernels
import TlsMpc.ReceiveField
import TlsMpc.EstablishProofs

/-!
Theorems about the first-message receive kernels (`TlsMpc/ReceiveKernels.lean`).

PROVED (standard axioms only; no `sorry`, no `native_decide`):

* `compiled_correct`: for every kernel `find` returns, each exported gate-level
  output bit equals the corresponding bit of the kernel's Lean definition
  evaluated on the inputs. (The JSON transport, the lowering to the flat gate
  list and the runtime are outside this statement.)
* `…_spec`, one per kernel: on every input assignment, the kernel's output
  fields are the corresponding specification function of
  `TlsMpc/Signal/ReceiveFirst.lean` on concrete bytes (with the reference
  SHA-256, AES, inverse AES, SHA-512 and scalar reduction), applied to the
  values of the kernel's input fields.
* `…_rejects`: when a stage's validity (its first result) is 0, every other
  result of that stage is zero: for the two halves of sealed sender (so the
  opened certificate length is zero), the content split, the prekey stage (so
  the opened ids and Kyber ciphertext are zero), and the session (records and
  plaintext).
* `keys_specification`: the concrete key derivation is the explicit HKDF/HMAC
  recurrence of PQXDH followed by the two ratchet steps and the start of the
  post-quantum chain.

NOT PROVED, only tested (`handshake_backend/EmpHybridWork/check_receive_kernels.py`,
against a real libsignal sender and an independent Python reference): that the
specification functions compute what libsignal computes; that the `shape`
kernels report the layout the later kernels then accept. Nothing here is a
security statement.
-/
namespace TlsMpc.ReceiveKernel
open Std.Tactic.BVDecide
open Signal
open HybridKernel (Kernel lookup)

theorem compiled_correct (arguments : List String) (k : Kernel) (_found : find arguments = some k)
    (assign : BVExpr.Assignment) (index : Nat) (hi : index < 8 * k.bytes.length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr k.bytes)).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr k.bytes)).vec.get index hi)) =
    (ByteCircuit.joinValue (k.bytes.map (BVExpr.eval assign))).getLsbD index :=
  HybridKernel.compiled_correct k assign index hi

/-- The values of a kernel's output fields under an assignment of its inputs. -/
def values (k : Kernel) (assign : BVExpr.Assignment) : List (List (BitVec 8)) :=
  k.outputs.map (fun field => field.value.map (BVExpr.eval assign))

/-! ### Sealed sender -/

theorem envelopePoint_spec (size : Nat) (assign : BVExpr.Assignment) :
    values (envelopePoint size) assign =
      [Establish.part ((lookup (envelopeInputs size) "envelope").map (BVExpr.eval assign)) 4 32] := by
  rw [← Establish.part_map]
  rfl

theorem unsealStatic_spec (size : Nat) (assign : BVExpr.Assignment) :
    let get := lookup (staticInputs size)
    let e := BVExpr.eval assign
    let out := ReceiveFirst.unsealStatic Aes.concrete Sha256.concrete ByteAuth.concrete size
      ((get "ourIdentity").map e) ((get "envelope").map e) ((get "agreement").map e)
    values (unsealStatic size) assign = [out.getD 0 [], out.getD 1 [], out.getD 1 [], out.getD 2 []] := by
  dsimp only
  simp only [values, unsealStatic, HybridKernel.priv, EstablishKernel.bits, List.map_cons, List.map_nil,
    EstablishKernel.getD_map, ReceiveFirst.unsealStatic_map (Aes.evaluationHom assign)
      (Sha256Ripple.evaluationHom assign) (ByteAuth.evaluationHom assign)]

theorem unsealMessage_spec (size : Nat) (assign : BVExpr.Assignment) :
    let get := lookup (messageInputs size)
    let e := BVExpr.eval assign
    values (unsealMessage size) assign =
      ReceiveFirst.unsealMessage Aes.concrete Sha256.concrete ByteAuth.concrete size ((get "envelope").map e)
        ((get "staticValid").map e) ((get "chain").map e) ((get "agreement").map e) := by
  intro get e
  rw [← ReceiveFirst.unsealMessage_map (Aes.evaluationHom assign) (Sha256Ripple.evaluationHom assign)
    (ByteAuth.evaluationHom assign)]
  rfl

theorem contentShape_spec (size cert : Nat) (assign : BVExpr.Assignment) :
    let get := lookup (contentInputs size)
    let e := BVExpr.eval assign
    values (contentShape size cert) assign =
      ReceiveFirst.contentShape ByteAuth.concrete size cert ((get "content").map e) ((get "valid").map e) := by
  intro get e
  rw [← ReceiveFirst.contentShape_map (ByteAuth.evaluationHom assign)]
  rfl

theorem content_spec (size cert : Nat) (hint : Bool) (assign : BVExpr.Assignment) :
    let get := lookup (contentInputs size)
    let e := BVExpr.eval assign
    values (content size cert hint) assign =
      ReceiveFirst.contentParts ByteAuth.concrete size cert hint ((get "content").map e) ((get "valid").map e) := by
  intro get e
  rw [← ReceiveFirst.contentParts_map (ByteAuth.evaluationHom assign)]
  rfl

/-! ### Sender certificate -/

theorem certificate_spec (cert : Nat) (c : ReceiveFirst.CertShape) (assign : BVExpr.Assignment) :
    let get := lookup (certificateInputs cert c)
    let e := BVExpr.eval assign
    let out := ReceiveFirst.certificate ByteAuth.concrete XEdDsaSha512.concrete XEdDsaScalar.concrete cert c
      ((get "certificate").map e) ((get "valid").map e) ((get "senderIdentity").map e) ((get "signer").map e)
      ((get "now").map e) ((get "serverX").map e) ((get "serverY").map e)
    values (certificate cert c) assign =
      [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 [], out.getD 4 [], out.getD 5 [],
        (out.getD 3 []).drop 32] := by
  dsimp only
  simp only [values, certificate, HybridKernel.priv, EstablishKernel.bits, List.map_cons, List.map_nil, List.map_drop,
    EstablishKernel.getD_map, ReceiveFirst.certificate_map (ByteAuth.evaluationHom assign)
      (XEdDsaSha512.evaluationHom assign) (XEdDsaScalar.evaluationHom assign)]

theorem certificateVerified_spec (assign : BVExpr.Assignment) :
    let get := lookup verifiedInputs
    let e := BVExpr.eval assign
    values (certificateVerified ()) assign =
      ReceiveFirst.certificateVerified ByteAuth.concrete ((get "certificateValid").map e) ((get "signature").map e)
        ((get "serverValid").map e) ((get "rx").map e) ((get "ry").map e) := by
  intro get e
  rw [← ReceiveFirst.certificateVerified_map (ByteAuth.evaluationHom assign)]
  rfl

/-! ### PreKeySignalMessage -/

theorem prekeyShape_spec (size : Nat) (assign : BVExpr.Assignment) :
    let get := lookup (shapeInputs size)
    let e := BVExpr.eval assign
    values (prekeyShape size) assign =
      ReceiveFirst.prekeyShape ByteAuth.concrete size ((get "message").map e) ((get "valid").map e) := by
  intro get e
  rw [← ReceiveFirst.prekeyShape_map (ByteAuth.evaluationHom assign)]
  rfl

theorem prekeyOpen_spec (size : Nat) (p : ReceiveFirst.PreKeyShape) (assign : BVExpr.Assignment) :
    let get := lookup (openInputs size)
    let e := BVExpr.eval assign
    values (prekeyOpen size p) assign =
      ReceiveFirst.prekeyOpen ByteAuth.concrete p size ((get "message").map e) ((get "valid").map e)
        ((get "messageType").map e) ((get "senderIdentity").map e) := by
  intro get e
  rw [← ReceiveFirst.prekeyOpen_map (ByteAuth.evaluationHom assign)]
  rfl

theorem signalShape_spec (size : Nat) (p : ReceiveFirst.PreKeyShape) (assign : BVExpr.Assignment) :
    let get := lookup (shapeInputs size)
    let e := BVExpr.eval assign
    values (signalShape size p) assign =
      ReceiveFirst.signalShape ByteAuth.concrete p size ((get "message").map e) ((get "valid").map e) := by
  intro get e
  rw [← ReceiveFirst.signalShape_map (ByteAuth.evaluationHom assign)]
  rfl

/-! ### Session -/

theorem session_spec (cert size : Nat) (p : ReceiveFirst.PreKeyShape) (q : ReceiveFirst.SignalShape) (jump : Nat)
    (assign : BVExpr.Assignment) :
    let get := lookup (sessionInputs cert size (p.oneTime != 0))
    let e := BVExpr.eval assign
    let out := ReceiveFirst.session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump
        ((get "message").map e)
        ((get "prekeyValid").map e ++ (get "verified").map e) ((get "senderIdentity").map e) ((get "ourIdentity").map e)
        ((get "localAddress").map e) ((get "uuid").map e) ((get "deviceId").map e) ((get "dh1").map e)
        ((get "dh2").map e) ((get "dh3").map e) ((get "dh4").map e) ((get "kemSecret").map e)
        ((get "receiveAgreement").map e) ((get "sendAgreement").map e) ((get "ratchetPublic").map e)
        ((get "baseValid").map e) ((get "torsionX").map e) ((get "torsionY").map e) ((get "certificate").map e)
        ((get "accessKey").map e) ((get "requestId").map e)
    values (session cert size p q jump) assign = [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 []] := by
  dsimp only
  simp only [values, session, HybridKernel.pub, HybridKernel.priv, List.map_cons, List.map_nil, List.map_append,
    EstablishKernel.getD_map, ReceiveFirst.session_map (AesInverse.evaluationHom assign)
      (Sha256Ripple.evaluationHom assign) (ByteAuth.evaluationHom assign)]

theorem text_spec (ciphertext capacity : Nat) (assign : BVExpr.Assignment) :
    let out := ReceiveFirst.text ByteAuth.concrete capacity
        ((lookup (textInputs ciphertext) "plaintext").map (BVExpr.eval assign))
    values (text ciphertext capacity) assign = [out.getD 0 [], out.getD 1 [], out.getD 2 [], out.getD 3 []] := by
  dsimp only
  simp only [values, text, HybridKernel.pub, List.map_cons, List.map_nil, EstablishKernel.getD_map,
    ReceiveFirst.text_map (ByteAuth.evaluationHom assign)]

theorem accessKey_spec (cert ciphertext offset : Nat) (assign : BVExpr.Assignment) :
    let get := lookup (accessKeyInputs cert ciphertext)
    let e := BVExpr.eval assign
    let out := ReceiveFirst.withAccessKey Aes.concrete ByteAuth.concrete cert offset ((get "conversation").map e)
        ((get "plaintext").map e)
    values (accessKey cert ciphertext offset) assign = [out.getD 0 [], out.getD 1 []] := by
  dsimp only
  simp only [values, accessKey, HybridKernel.pub, HybridKernel.priv, List.map_cons, List.map_nil,
    EstablishKernel.getD_map, ReceiveFirst.withAccessKey_map (Aes.evaluationHom assign) (ByteAuth.evaluationHom assign)]

/-! ### A failed stage releases nothing -/

theorem released_zero (status : BitVec 8) (fields : List (List (BitVec 8))) (failed : status = 0) :
    ∀ field ∈ [status] :: fields.map (ByteAuth.release ByteAuth.concrete status), ∀ byte ∈ field, byte = 0 := by
  intro field member byte inside
  subst failed
  rcases List.mem_cons.mp member with rfl | member
  · simpa using inside
  · obtain ⟨bytes, _, rfl⟩ := List.mem_map.mp member
    simp only [ByteAuth.release, List.mem_map] at inside
    obtain ⟨x, _, rfl⟩ := inside
    exact BitVec.zero_and

theorem unsealStatic_rejects (size : Nat) (ourIdentity envelope agreement : List (BitVec 8))
    (failed : (ReceiveFirst.unsealStatic Aes.concrete Sha256.concrete ByteAuth.concrete size ourIdentity envelope
      agreement).getD 0 [] = [0]) :
    ∀ field ∈ ReceiveFirst.unsealStatic Aes.concrete Sha256.concrete ByteAuth.concrete size ourIdentity envelope
      agreement, ∀ byte ∈ field, byte = 0 := by
  obtain ⟨status, fields, shape⟩ : ∃ status fields, ReceiveFirst.unsealStatic Aes.concrete Sha256.concrete
      ByteAuth.concrete size ourIdentity envelope agreement =
        [status] :: fields.map (ByteAuth.release ByteAuth.concrete status) := ⟨_, [_, _], rfl⟩
  rw [shape] at failed ⊢
  exact released_zero status fields (by simpa using failed)

theorem unsealMessage_rejects (size : Nat) (envelope staticValid chain agreement : List (BitVec 8))
    (failed : (ReceiveFirst.unsealMessage Aes.concrete Sha256.concrete ByteAuth.concrete size envelope staticValid
      chain agreement).getD 0 [] = [0]) :
    ∀ field ∈ ReceiveFirst.unsealMessage Aes.concrete Sha256.concrete ByteAuth.concrete size envelope staticValid
      chain agreement, ∀ byte ∈ field, byte = 0 := by
  obtain ⟨status, fields, shape⟩ : ∃ status fields, ReceiveFirst.unsealMessage Aes.concrete Sha256.concrete
      ByteAuth.concrete size envelope staticValid chain agreement =
        [status] :: fields.map (ByteAuth.release ByteAuth.concrete status) := ⟨_, [_, _], rfl⟩
  rw [shape] at failed ⊢
  exact released_zero status fields (by simpa using failed)

theorem content_rejects (size cert : Nat) (hint : Bool) (content valid : List (BitVec 8))
    (failed : (ReceiveFirst.contentParts ByteAuth.concrete size cert hint content valid).getD 0 [] = [0]) :
    ∀ field ∈ ReceiveFirst.contentParts ByteAuth.concrete size cert hint content valid, ∀ byte ∈ field, byte = 0 := by
  obtain ⟨status, fields, shape⟩ : ∃ status fields, ReceiveFirst.contentParts ByteAuth.concrete size cert hint content
      valid = [status] :: fields.map (ByteAuth.release ByteAuth.concrete status) := ⟨_, [_, _, _], rfl⟩
  rw [shape] at failed ⊢
  exact released_zero status fields (by simpa using failed)

theorem prekeyOpen_rejects (p : ReceiveFirst.PreKeyShape) (size : Nat)
    (message valid messageType senderIdentity : List (BitVec 8))
    (failed : (ReceiveFirst.prekeyOpen ByteAuth.concrete p size message valid messageType senderIdentity).getD 0 [] =
      [0]) :
    ∀ field ∈ ReceiveFirst.prekeyOpen ByteAuth.concrete p size message valid messageType senderIdentity,
      ∀ byte ∈ field, byte = 0 := by
  obtain ⟨status, fields, shape⟩ : ∃ status fields, ReceiveFirst.prekeyOpen ByteAuth.concrete p size message valid
      messageType senderIdentity = [status] :: fields.map (ByteAuth.release ByteAuth.concrete status) :=
    ⟨_, [_, _, _, _, _, _], rfl⟩
  rw [shape] at failed ⊢
  exact released_zero status fields (by simpa using failed)

theorem session_rejects (p : ReceiveFirst.PreKeyShape) (q : ReceiveFirst.SignalShape) (size jump : Nat)
    (message checks senderIdentity ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement
      sendAgreement ratchetPublic baseValid torsionX torsionY certificate accessKey requestId : List (BitVec 8))
    (failed : (ReceiveFirst.session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump message checks
      senderIdentity ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement
      ratchetPublic baseValid torsionX torsionY certificate accessKey requestId).getD 0 [] = [0]) :
    ∀ field ∈ ReceiveFirst.session AesInverse.concrete Sha256.concrete ByteAuth.concrete p q size jump message checks
      senderIdentity ourIdentity localAddress uuid device dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement
      ratchetPublic baseValid torsionX torsionY certificate accessKey requestId, ∀ byte ∈ field, byte = 0 := by
  obtain ⟨status, fields, shape⟩ : ∃ status fields, ReceiveFirst.session AesInverse.concrete Sha256.concrete
      ByteAuth.concrete p q size jump message checks senderIdentity ourIdentity localAddress uuid device dh1 dh2 dh3
      oneTime kem receiveAgreement sendAgreement ratchetPublic baseValid torsionX torsionY certificate accessKey
      requestId = [status] :: fields.map (ByteAuth.release ByteAuth.concrete status) := ⟨_, [_, _, _], rfl⟩
  rw [shape] at failed ⊢
  exact released_zero status fields (by simpa using failed)

/-! ### The key derivation as explicit HMAC steps -/

/-- The session keys, written out: PQXDH (`Pqxdh.specification`), the
receiving ratchet step, the sending ratchet step, and the start of the
post-quantum chain. -/
def keysSpecification (dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement : List (BitVec 8)) : List (BitVec 8) :=
  let handshake := Pqxdh.specification dh1 dh2 dh3 oneTime kem
  let receive := DhRatchet.material Sha256.concrete (handshake.take 32) receiveAgreement
  receive ++ DhRatchet.material Sha256.concrete (receive.take 32) sendAgreement ++
    TlsKdf.expandCore Sha256.concrete (TlsKdf.extract Sha256.concrete (List.replicate 32 0) (handshake.drop 64))
      ((TlsKdf.ascii "Signal PQ Ratchet V1 Chain  Start").map (BitVec.ofNat 8)) 96

theorem keys_specification (dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement : List (BitVec 8)) :
    ReceiveFirst.keys Sha256.concrete dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement =
      keysSpecification dh1 dh2 dh3 oneTime kem receiveAgreement sendAgreement := by
  simp only [ReceiveFirst.keys, keysSpecification, Pqxdh.deriveCore_specification, DhRatchet.materialFast_correct,
    PrivateInitialSpqrV1.chainStart, TlsKdf.expandFast_correct, TlsKdf.zeros]
  rfl

#print axioms compiled_correct
#print axioms unsealStatic_spec
#print axioms unsealMessage_spec
#print axioms contentShape_spec
#print axioms content_spec
#print axioms certificate_spec
#print axioms certificateVerified_spec
#print axioms prekeyShape_spec
#print axioms prekeyOpen_spec
#print axioms signalShape_spec
#print axioms session_spec
#print axioms text_spec
#print axioms unsealStatic_rejects
#print axioms unsealMessage_rejects
#print axioms content_rejects
#print axioms prekeyOpen_rejects
#print axioms session_rejects
#print axioms keys_specification

end TlsMpc.ReceiveKernel
