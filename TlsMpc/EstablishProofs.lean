import TlsMpc.EstablishKernels
import TlsMpc.HybridKernelsProofs

/-!
Theorems about the establishment kernels (`TlsMpc/EstablishKernels.lean`).

PROVED (standard axioms only; no `sorry`, no `native_decide`):

* `compiled_correct`: for every kernel `find` returns, each exported gate-level
  output bit equals the corresponding bit of the kernel's Lean definition
  evaluated on the inputs. (The JSON transport, the lowering to the flat gate
  list and the runtime are outside this statement.)
* `establishChallenges_spec`, `establishVerified_spec`, `establishSession_spec`,
  `establishSeal_spec`: on every input assignment, the kernel's output fields
  are the corresponding specification function of
  `TlsMpc/Signal/Establish.lean` on concrete bytes, applied to the values of the
  kernel's input fields. For `establish-seal` the text builder's output is
  taken as given (its own refinement theorem is in
  `TlsMpc/Signal/PrivateTextNotification.lean`).
* `Establish.keys_specification` (in that file): the concrete key derivation is
  the explicit HKDF/HMAC recurrence of PQXDH, the first sending ratchet step and
  the start of the post-quantum chain.
* `establish_rejects`: when the acceptance mask is 0 (a check byte other than
  255, or an all-zero agreement), the status and all three records are zero.

NOT PROVED, only tested (`handshake_backend/EmpHybridWork/check_establish_kernels.py`,
against an independent Python reference): that the specification functions
compute what libsignal computes. No theorem is stated about `establish-kem`
beyond `compiled_correct`, and none about the field programs beyond
`EstablishField.recover_correct` and `check_correct`. Nothing here is a
security statement.
-/
namespace TlsMpc.EstablishKernel
open Std.Tactic.BVDecide
open Signal
open HybridKernel (Kernel lookup sl)

theorem compiled_correct (arguments : List String) (k : Kernel) (_found : find arguments = some k)
    (assign : BVExpr.Assignment) (index : Nat) (hi : index < 8 * k.bytes.length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr k.bytes)).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr k.bytes)).vec.get index hi)) =
    (ByteCircuit.joinValue (k.bytes.map (BVExpr.eval assign))).getLsbD index :=
  HybridKernel.compiled_correct k assign index hi

/-- The values of a kernel's output fields under an assignment of its inputs. -/
def Kernel.values (k : Kernel) (assign : BVExpr.Assignment) : List (List (BitVec 8)) :=
  k.outputs.map (fun field => field.value.map (BVExpr.eval assign))

theorem getD_map (f : α → β) (lists : List (List α)) (index : Nat) :
    ((lists.getD index []).map f) = (lists.map (List.map f)).getD index [] := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases lists[index]? <;> rfl

/-! ### Signature verification -/

theorem establishChallenges_spec (assign : BVExpr.Assignment) :
    let value := fun name => (lookup challengeInputs name).map (BVExpr.eval assign)
    let run := fun (tag : Nat) (signature key : String) =>
      Establish.challenge ByteAuth.concrete XEdDsaSha512.concrete XEdDsaScalar.concrete tag
        (value signature) (value "identityX") (value "identityY") (value key)
    Kernel.values establishChallenges assign =
      [(run 5 "signedPrekeySignature" "signedPrekey").take 1, (run 5 "signedPrekeySignature" "signedPrekey").drop 1,
        (value "signedPrekeySignature").drop 32,
        (run 8 "kyberPrekeySignature" "kyberPrekey").take 1, (run 8 "kyberPrekeySignature" "kyberPrekey").drop 1,
        (value "kyberPrekeySignature").drop 32] := by
  intro value run
  simp only [run, value, ← Establish.challenge_map (ByteAuth.evaluationHom assign)
    (XEdDsaSha512.evaluationHom assign) (XEdDsaScalar.evaluationHom assign), ← List.map_take, ← List.map_drop]
  rfl

theorem establishVerified_spec (assign : BVExpr.Assignment) :
    let value := fun name => (lookup verifiedInputs name).map (BVExpr.eval assign)
    Kernel.values establishVerified assign =
      [[Establish.verified ByteAuth.concrete (value "signedPrekeySignature") (value "kyberPrekeySignature")
        (value "identityValid") (value "ecRx") (value "ecRy") (value "pqRx") (value "pqRy")]] := by
  intro value
  simp only [value, ← Establish.verified_map (ByteAuth.evaluationHom assign)]
  rfl

/-! ### Session keys and records -/

theorem establishSession_spec (cert : Nat) (withOneTime : Bool) (assign : BVExpr.Assignment) :
    let get := lookup (sessionInputs cert withOneTime)
    let e := BVExpr.eval assign
    Kernel.values (establishSession cert withOneTime) assign =
      Establish.establish Sha256.concrete ByteAuth.concrete 80 ((get "verified" ++ get "kemStatus").map e)
        ((get "dh1").map e) ((get "dh2").map e) ((get "dh3").map e) ((get "dh4").map e) ((get "kemSecret").map e)
        ((get "ratchetAgreement").map e) ((get "basePublic").map e) ((get "ratchetPublic").map e)
        ((get "senderPublic").map e) ((get "identityKey").map e) ((get "signedPrekey").map e)
        ((get "certificate").map e) ((get "uuid").map e) ((get "accessKey").map e) ((get "requestId").map e)
        ((get "deviceId").map e) ((get "registrationId").map e) ((get "localRegistrationId").map e)
        ((if withOneTime then get "oneTimePrekeyId" else HybridKernel.zeros 4).map e)
        ((get "signedPrekeyId").map e) ((get "kyberPrekeyId").map e) ((get "kemCiphertext").map e) := by
  intro get e
  rw [← Establish.establish_map (Sha256Ripple.evaluationHom assign) (ByteAuth.evaluationHom assign)]
  rfl

/-- A failed check gives status 0 and zero records, whatever the other inputs. -/
theorem establish_rejects (size : Nat) (checks : List (BitVec 8))
    (dh1 dh2 dh3 oneTime kem ratchetAgreement basePublic ratchetPublic senderPublic identityKey signedPrekey
      certificate uuid accessKey requestId device registration localRegistration oneTimeId signedId kyberId
      ciphertext : List (BitVec 8))
    (failed : Establish.accepted ByteAuth.concrete checks
      ([dh1, dh2, dh3] ++ (if oneTime.length = 0 then [] else [oneTime]) ++ [ratchetAgreement]) = 0) :
    ∀ field ∈ Establish.establish Sha256.concrete ByteAuth.concrete size checks dh1 dh2 dh3 oneTime kem
      ratchetAgreement basePublic ratchetPublic senderPublic identityKey signedPrekey certificate uuid accessKey
      requestId device registration localRegistration oneTimeId signedId kyberId ciphertext,
      ∀ byte ∈ field, byte = 0 := by
  intro field member byte inside
  simp only [Establish.establish, failed, List.mem_cons, List.not_mem_nil, or_false] at member
  have zero : ∀ bytes : List (BitVec 8), ∀ b ∈ ByteAuth.release ByteAuth.concrete 0 bytes, b = 0 := by
    intro bytes b hb
    simp only [ByteAuth.release, List.mem_map] at hb
    obtain ⟨x, _, rfl⟩ := hb
    exact BitVec.zero_and
  rcases member with rfl | rfl | rfl | rfl
  · simpa using inside
  · exact zero _ _ inside
  · exact zero _ _ inside
  · exact zero _ _ inside

/-! ### First message -/

theorem establishSeal_spec (cert : Nat) (withOneTime : Bool) (counterWidth previousWidth epochWidth indexWidth : Nat)
    (assign : BVExpr.Assignment) :
    let get := lookup (sealInputs cert)
    let e := BVExpr.eval assign
    let record := get "conversation"
    let text := PrivateTextNotification.build Sha256.symbolic Varint64.symbolic ByteAuth.symbolic (get "text")
    let out := Establish.sealMessage Aes.concrete Varint64.concrete Sha256.concrete ByteAuth.concrete withOneTime
      ⟨counterWidth, previousWidth, true⟩ ⟨epochWidth, indexWidth, 0, false⟩ 80 ((sl record cert 262).map e)
      ((sl record (cert + 262) 57).map e) ((get "pending").map e) ((sl record 0 cert).map e)
      ((get "localAddress").map e) (text.map e) ((get "ephemeralPublic").map e) ((get "senderPublic").map e)
      ((get "ephemeralAgreement").map e) ((get "staticAgreement").map e)
    Kernel.values (establishSeal cert withOneTime counterWidth previousWidth epochWidth indexWidth) assign =
      [out.getD 0 [], (sl record 0 cert).map e ++ out.getD 1 [] ++ (sl record (cert + 262) 57).map e,
        (sl text 82 8).map e, out.getD 2 []] := by
  dsimp only
  simp only [Kernel.values, establishSeal, HybridKernel.pub, HybridKernel.priv, List.map_cons, List.map_nil,
    List.map_append, getD_map, Establish.sealMessage_map (Aes.evaluationHom assign) (Varint64.evaluationHom assign)
      (Sha256Ripple.evaluationHom assign) (ByteAuth.evaluationHom assign)]

#print axioms compiled_correct
#print axioms establishChallenges_spec
#print axioms establishVerified_spec
#print axioms establishSession_spec
#print axioms establish_rejects
#print axioms establishSeal_spec

end TlsMpc.EstablishKernel
