import ChatResponseReferenceWork.StatusReference
import ChatResponseReferenceWork.FinishReference
namespace ChatResponseReference.HttpStatusBridge
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
open ActualChatResponseStatus
/-- Project actual checked HTTP conversion to the two private Core flags.
The exact native conversion theorem independently retains the error result. -/
noncomputable def nativeFlags (raw : U32) : BitVec 8 × BitVec 8 :=
  match checked_status raw with
  | .ok (.Ok (_,successful)) => (255,if successful then 255 else 0)
  | _ => (0,0)
theorem native_status_flags (raw : U32) : nativeFlags raw =
    (if 100 ≤ raw.val ∧ raw.val ≤ 999 then 255 else 0,
     if 200 ≤ raw.val ∧ raw.val ≤ 299 then 255 else 0) := by
  unfold nativeFlags
  rw [Status.checked_status_reference]
  by_cases bound : raw.val ≤ UScalar.max .U16
  · simp only [if_pos bound]
    have value : (UScalar.cast .U16 raw).val = raw.val := by
      rw [UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      change raw.val < 65536
      have hb : raw.val ≤ 65535 := by
        simpa only [UScalar.max_UScalarTy_U16_eq,U16.max_eq] using bound
      omega
    have low : (100#u16 ≤ UScalar.cast .U16 raw) ↔ 100 ≤ raw.val := by scalar_tac
    have high : (UScalar.cast .U16 raw ≤ 999#u16) ↔ raw.val ≤ 999 := by scalar_tac
    have sl : (200#u16 ≤ UScalar.cast .U16 raw) ↔ 200 ≤ raw.val := by scalar_tac
    have su : (UScalar.cast .U16 raw < 300#u16) ↔ raw.val ≤ 299 := by scalar_tac
    simp only [low,high,sl,su]
    by_cases hl : 100 ≤ raw.val <;> by_cases hu : raw.val ≤ 999 <;>
      by_cases hs : 200 ≤ raw.val ∧ raw.val ≤ 299 <;>
      simp [hl,hu,hs] <;> omega
  · have large : 65535 < raw.val := by
      have hb : ¬raw.val ≤ 65535 := by simpa only [UScalar.max_UScalarTy_U16_eq,U16.max_eq] using bound
      omega
    simp only [if_neg bound]
    simp [show ¬(100 ≤ raw.val ∧ raw.val ≤ 999) by omega,
      show ¬(200 ≤ raw.val ∧ raw.val ≤ 299) by omega]
/-- Actual checked native status and both numeric Core decisions agree whenever
schema completion and exact private ID binding have been established. -/
theorem core_native_status (s : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (ready : Finish.Ready s) (raw : U32) (status : s.status.toNat = raw.val) :
    ((TlsChatResponse.finish Word64.concrete ByteAuth.concrete s).valid,
     (TlsChatResponse.finish Word64.concrete ByteAuth.concrete s).successful) = nativeFlags raw := by
  rw [Finish.core_status_range s ready,Finish.core_success_range s ready,native_status_flags,status]
#print axioms native_status_flags
#print axioms core_native_status
end ChatResponseReference.HttpStatusBridge
