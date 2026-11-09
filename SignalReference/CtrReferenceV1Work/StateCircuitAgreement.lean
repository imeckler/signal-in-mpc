import CtrReferenceV1Work.StateReference
import TlsMpc.Signal.SealedSenderV1
namespace LibSignalReference.Candidate.CtrState
open Aeneas Aeneas.Std
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
theorem counter_circuit (counter : U32) :
  (expected counter).val.map UScalar.bv =
    TlsMpc.Signal.SealedSenderV1.counter TlsMpc.Aes.concrete counter.val := by
  simp [expected, TlsMpc.Signal.SealedSenderV1.counter, TlsMpc.Aes.concrete,
    core.num.U32.to_be_bytes, BitVec.toBEBytes, BitVec.toLEBytes, List.range_succ]
  constructor <;> (try constructor)
  all_goals apply BitVec.eq_of_toNat_eq
  all_goals simp
  all_goals omega
/-- Actual pinned loop, including all nested mutable-slice writebacks, agrees
with the concrete sealed-sender counter circuit for the zero-nonce caller. -/
theorem actual_current_circuit (counter : U32) :
  ∃ block, _root_.CtrStateV1.current (zeroNonce counter) = .ok block ∧
    block.val.map UScalar.bv =
      TlsMpc.Signal.SealedSenderV1.counter TlsMpc.Aes.concrete counter.val := by
  exact ⟨expected counter, actual_current_zero_nonce counter, counter_circuit counter⟩
end LibSignalReference.Candidate.CtrState
