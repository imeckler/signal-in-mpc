import ChatResponseReferenceWork.StreamingV1.KeyTransition
import ProtoParseWork.FullParserV3Work.KeyCircuit
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey

local instance (native : U64) : Decidable (ValidValue native) :=
  inferInstanceAs (Decidable (native.val ≤ 4294967295 ∧ 8 ≤ native.val ∧ native.val % 8 ≤ 5))

def commonKey (value : BitVec 64) : BitVec 8 :=
  (keyFields Word64.concrete ByteAuth.concrete ⟨255,0,value⟩).ok

theorem common_key_exact (native : U64) :
    commonKey native.bv = if ValidValue native then 255 else 0 := by
  unfold commonKey
  rw [key_mask]
  change (255 : BitVec 8) &&& (if native.val ≤ 4294967295 ∧ 8 ≤ native.val ∧ native.val % 8 ≤ 5 then 255 else 0) = _
  have hot (x : BitVec 8) : (255 : BitVec 8) &&& x = x := BitVec.allOnes_and
  rw [hot]
  rfl

theorem native_key_rejected_common (native : U64) (error : LoopSupportSkip.error.DecodeError)
    (rejected : keyResult native = .Err error) : commonKey native.bv = 0 := by
  rw [common_key_exact]
  apply if_neg
  intro valid
  obtain ⟨wire,accepted,_⟩ := key_success native valid
  rw [rejected] at accepted
  contradiction

#print axioms common_key_exact
#print axioms native_key_rejected_common
end ChatResponseReference.StreamingV1
