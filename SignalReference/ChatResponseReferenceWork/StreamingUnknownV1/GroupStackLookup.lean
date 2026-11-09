import ChatResponseReferenceWork.StreamingUnknownV1.GroupKeyGuard
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 500000

/-- Exact bounded numeric index comparison used by the actual stack circuits. -/
theorem stack_index_eq (index offset : Nat) (indexBound : index < 2^64) (offsetBound : offset < 2^64) :
    TlsChatResponse.weq Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 index) offset =
      if index = offset then 255 else 0 := by
  unfold TlsChatResponse.weq
  rw [word_eq_value]
  have equal : BitVec.ofNat 64 index = Word64.concrete.const offset ↔ index = offset := by
    constructor
    · intro same
      change BitVec.ofNat 64 index = BitVec.ofNat 64 offset at same
      have numeric := congrArg BitVec.toNat same
      simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt indexBound,Nat.mod_eq_of_lt offsetBound] using numeric
    · intro same; rw [same]; rfl
  simp only [equal]

/-- Actual oblivious lookup equals the corresponding active stack element.
The public 100-slot bound prevents integer index wraparound; no lookup oracle or
assumed table result is introduced. -/
theorem group_stack_lookup (stack : List (BitVec 64)) (start index : Nat)
    (size : start+stack.length ≤ 100) (lower : start ≤ index) (upper : index < start+stack.length) :
    TlsChatResponse.lookup Word64.concrete ByteAuth.concrete (BitVec.ofNat 64 index) start stack =
      stack[index-start]'(by omega) := by
  induction stack generalizing start with
  | nil => simp only [List.length_nil,Nat.add_zero] at upper; omega
  | cons row rest ih =>
    rw [TlsChatResponse.lookup,stack_index_eq index start (by simp only [List.length_cons] at upper size; omega) (by omega)]
    by_cases first : index = start
    · rw [if_pos first,Word64.select_accept]
      simp only [first,Nat.sub_self,List.getElem_cons_zero]
    · rw [if_neg first,Word64.select_reject]
      have nextSize : (start+1)+rest.length ≤ 100 := by simp only [List.length_cons] at size; omega
      have nextLower : start+1 ≤ index := by omega
      have nextUpper : index < (start+1)+rest.length := by simp only [List.length_cons] at upper; omega
      rw [ih (start+1) nextSize nextLower nextUpper]
      have offset : index-start = (index-(start+1))+1 := by omega
      simp only [offset,List.getElem_cons_succ]

#print axioms stack_index_eq
#print axioms group_stack_lookup
end ChatResponseReference.StreamingUnknownV1
