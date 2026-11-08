import SkipPlanWork.Group

namespace LibSignalReference.Candidate.ProstSkipPlan
open TlsMpc TlsMpc.Signal
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 500000

/-- Oblivious lookup agrees with ordinary list indexing throughout its bounded
range; the bound excludes 64-bit index aliases. -/
theorem lookup_stack_get (stack : List (BitVec 64)) (start index : Nat)
    (hi : index < stack.length) (hb : start + stack.length ≤ 2^64) :
    ProtoParse.lookupWord Word64.concrete ByteAuth.concrete
      (BitVec.ofNat 64 (start + index)) start stack = stack[index] := by
  induction stack generalizing start index with
  | nil => simp at hi
  | cons x xs ih =>
    cases index with
    | zero =>
      simp only [Nat.add_zero,ProtoParse.lookupWord,word_eq_value,List.getElem_cons_zero]
      have he : BitVec.ofNat 64 start = Word64.concrete.const start := rfl
      rw [if_pos he,Word64.select_accept]
    | succ index =>
      have hi' : index < xs.length := by simpa using hi
      have hs : start < 2^64 := by simp only [List.length_cons] at hb; omega
      have hx : start + (index+1) < 2^64 := by simp only [List.length_cons] at hb; omega
      have hn : BitVec.ofNat 64 (start+(index+1)) ≠ Word64.concrete.const start := by
        intro he
        have hh := congrArg BitVec.toNat he
        change (start+(index+1)) % 2^64 = start % 2^64 at hh
        rw [Nat.mod_eq_of_lt hx,Nat.mod_eq_of_lt hs] at hh
        omega
      simp only [ProtoParse.lookupWord,word_eq_value,List.getElem_cons_succ,if_neg hn]
      rw [Word64.select_reject]
      have next := ih (start+1) index hi' (by simp only [List.length_cons] at hb; omega)
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using next

#print axioms lookup_stack_get
end LibSignalReference.Candidate.ProstSkipPlan
