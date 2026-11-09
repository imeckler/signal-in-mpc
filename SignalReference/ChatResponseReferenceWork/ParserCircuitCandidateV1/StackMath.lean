import ChatResponseReferenceWork.ParserCircuitCandidateV1.CompiledCodec
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1

def NarrowWord (word : BitVec 64) : Prop := word >>> 32 = 0

def NarrowStack (stack : List (BitVec 64)) : Prop := ∀ word ∈ stack, NarrowWord word

theorem narrow_of_bound (word : BitVec 64) (bound : word.toNat < 2^32) : NarrowWord word := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,Nat.div_eq_of_lt bound,BitVec.toNat_ofNat]
  rfl

theorem narrow_select (mask : BitVec 8) (yes no : BitVec 64)
    (hy : NarrowWord yes) (hn : NarrowWord no) : NarrowWord (Word64.concrete.select mask yes no) := by
  unfold NarrowWord at hy hn ⊢
  change ((BitVec.replicate 8 mask &&& yes) ^^^ ((~~~BitVec.replicate 8 mask) &&& no)) >>> 32 = 0
  rw [BitVec.ushiftRight_xor_distrib,BitVec.ushiftRight_and_distrib,BitVec.ushiftRight_and_distrib,hy,hn]
  have andZero (x : BitVec 64) : x &&& 0 = 0 := BitVec.and_zero
  have xorZero : (0 : BitVec 64) ^^^ 0 = 0 := rfl
  simp only [andZero,xorZero]

theorem narrow_write_stack (mask : BitVec 8) (index tag : BitVec 64) (stack : List (BitVec 64))
    (old : NarrowStack stack) (written : NarrowWord tag) :
    NarrowStack (TlsChatResponse.writeStack Word64.concrete ByteAuth.concrete mask index tag stack) := by
  intro word member
  obtain ⟨pair,inStack,rfl⟩ := List.mem_map.mp member
  rcases pair with ⟨value,position⟩
  have valueMember : value ∈ stack := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp inStack)
  exact narrow_select _ tag value written (old value valueMember)

theorem write_stack_zero (index tag : BitVec 64) (stack : List (BitVec 64)) :
    TlsChatResponse.writeStack Word64.concrete ByteAuth.concrete 0 index tag stack = stack := by
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  simp only [TlsChatResponse.writeStack,zeroAnd,Word64.select_reject]
  exact List.zipIdx_map_fst 0 stack

#print axioms narrow_of_bound
#print axioms narrow_select
#print axioms narrow_write_stack
#print axioms write_stack_zero
end ChatResponseReference.ParserCircuitCandidateV1
