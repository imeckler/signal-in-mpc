import ChatResponseReferenceWork.ParserCircuitCandidateV1.MuxStackSafe
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1

/-- The codec's only lossy operation: erase the high half of each group tag. -/
def trimWord (word : BitVec 64) : BitVec 64 := word &&& 4294967295

def trimStack (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) :=
  {state with stack := state.stack.map trimWord}

theorem trim_word_narrow (word : BitVec 64) : NarrowWord (trimWord word) := by
  unfold NarrowWord trimWord
  rw [BitVec.ushiftRight_and_distrib]
  change (word >>> 32) &&& 0 = 0
  exact BitVec.and_zero

theorem trim_word_idempotent (word : BitVec 64) : trimWord (trimWord word) = trimWord word := by
  simp only [trimWord,BitVec.and_assoc,BitVec.and_self]

theorem trim_stack_idempotent (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) :
    trimStack (trimStack state) = trimStack state := by
  simp only [trimStack,List.map_map,Function.comp_def,trim_word_idempotent]

theorem trim_word_identity (word : BitVec 64) (narrow : NarrowWord word) : trimWord word = word := by
  have small : word.toNat < 2^32 := by
    have zero := congrArg BitVec.toNat narrow
    simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow] at zero
    have bound := Nat.div_eq_zero_iff.mp zero
    omega
  apply BitVec.eq_of_toNat_eq
  change word.toNat &&& (2^32-1) = word.toNat
  exact Nat.and_two_pow_sub_one_of_lt_two_pow small

theorem trim_stack_identity (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (narrow : NarrowStack state.stack) : trimStack state = state := by
  have same : state.stack.map trimWord = state.stack := by
    calc
      state.stack.map trimWord = state.stack.map id := List.map_congr_left (fun word member => trim_word_identity word (narrow word member))
      _ = state.stack := List.map_id _
  unfold trimStack
  rw [same]

theorem trim_word_select (mask : BitVec 8) (yes no : BitVec 64) :
    trimWord (Word64.concrete.select mask yes no) =
    Word64.concrete.select mask (trimWord yes) (trimWord no) := by
  apply BitVec.eq_of_getLsbD_eq
  intro index
  simp [trimWord,Word64.concrete,BitVec.getLsbD_and,BitVec.getLsbD_xor,
    Bool.and_xor_distrib_right,Bool.and_assoc]

theorem trim_write_stack (mask : BitVec 8) (index tag : BitVec 64) (stack : List (BitVec 64)) :
    (TlsChatResponse.writeStack Word64.concrete ByteAuth.concrete mask index tag stack).map trimWord =
    TlsChatResponse.writeStack Word64.concrete ByteAuth.concrete mask index (trimWord tag) (stack.map trimWord) := by
  simp only [TlsChatResponse.writeStack,List.map_map,List.zipIdx_map]
  congr 1
  funext pair
  exact trim_word_select _ _ _

theorem trim_lookup (index : BitVec 64) (start : Nat) (stack : List (BitVec 64)) :
    trimWord (TlsChatResponse.lookup Word64.concrete ByteAuth.concrete index start stack) =
    TlsChatResponse.lookup Word64.concrete ByteAuth.concrete index start (stack.map trimWord) := by
  induction stack generalizing start with
  | nil => exact BitVec.zero_and
  | cons word rest ih =>
    simp only [TlsChatResponse.lookup,List.map_cons,trim_word_select,ih]

theorem trim_stack_narrow (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) :
    NarrowStack (trimStack state).stack := by
  intro word member
  obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
  exact trim_word_narrow original

theorem trim_finish (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) :
    trimStack (TlsChatResponse.finish Word64.concrete ByteAuth.concrete state) =
    TlsChatResponse.finish Word64.concrete ByteAuth.concrete (trimStack state) := rfl

theorem trim_state_select (mask : BitVec 8)
    (yes no : TlsChatResponse.State (BitVec 8) (BitVec 64)) :
    trimStack (TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete mask yes no) =
    TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete mask (trimStack yes) (trimStack no) := by
  have stack : (List.zipWith (Word64.concrete.select mask) yes.stack no.stack).map trimWord =
      List.zipWith (Word64.concrete.select mask) (yes.stack.map trimWord) (no.stack.map trimWord) := by
    simp only [List.map_zipWith,List.zipWith_map,trim_word_select]
  cases yes
  cases no
  simp only [TlsChatResponse.stateSelect,trimStack,stack]

def trimEvent (event : TlsChatResponse.Event (BitVec 8) (BitVec 64)) :=
  {event with state := trimStack event.state}

theorem trim_rejected_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (rejected : state.valid = 0) :
    trimEvent (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (trimStack state) byte) =
    trimEvent (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte) := by
  have sameStack :
      (TlsChatResponse.writeStack Word64.concrete ByteAuth.concrete
        (ByteAuth.concrete.and (keyActivity state byte)
          (TlsChatResponse.weq Word64.concrete ByteAuth.concrete
            (Word64.concrete.band (decodedValue state byte) (Word64.concrete.const 7)) 3))
        state.depth (Word64.concrete.shift (decodedValue state byte) 3) (state.stack.map trimWord)).map trimWord =
      (TlsChatResponse.writeStack Word64.concrete ByteAuth.concrete
        (ByteAuth.concrete.and (keyActivity state byte)
          (TlsChatResponse.weq Word64.concrete ByteAuth.concrete
            (Word64.concrete.band (decodedValue state byte) (Word64.concrete.const 7)) 3))
        state.depth (Word64.concrete.shift (decodedValue state byte) 3) state.stack).map trimWord := by
    rw [trim_write_stack,trim_write_stack,List.map_map]
    simp only [Function.comp_def,trim_word_idempotent]
  have zeroAnd (other : BitVec 8) : ByteAuth.concrete.and 0 other = 0 := BitVec.zero_and
  simp only [trimEvent,trimStack,TlsChatResponse.step,rejected,zeroAnd]
  simp only [keyActivity,decodedValue] at sameStack
  rw [sameStack]

theorem trim_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (safe : SafeStack state) :
    trimEvent (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (trimStack state) byte) =
    trimEvent (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte) := by
  rcases safe with rejected|narrow
  · exact trim_rejected_step state byte rejected
  · rw [trim_stack_identity state narrow]

#print axioms trim_lookup
#print axioms trim_word_identity
#print axioms trim_state_select
#print axioms trim_rejected_step
#print axioms trim_step
#print axioms trim_word_select
#print axioms trim_write_stack
#print axioms trim_stack_narrow
#print axioms trim_finish
end ChatResponseReference.ParserCircuitCandidateV1
