import ChatResponseReferenceWork.ParserCircuitCandidateV1.KeyRange
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Rejected intermediate scratch may contain high tag bits. The invariant
requires narrow stack words only while parsing is not already rejected. -/
def SafeStack (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) : Prop :=
  state.valid = 0 ∨ NarrowStack state.stack

theorem step_zero_valid (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8) (zero : state.valid = 0) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.valid = 0 := by
  change ByteAuth.concrete.and state.valid _ = 0
  rw [zero]
  exact BitVec.zero_and

theorem step_narrow_stack (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (old : NarrowStack state.stack) (controls : ControlMasks state)
    (valid : (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.valid ≠ 0) :
    NarrowStack (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.stack := by
  have active : Canonical (keyActivity state byte) := canonical_and _ _ (canonical_get state.modes 0 controls.modes) (canonical_terminal byte)
  change NarrowStack (TlsChatResponse.writeStack Word64.concrete ByteAuth.concrete
    (ByteAuth.concrete.and (keyActivity state byte) _)
    state.depth (Word64.concrete.shift (decodedValue state byte) 3) state.stack)
  rcases active with inactive|active
  · have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
    rw [inactive,zeroAnd,write_stack_zero]
    exact old
  · exact narrow_write_stack _ _ _ _ old (nonrejected_key_tag_narrow state byte active valid)

theorem step_safe_stack (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (old : SafeStack state) (controls : ControlMasks state) :
    SafeStack (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state := by
  by_cases rejected : (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.valid = 0
  · exact .inl rejected
  · rcases old with zero|narrow
    · exact False.elim (rejected (step_zero_valid state byte zero))
    · exact .inr (step_narrow_stack state byte narrow controls rejected)

theorem initial_narrow_stack (capacity : Nat) (expected : BitVec 64) :
    NarrowStack (TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity expected).stack := by
  intro word member
  change word ∈ List.replicate 100 (Word64.concrete.const 0) at member
  have equal := List.eq_of_mem_replicate member
  rw [equal]
  rfl

theorem finish_safe_stack (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (previous : SafeStack state) :
    SafeStack (TlsChatResponse.finish Word64.concrete ByteAuth.concrete state) := by
  rcases previous with rejected|narrow
  · apply Or.inl
    change ByteAuth.concrete.and state.valid _ = 0
    rw [rejected]
    exact BitVec.zero_and
  · exact .inr narrow

#print axioms step_narrow_stack
#print axioms step_safe_stack
#print axioms initial_narrow_stack
#print axioms finish_safe_stack
end ChatResponseReference.ParserCircuitCandidateV1
