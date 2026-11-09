import ChatResponseReferenceWork.StreamingUnknownV1.GroupPush
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey

private theorem write_zero (index tag : BitVec 64) (stack : List (BitVec 64)) :
    TlsChatResponse.writeStack Word64.concrete ByteAuth.concrete 0 index tag stack = stack := by
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  simp only [TlsChatResponse.writeStack,zeroAnd,Word64.select_reject]
  exact List.zipIdx_map_fst 0 stack

/-- Continuing key bytes do not mutate the group stack, including on invalid
lexer states. The actual terminal alone may install a decoded group tag. -/
theorem continuing_stack (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (continues : VarintDecode.Spqr.terminates byte = false) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.stack = state.stack := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 0 := by rw [terminal_exact byte,continues]; rfl
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  change TlsChatResponse.writeStack Word64.concrete ByteAuth.concrete
    (ByteAuth.concrete.and (ByteAuth.concrete.and _ (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7))) _)
    state.depth _ state.stack = state.stack
  rw [ended,andZero,zeroAnd,write_zero]

theorem continuing_prefix_stack (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (leading : List (BitVec 8))
    (continues : ∀ byte ∈ leading, VarintDecode.Spqr.terminates byte = false) :
    (feed state leading).stack = state.stack := by
  induction leading generalizing state with
  | nil => rfl
  | cons byte rest ih =>
    exact (ih (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state
      (by intro x member; exact continues x (by simp [member]))).trans (continuing_stack state byte (continues byte (by simp)))

/-- Non-start native keys preserve every stack slot. End keys pop logical depth
without clearing stale inactive storage, exactly as the actual numeric parser. -/
theorem native_nonstart_stack (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (native : U64) (tag : U32) (wire : WireType) (notStart : wire ≠ .StartGroup)
    (decoded : coreDecoded state byte = native.bv) (accepted : keyResult native = .Ok (tag,wire)) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.stack = state.stack := by
  have kind : Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7) = Word64.concrete.const (wireNumber wire) := by
    rw [decoded]; exact native_key_kind native tag wire accepted
  have notGroup : TlsChatResponse.weq Word64.concrete ByteAuth.concrete
      (Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7)) 3 = 0 := by
    rw [kind]
    cases wire <;> first | contradiction | rfl
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  change TlsChatResponse.writeStack Word64.concrete ByteAuth.concrete
    (ByteAuth.concrete.and _ (TlsChatResponse.weq Word64.concrete ByteAuth.concrete
      (Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7)) 3)) state.depth _ state.stack = state.stack
  rw [notGroup,andZero,write_zero]

#print axioms continuing_stack
#print axioms continuing_prefix_stack
#print axioms native_nonstart_stack
end ChatResponseReference.StreamingUnknownV1
