import ChatResponseReferenceWork.StreamingUnknownV1.GroupOpaqueProjection
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1

private theorem opaque_stack_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 3) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.stack = state.stack := by
  have p0 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 3) 0 = 0 := rfl
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  change TlsChatResponse.writeStack Word64.concrete ByteAuth.concrete
    (ByteAuth.concrete.and (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0) _) _)
    state.depth _ state.stack = state.stack
  rw [modes,p0,zeroAnd,zeroAnd]
  simp only [TlsChatResponse.writeStack,zeroAnd,Word64.select_reject]
  exact List.zipIdx_map_fst 0 state.stack

/-- Every actual opaque payload prefix preserves the whole stack, retaining
inactive slots as well as the active source parent tags. -/
theorem group_opaque_prefix_stack (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (bytes : List (BitVec 8)) (count : Nat) (bounded : count < 2^64)
    (fits : bytes.length ≤ count) (modes : state.modes = lane 3) (skip : state.skip = BitVec.ofNat 64 count) :
    (feed state bytes).stack = state.stack := by
  induction bytes generalizing state count with
  | nil => rfl
  | cons byte rest ih =>
    have firstStack := opaque_stack_step state byte modes
    cases rest with
    | nil => exact firstStack
    | cons following tail =>
      let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state
      have first := opaque_prefix_inside state [byte] count bounded
        (by simp only [List.length_cons,List.length_nil] at fits ⊢; omega) modes skip
      exact (ih next (count-1) (by omega) (by simp only [List.length_cons] at fits ⊢; omega) first.1 first.2).trans firstStack

#print axioms group_opaque_prefix_stack
end ChatResponseReference.StreamingUnknownV1
