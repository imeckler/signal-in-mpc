import ChatResponseReferenceWork.StreamingUnknownV1.GroupKeyStack
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

theorem scalar_stack_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 1) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.stack = state.stack := by
  have p0 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 1) 0 = 0 := rfl
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  change TlsChatResponse.writeStack Word64.concrete ByteAuth.concrete
    (ByteAuth.concrete.and (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0) _) _)
    state.depth _ state.stack = state.stack
  rw [modes,p0,zeroAnd,zeroAnd]
  simp only [TlsChatResponse.writeStack,zeroAnd,Word64.select_reject]
  exact List.zipIdx_map_fst 0 state.stack

/-- Actual native scalar span preserves all stack slots, including inactive data;
no stack-clearing projection replaces the real implementation. -/
theorem native_scalar_stack (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64)
    (modes : state.modes = lane 1) (positions : state.positions = oneHot 0)
    (actual : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ consumed,contents before = consumed ++ contents after ∧ (feed state consumed).stack = state.stack := by
  obtain ⟨leading,byte,tail,span,suffix,bound,continues,terminal,tenth,nativeValue⟩ := native_success_span before after native actual
  have invariant := core_prefix_invariant state leading 1 0 (by decide) (by omega) modes positions continues
  let consumed := leading ++ [byte]
  refine ⟨consumed,?_,?_⟩
  · calc
      contents before = leading ++ byte::contents after := by rw [span,←suffix]
      _ = consumed ++ contents after := by simp only [consumed,List.append_assoc,List.singleton_append]
  · have result := (scalar_stack_step (feed state leading) byte invariant.1).trans (continuing_prefix_stack state leading continues)
    simpa only [consumed,feed,List.foldl_append,List.foldl_cons,List.foldl_nil] using result

#print axioms scalar_stack_step
#print axioms native_scalar_stack
end ChatResponseReference.StreamingUnknownV1
