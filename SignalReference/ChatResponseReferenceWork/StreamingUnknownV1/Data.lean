import ChatResponseReferenceWork.StreamingUnknownV1.Source
import ChatResponseReferenceWork.StreamingV1.ScalarResume
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

private theorem zero_and (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
private theorem and_zero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
private theorem either_zero (x : BitVec 8) : TlsWebSocketUpgrade.either ByteAuth.concrete x 0 = x := by
  unfold TlsWebSocketUpgrade.either
  have nz : ByteAuth.concrete.not 0 = 255 := rfl
  have keep (x : BitVec 8) : ByteAuth.concrete.and x 255 = x := BitVec.and_allOnes
  rw [nz,keep]
  exact BitVec.not_not

/-- Unknown scalar payloads never change any source-cached response field,
including on malformed/rejected intermediate states. -/
theorem unknown_scalar_step_data (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 1) (unknown : state.scalarKnown = 0) :
    responseData (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state = responseData state := by
  simp only [responseData,TlsChatResponse.step]
  rw [modes,unknown]
  have p0 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 1) 0 = 0 := rfl
  have p1 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 1) 1 = 255 := rfl
  have p2 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 1) 2 = 0 := rfl
  simp only [p0,p1,p2,zero_and,and_zero,either_zero,Word64.select_reject]

/-- Native scalar success determines the complete consumed prefix and leaves
cached source data unchanged, with exact lexer reset at its actual suffix. -/
theorem unknown_scalar_native_data (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (remaining : Nat)
    (bounded : remaining ≤ 4096) (physical : remaining ≤ before.length)
    (fits : before.length-remaining ≤ after.length) (modes : state.modes = lane 1)
    (positions : state.positions = oneHot 0)
    (inner : state.inner = 255) (counter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (unknown : state.scalarKnown = 0)
    (actual : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ consumed,
      contents before = consumed ++ contents after ∧
      responseData (feed state consumed) = responseData state ∧
      (feed state consumed).modes = lane 0 ∧ (feed state consumed).positions = oneHot 0 ∧
      (feed state consumed).value = 0 := by
  obtain ⟨leading,byte,tail,span,suffix,bound,continues,terminal,_tenth,_nativeValue⟩ := native_success_span before after native actual
  have tailLength : tail.length = after.length := by
    have result := congrArg List.length suffix
    simpa only [contents,List.length_map] using result.symm
  have inputLength : before.length = leading.length+1+after.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append,List.length_cons,tailLength,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
  have inside : leading.length < remaining := by omega
  have context := bounded_varint_prefix_context state leading remaining bounded inside inner counter continues
  have invariant := core_prefix_invariant state leading 1 0 (by decide) (by omega) modes positions continues
  have currentPositions : (feed state leading).positions = oneHot leading.length := by simpa only [Nat.zero_add] using invariant.2.1
  let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (feed state leading) byte).state
  have data : responseData next = responseData state := by
    rw [unknown_scalar_step_data _ byte invariant.1 (context.2.1.trans unknown),nonterminal_prefix_data state leading continues]
  have nextModes : next.modes = lane 0 := scalar_terminal_modes _ byte invariant.1 terminal
  have nextPositions : next.positions = oneHot 0 := terminal_position_reset _ byte 1 leading.length (by decide) invariant.1 currentPositions terminal
  have nextValue : next.value = 0 := terminal_value_reset _ byte 1 (by decide) invariant.1 terminal
  let consumed := leading ++ [byte]
  refine ⟨consumed,?_,?_,?_,?_,?_⟩
  · calc
      contents before = leading ++ byte::contents after := by rw [span,←suffix]
      _ = consumed ++ contents after := by simp only [consumed,List.append_assoc,List.singleton_append]
  · simpa only [consumed,next,feed,List.foldl_append,List.foldl_cons,List.foldl_nil] using data
  · simpa only [consumed,next,feed,List.foldl_append,List.foldl_cons,List.foldl_nil] using nextModes
  · simpa only [consumed,next,feed,List.foldl_append,List.foldl_cons,List.foldl_nil] using nextPositions
  · simpa only [consumed,next,feed,List.foldl_append,List.foldl_cons,List.foldl_nil] using nextValue

#print axioms unknown_scalar_step_data
#print axioms unknown_scalar_native_data
end ChatResponseReference.StreamingUnknownV1
