import ChatResponseReferenceWork.StreamingV1.LengthScope
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Exact private child scope after the actual native message length header,
independent of source/numeric validity and decoded UTF8 content. -/
theorem native_message_header_scope (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (remaining : Nat)
    (bounded : remaining ≤ 4096) (physical : remaining ≤ before.length)
    (headerFits : before.length-remaining ≤ after.length)
    (modes : state.modes = lane 2) (positions : state.positions = oneHot 0)
    (kinds : state.kinds = [0,0,255,0]) (inner : state.inner = 255)
    (counter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ header,
      contents before = header ++ contents after ∧
      (feed state header).responseRemaining = BitVec.ofNat 64 (remaining-header.length) ∧
      (feed state header).inner = (if header.length = remaining then 0 else 255) ∧
      (feed state header).depth = state.depth := by
  obtain ⟨leading,byte,tail,span,suffix,bound,continues,terminal,tenth,nativeValue⟩ := native_success_span before after native sourceSuccess
  have tailLength : tail.length = after.length := by
    have result := congrArg List.length suffix
    simpa only [contents,List.length_map] using result.symm
  have inputLength : before.length = leading.length+1+after.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append,List.length_cons,tailLength,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
  have inside : leading.length < remaining := by omega
  have context := bounded_varint_prefix_context state leading remaining bounded inside inner counter continues
  have invariant := core_prefix_invariant state leading 2 0 (by decide) (by omega) modes positions continues
  have currentKinds : (feed state leading).kinds = [0,0,255,0] :=
    (prefix_kinds state leading continues (by rw [kinds]; rfl)).trans kinds
  let header := leading ++ [byte]
  have length : header.length = leading.length+1 := by simp only [header,List.length_append,List.length_singleton]
  let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (feed state leading) byte).state
  have unfoldFeed : feed state header = next := by simp only [header,next,feed,List.foldl_append,List.foldl_cons,List.foldl_nil]
  have nextInner : next.inner = if remaining-leading.length = 1 then 0 else 255 :=
    length_inner_exact _ byte (remaining-leading.length) (by omega) (by rw [currentKinds]; rfl) context.2.2.2.1 context.2.2.2.2
  have equal : remaining-leading.length = 1 ↔ header.length = remaining := by omega
  refine ⟨header,?_,?_,?_,?_⟩
  · calc
      contents before = leading ++ byte::contents after := by rw [span,←suffix]
      _ = header ++ contents after := by simp only [header,List.append_assoc,List.singleton_append]
  · rw [unfoldFeed,message_length_remaining_step _ byte invariant.1 currentKinds context.2.2.2.1,context.2.2.2.2]
    change BitVec.ofNat 64 (remaining-leading.length) - BitVec.ofNat 64 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le (remaining-leading.length) 1 (by decide) (by omega)]
    congr 1 <;> omega
  · rw [unfoldFeed]
    simpa only [equal] using nextInner
  · rw [unfoldFeed]
    exact (message_length_depth_step _ byte invariant.1).trans context.2.2.1

#print axioms native_message_header_scope
end ChatResponseReference.StreamingV1
