import ChatResponseReferenceWork.StreamingV1.MessageLengthData
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Successful actual source copy gives an exact consumed prefix and actual Core
post-payload cache/control state. This is cached data, not the full event/validity
relation; all source body contents remain exact in the separate source result. -/
theorem native_message_data_complete (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (fits : native.val ≤ after.length)
    (modes : state.modes = lane 2) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (kinds : state.kinds = [0,0,255,0])
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ consumed,
      contents before = consumed ++ contents (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) ∧
      responseData (feed state consumed) = {responseData state with messagePresent := 255} ∧
      (feed state consumed).modes = lane 0 ∧ (feed state consumed).skip = 0 := by
  obtain ⟨leading,byte,tail,span,suffix,bound,continues,terminal,tenth,nativeValue⟩ := native_success_span before after native sourceSuccess
  have invariant := core_prefix_invariant state leading 2 0 (by decide) (by omega) modes positions continues
  have currentKinds : (feed state leading).kinds = [0,0,255,0] :=
    (prefix_kinds state leading continues (by rw [kinds]; rfl)).trans kinds
  have currentPositions : (feed state leading).positions = oneHot leading.length := by simpa only [Nat.zero_add] using invariant.2.1
  have currentValue : (feed state leading).value = accumulated leading 0 0 := by simpa only [value] using invariant.2.2
  have decoded : coreDecoded (feed state leading) byte = native.bv := by
    unfold coreDecoded
    rw [currentPositions,currentValue,contribution_one_hot leading.length (by omega) byte]
    exact nativeValue.symm
  let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (feed state leading) byte).state
  have nextData : responseData next = {responseData state with messagePresent := 255} := by
    rw [message_length_response_data _ byte invariant.1 currentKinds terminal,nonterminal_prefix_data state leading continues]
  have nextModes := message_mode_terminal (feed state leading) byte invariant.1 currentKinds terminal
  have nextCounter := length_skip_terminal (feed state leading) byte invariant.1 terminal
  rw [decoded] at nextModes nextCounter
  let payload := ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val
  have payloadLength : (contents payload).length = native.val := by
    have result := copied_body_length after native fits
    simpa only [contents,List.length_map] using result
  have nativeBound : native.val < 2^64 := native.bv.isLt
  have nativeBits : native.bv = BitVec.ofNat 64 native.val := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt nativeBound,UScalar.bv_toNat]
  have finished : responseData (feed next (contents payload)) = {responseData state with messagePresent := 255} ∧
      (feed next (contents payload)).modes = lane 0 ∧ (feed next (contents payload)).skip = 0 := by
    by_cases empty : native.val = 0
    · have emptyPayload : contents payload = [] := List.length_eq_zero_iff.mp (payloadLength.trans empty)
      have zero : native.bv = BitVec.ofNat 64 0 := by rw [nativeBits,empty]
      rw [if_pos zero] at nextModes
      rw [zero] at nextCounter
      rw [emptyPayload]
      exact ⟨nextData,nextModes,nextCounter⟩
    · have nonzero : native.bv ≠ BitVec.ofNat 64 0 := by
        intro equal
        have numeric := congrArg BitVec.toNat equal
        simp only [UScalar.bv_toNat,BitVec.toNat_ofNat] at numeric
        exact empty numeric
      rw [if_neg nonzero] at nextModes
      have nonempty : contents payload ≠ [] := by intro nil; have := congrArg List.length nil; rw [payloadLength] at this; exact empty this
      have metadata := opaque_prefix_data next (contents payload) native.val nativeBound (by rw [payloadLength]) nextModes (nextCounter.trans nativeBits)
      have complete := opaque_payload_complete next (contents payload) nonempty (by rw [payloadLength]; exact nativeBound) nextModes
        (by rw [payloadLength]; exact nextCounter.trans nativeBits)
      exact ⟨metadata.trans nextData,complete⟩
  let consumed := leading ++ byte::contents payload
  refine ⟨consumed,?_,?_,?_,?_⟩
  · calc
      contents before = leading ++ byte::contents after := by rw [span,←suffix]
      _ = leading ++ byte::(contents payload ++ contents (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val)) := by rw [copied_body_partition after native fits]
      _ = consumed ++ contents (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) := by simp only [consumed,List.append_assoc,List.cons_append]
  · simpa only [consumed,next,feed,List.foldl_append,List.foldl_cons] using finished.1
  · simpa only [consumed,next,feed,List.foldl_append,List.foldl_cons] using finished.2.1
  · simpa only [consumed,next,feed,List.foldl_append,List.foldl_cons] using finished.2.2

#print axioms native_message_data_complete
end ChatResponseReference.StreamingV1
