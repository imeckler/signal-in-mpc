import ChatResponseReferenceWork.StreamingV1.OpaqueData
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

private theorem take_contents (after : Slice U8) (count : Nat) :
    contents (ActualResponseBytesV1.ContentModel.take after count) = (contents after).take count := by
  simp only [contents,ActualResponseBytesV1.ContentModel.take,List.map_take]
private theorem drop_contents (after : Slice U8) (count : Nat) :
    contents (LibSignalReference.Candidate.ProstBytesBuf.drop after count) = (contents after).drop count := by
  change (after.val.drop count).map UScalar.bv = (after.val.map UScalar.bv).drop count
  simp only [List.map_drop]

/-- Exact source copy partitions the actual source input; inactive capacity bytes
are not included in this span. -/
theorem copied_body_partition (after : Slice U8) (native : U64) (fits : native.val ≤ after.length) :
    contents after = contents (ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val) ++
      contents (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) := by
  rw [take_contents,drop_contents,BytesContentV1.payload_length after native fits]
  exact (List.take_append_drop native.val (contents after)).symm

/-- Successful actual source copy gives an exact consumed prefix and actual Core
post-payload cache/control state. This is cached data, not the full event/validity
relation; all source body contents remain exact in the separate source result. -/
theorem native_body_data_complete (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (fits : native.val ≤ after.length)
    (modes : state.modes = lane 2) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (kinds : state.kinds = [0,255,0,0])
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ consumed,
      contents before = consumed ++ contents (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) ∧
      responseData (feed state consumed) = {responseData state with bodyPresent := 255,bodyLength := native.bv} ∧
      (feed state consumed).modes = lane 0 ∧ (feed state consumed).skip = 0 := by
  obtain ⟨leading,byte,tail,span,suffix,bound,continues,terminal,tenth,nativeValue⟩ := native_success_span before after native sourceSuccess
  have invariant := core_prefix_invariant state leading 2 0 (by decide) (by omega) modes positions continues
  have currentKinds : (feed state leading).kinds = [0,255,0,0] :=
    (prefix_kinds state leading continues (by rw [kinds]; rfl)).trans kinds
  have currentPositions : (feed state leading).positions = oneHot leading.length := by simpa only [Nat.zero_add] using invariant.2.1
  have currentValue : (feed state leading).value = accumulated leading 0 0 := by simpa only [value] using invariant.2.2
  have decoded : coreDecoded (feed state leading) byte = native.bv := by
    unfold coreDecoded
    rw [currentPositions,currentValue,contribution_one_hot leading.length (by omega) byte]
    exact nativeValue.symm
  let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (feed state leading) byte).state
  have nextData : responseData next = {responseData state with bodyPresent := 255,bodyLength := native.bv} := by
    rw [body_length_response_data _ byte invariant.1 currentKinds terminal,nonterminal_prefix_data state leading continues,decoded]
  have nextModes := body_mode_terminal (feed state leading) byte invariant.1 currentKinds terminal
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
  have finished : responseData (feed next (contents payload)) = {responseData state with bodyPresent := 255,bodyLength := native.bv} ∧
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

/-- Actual generated source body-copy success and the matching complete Core
cached-data transition, with exact source content/returned suffix retained. -/
theorem actual_body_field_data_success (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8) (native : U64)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext) (fits : native.val ≤ after.length)
    (modes : state.modes = lane 2) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (kinds : state.kinds = [0,255,0,0])
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source (4#u32) .LengthDelimited before ctx =
      .ok (.Ok (),{source with body := some ⟨ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val⟩},
        LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) ∧
    ∃ consumed,
      contents before = consumed ++ contents (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) ∧
      responseData (feed state consumed) = {responseData state with bodyPresent := 255,bodyLength := native.bv} ∧
      (feed state consumed).modes = lane 0 ∧ (feed state consumed).skip = 0 := by
  refine ⟨?_,native_body_data_complete state before after native fits modes positions value kinds sourceSuccess⟩
  rw [actual_body_field_decoded source before after ctx (.Ok native) sourceSuccess,body_field_success source after native fits]

#print axioms copied_body_partition
#print axioms native_body_data_complete
#print axioms actual_body_field_data_success
end ChatResponseReference.StreamingV1
