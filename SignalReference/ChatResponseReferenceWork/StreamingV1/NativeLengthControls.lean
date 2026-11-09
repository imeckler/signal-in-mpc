import ChatResponseReferenceWork.StreamingV1.LengthControls
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

theorem native_length_field_controls (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (fits : native.val ≤ after.length)
    (modes : state.modes = lane 2) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (kindsShape : state.kinds.length = 4)
    (kindsOff : TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 0 = 0)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ consumed,
      contents before = consumed ++ contents (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) ∧
      (feed state consumed).positions = oneHot 0 ∧ (feed state consumed).value = 0 := by
  obtain ⟨leading,byte,tail,span,suffix,bound,continues,terminal,tenth,nativeValue⟩ := native_success_span before after native sourceSuccess
  have invariant := core_prefix_invariant state leading 2 0 (by decide) (by omega) modes positions continues
  have currentKinds : (feed state leading).kinds = state.kinds := prefix_kinds state leading continues kindsShape
  have currentKindsOff : TlsWebSocketUpgrade.get ByteAuth.concrete (feed state leading).kinds 0 = 0 := by rw [currentKinds]; exact kindsOff
  have currentPositions : (feed state leading).positions = oneHot leading.length := by simpa only [Nat.zero_add] using invariant.2.1
  have currentValue : (feed state leading).value = accumulated leading 0 0 := by simpa only [value] using invariant.2.2
  have decoded : coreDecoded (feed state leading) byte = native.bv := by
    unfold coreDecoded
    rw [currentPositions,currentValue,contribution_one_hot leading.length (by omega) byte]
    exact nativeValue.symm
  let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (feed state leading) byte).state
  have nextPositions : next.positions = oneHot 0 := terminal_position_reset _ byte 2 leading.length (by decide) invariant.1 currentPositions terminal
  have nextValue : next.value = 0 := terminal_value_reset _ byte 2 (by decide) invariant.1 terminal
  have nextModes := nonresponse_length_mode_terminal (feed state leading) byte invariant.1 currentKindsOff terminal
  have nextSkip := length_skip_terminal (feed state leading) byte invariant.1 terminal
  rw [decoded] at nextModes nextSkip
  let payload := ActualResponseBytesV1.ContentModel.take after (UScalar.cast .Usize native).val
  have payloadLength : (contents payload).length = native.val := by
    simpa only [contents,List.length_map] using copied_body_length after native fits
  have nativeBound : native.val < 2^64 := native.bv.isLt
  have nativeBits : native.bv = BitVec.ofNat 64 native.val := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt nativeBound,UScalar.bv_toNat]
  have finished : (feed next (contents payload)).positions = oneHot 0 ∧ (feed next (contents payload)).value = 0 := by
    by_cases empty : native.val = 0
    · have noPayload : contents payload = [] := List.length_eq_zero_iff.mp (payloadLength.trans empty)
      rw [noPayload]
      exact ⟨nextPositions,nextValue⟩
    · have nonzero : native.bv ≠ BitVec.ofNat 64 0 := by
        intro equal; have numeric := congrArg BitVec.toNat equal
        simp only [UScalar.bv_toNat,BitVec.toNat_ofNat] at numeric
        exact empty numeric
      rw [if_neg nonzero] at nextModes
      have result := opaque_prefix_controls next (contents payload) native.val nativeBound (by rw [payloadLength]) nextModes
        (nextSkip.trans nativeBits) (by rw [nextPositions]; rfl)
      exact ⟨result.1.trans nextPositions,result.2.trans nextValue⟩
  let consumed := leading ++ byte::contents payload
  refine ⟨consumed,?_,?_,?_⟩
  · calc
      contents before = leading ++ byte::contents after := by rw [span,←suffix]
      _ = leading ++ byte::(contents payload ++ contents (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val)) := by rw [copied_body_partition after native fits]
      _ = consumed ++ contents (LibSignalReference.Candidate.ProstBytesBuf.drop after native.val) := by simp only [consumed,List.append_assoc,List.cons_append]
  · simpa only [consumed,next,feed,List.foldl_append,List.foldl_cons] using finished.1
  · simpa only [consumed,next,feed,List.foldl_append,List.foldl_cons] using finished.2

#print axioms native_length_field_controls
end ChatResponseReference.StreamingV1
