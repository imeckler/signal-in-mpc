import ChatResponseReferenceWork.StreamingV1.LengthFieldErrors
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- Actual native length success derives Core String counter/mode
at its actual terminal byte. No caller prefix/table/response-validity premise. -/
theorem native_message_length_transition (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64)
    (modes : state.modes = lane 2) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (kinds : state.kinds = [0,0,255,0])
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    ∃ leading byte tail,
      contents before = leading ++ byte::tail ∧ contents after = tail ∧
      let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (feed state leading) byte).state
      next.skip = native.bv ∧
      next.modes = if native.bv = BitVec.ofNat 64 0 then lane 0 else lane 3 := by
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
  refine ⟨leading,byte,tail,span,suffix,?_,?_⟩
  · rw [length_skip_terminal _ byte invariant.1 terminal,decoded]
  · rw [message_mode_terminal _ byte invariant.1 currentKinds terminal,decoded]

/-- Actual Prost String underflow: declared length exceeds all physical input
remaining after the length prefix. Actual Core rejects at actual EOF; no padding
or future byte can be borrowed into this input. Exact native error/suffix is kept
by the separate Bytes source reference. -/
theorem native_message_underflow_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64)
    (modes : state.modes = lane 2) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (kinds : state.kinds = [0,0,255,0]) (underflow : after.length < native.val)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨leading,byte,tail,span,suffix,counter,nextModes⟩ :=
    native_message_length_transition state before after native modes positions value kinds sourceSuccess
  have nonzero : native.bv ≠ BitVec.ofNat 64 0 := by
    intro equal
    have numeric := congrArg BitVec.toNat equal
    simp only [UScalar.bv_toNat,BitVec.toNat_ofNat] at numeric
    omega
  rw [if_neg nonzero] at nextModes
  have nativeBound : native.val < 2^64 := native.bv.isLt
  have nativeBits : native.bv = BitVec.ofNat 64 native.val := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt nativeBound,UScalar.bv_toNat]
  have tailLength : tail.length = after.length := by
    have result := congrArg List.length suffix
    simpa only [contents,List.length_map] using result.symm
  have result := opaque_truncated_reject
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (feed state leading) byte).state
    tail native.val nativeBound (by omega) nextModes (counter.trans nativeBits)
  rw [span]
  simpa only [feed,List.foldl_append,List.foldl_cons] using result


open ActualInnerResponseV1
/-- Physical String underflow retains native suffix, total clear and diagnostic
Result effects while the actual numeric parser rejects the same actual input. -/
theorem actual_message_underflow (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before after : Slice U8) (native : U64)
    (ctx : prost.encoding.DecodeContext) (underflow : after.length < native.val)
    (modes : state.modes = lane 2) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (kinds : state.kinds = [0,0,255,0])
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    merge_response InnerResponseV1.sliceBuf source (3#u32) .LengthDelimited before ctx =
      (do let observed ← InnerResponseV1.stamp diagnosticFrame2
            (.Err (fromStringError (StringContentV3.decodeError .BufferUnderflow)))
          .ok (observed,{source with message := some (alloc.vec.Vec.new U8)},after)) ∧
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  refine ⟨?_,native_message_underflow_reject state before after native modes positions value kinds underflow sourceSuccess⟩
  rw [actual_message_field_decoded source before after ctx (.Ok native) sourceSuccess]
  simp only [messageFieldDecoded,StringContentV3.bytesResult,if_neg (by omega : ¬native.val ≤ after.length),
    StringContentV3.stringResult,InnerResponseV1.strongStringResult]

#print axioms native_message_length_transition
#print axioms native_message_underflow_reject
#print axioms actual_message_underflow
end ChatResponseReference.StreamingV1
