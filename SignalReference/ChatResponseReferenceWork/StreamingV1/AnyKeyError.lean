import ChatResponseReferenceWork.StreamingV1.LexerShape
import ChatResponseReferenceWork.StreamingV1.CoreKeyGuard
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkipKey

/-- For every nonempty input, an actual native key error rejects the actual Core
fold and finish, without a prefix decomposition or decoder-table premise. Native
error contents and exact cursor remain in the separate actual key result. -/
theorem any_native_key_error_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (error : LoopSupportSkip.error.DecodeError)
    (nonempty : 0 < before.length) (modes : state.modes = lane 0)
    (positions : state.positions = oneHot 0) (value : state.value = 0)
    (sourceError : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Err error,after)) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  cases lexer_shape (contents before) with
  | terminal leading tail byte span bound continues ended tenth =>
    obtain ⟨native,suffix,keyRun,_,nativeValue,_,_⟩ :=
      core_terminal_key state before leading tail byte bound modes positions value span continues ended tenth
    rw [sourceError] at keyRun
    have rejected : keyResult native = .Err error := (congrArg Prod.fst (Result.ok.inj keyRun)).symm
    rw [span]
    have result := native_key_failure_tail (feed state leading) byte tail native error
      (core_prefix_invariant state leading 0 0 (by decide) (by omega) modes positions continues).1
      ended nativeValue rejected
    simpa only [feed,List.foldl_append] using result
  | malformed leading tail byte span length continues invalid =>
    rw [span]
    exact bad_tenth_suffix_reject state leading tail byte 0 (by decide) length modes positions continues invalid
  | truncated leading span bound continues =>
    rw [span]
    have positive : 0 < leading.length := by
      have len : (contents before).length = before.length := by simp only [contents,List.length_map]
      rw [span] at len
      omega
    exact prefix_eof_reject state leading 0 (by decide) bound modes positions continues (.inr positive)

/-- The same all-input result at the actual generated schema driver's key ABI. -/
theorem actual_driver_key_error_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (error : ActualInnerScanV1.prost.error.DecodeError)
    (nonempty : 0 < before.length) (modes : state.modes = lane 0)
    (positions : state.positions = oneHot 0) (value : state.value = 0)
    (sourceError : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Err error,after)) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨result,middle,nativeRun,actualRun,_,_⟩ := InnerScanV1.key_total before
  cases result with
  | Err raw => exact any_native_key_error_reject state before middle raw nonempty modes positions value nativeRun
  | Ok pair =>
    rcases pair with ⟨tag,wire⟩
    rw [sourceError] at actualRun
    simp at actualRun

#print axioms any_native_key_error_reject
#print axioms actual_driver_key_error_reject
end ChatResponseReference.StreamingV1
