import ChatResponseReferenceWork.StreamingV1.TerminalNative
import ChatResponseReferenceWork.InnerScanV1.DriverReference
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkipKey

/-- Actual key validation is executed after the established Core lexer value.
Invalid key range, wire type and zero tag retain their real constructor and
precedence; no successful-key or response-validity premise is supplied. -/
theorem core_terminal_key (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before : Slice U8) (leading tail : List (BitVec 8)) (byte : BitVec 8)
    (bound : leading.length ≤ 9) (modes : state.modes = lane 0)
    (positions : state.positions = oneHot 0) (value : state.value = 0)
    (span : contents before = leading ++ byte::tail)
    (continues : ∀ byte ∈ leading, VarintDecode.Spqr.terminates byte = false)
    (terminal : VarintDecode.Spqr.terminates byte = true)
    (tenth : leading.length = 9 → byte.toNat < 2) :
    ∃ native after,
      LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (keyResult native,after) ∧
      ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok
        ((match keyResult native with
          | .Ok (tag,wire) => .Ok (tag,ActualResponseBytesV1.fromSkipWire wire)
          | .Err error => .Err (ActualResponseBytesV1.fromSkipError error)),after) ∧
      native.bv = coreDecoded (feed state leading) byte ∧ contents after = tail ∧
      leading.length+1 ≤ before.length := by
  obtain ⟨native,after,run,nativeValue,suffix,lengthBound⟩ := core_terminal_native
    state before leading tail byte 0 (by decide) bound modes positions value span continues terminal tenth
  have keyRun := key_from_varint before after (.Ok native) run
  change LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (keyResult native,after) at keyRun
  refine ⟨native,after,keyRun,?_,nativeValue,suffix,lengthBound⟩
  unfold ActualInnerScanV1.prost.encoding.decode_key
  rw [InnerScanV1.slice_adapter,keyRun]
  cases keyResult native <;> rfl

#print axioms core_terminal_key
end ChatResponseReference.StreamingV1
