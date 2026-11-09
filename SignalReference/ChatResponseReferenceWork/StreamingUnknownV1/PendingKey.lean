import ChatResponseReferenceWork.StreamingUnknownV1.FixedReject
import ChatResponseReferenceWork.StreamingV1.NativePendingKey
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- A real source scalar key may end at/past the child boundary because Prost
uses the parent buffer. Core rejects before borrowing parent suffix or padding. -/
theorem actual_pending_key_not_inside_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before middle : Slice U8) (tag : U32) (wire : ActualInnerScanV1.prost.encoding.wire_type.WireType) (budget remaining : Nat)
    (pending : wireNumber (ActualInnerResponseV1.toSkipWire wire) = 0 ∨
      wireNumber (ActualInnerResponseV1.toSkipWire wire) = 1 ∨
      wireNumber (ActualInnerResponseV1.toSkipWire wire) = 2 ∨
      wireNumber (ActualInnerResponseV1.toSkipWire wire) = 5)
    (boundary : ChildAtKey state before budget remaining) (positive : 0 < remaining)
    (notInside : middle.length ≤ before.length-remaining)
    (actual : ActualInnerScanV1.prost.encoding.decode_key InnerScanV1.sliceBuf before = .ok (.Ok (tag,wire),middle)) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  have ready := ready_of_key state before budget remaining boundary positive
  have native := actual_driver_key_native before middle tag wire actual
  by_cases past : middle.length < before.length-remaining
  · obtain ⟨nativeValue,nativeRun,_⟩ := native_key_success_varint before middle tag (ActualInnerResponseV1.toSkipWire wire) native
    exact native_varint_child_overrun_reject state before middle nativeValue remaining 0 (by decide)
      ready.remainingBound positive ready.physical past boundary.modes ready.inner ready.childCounter nativeRun
  · exact native_pending_key_at_child_end state before middle tag (ActualInnerResponseV1.toSkipWire wire) remaining ready.remainingBound
      (by have := ready.physical; omega) pending boundary.modes ready.positions ready.value ready.inner ready.childCounter native

#print axioms actual_pending_key_not_inside_reject
end ChatResponseReference.StreamingUnknownV1
