import ChatResponseReferenceWork.StreamingV1.KnownWire
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkipKey

private theorem rejected_terminal_tail (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (leading tail : List (BitVec 8)) (byte : BitVec 8)
    (invalid : (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (feed state leading) byte).state.valid = 0) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (leading ++ byte::tail))).valid = 0 := by
  apply finish_invalid_sticky
  simp only [feed,List.foldl_append,List.foldl_cons]
  exact feed_invalid_sticky _ tail invalid

/-- All native known response fields with wrong wire kinds are rejected by the
actual Core on the entire input. The source key-success span is derived. -/
theorem bounded_inner_wrong_wire_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (tag : U32) (wire : WireType) (remaining : Nat)
    (capacity : remaining ≤ 4096) (physical : remaining ≤ before.length)
    (fits : before.length-remaining ≤ after.length)
    (modes : state.modes = lane 0) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (depth : state.depth = 0) (inner : state.inner = 255)
    (counter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (wrong : ((tag.val = 1 ∨ tag.val = 2) ∧ wire ≠ .Varint) ∨
      ((tag.val = 3 ∨ tag.val = 4 ∨ tag.val = 5) ∧ wire ≠ .LengthDelimited))
    (sourceSuccess : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,wire),after)) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨native,run,accepted⟩ := native_key_success_varint before after tag wire sourceSuccess
  obtain ⟨leading,byte,tail,span,suffix,bound,terminal,tagEq,knownEq,depthEq,inside,currentModes,currentPositions,decoded⟩ :=
    bounded_varint_terminal state before after native remaining 0 (by decide) capacity physical fits modes positions value inner counter run
  have newTag : Word64.concrete.shift (coreDecoded (feed state leading) byte) 3 = Word64.concrete.const tag.val := by
    rw [decoded]; exact native_key_tag native tag wire accepted
  have kind : Word64.concrete.band (coreDecoded (feed state leading) byte) 7 = Word64.concrete.const (wireNumber wire) := by
    rw [decoded]; exact native_key_kind native tag wire accepted
  have guard : schemaWireMask (feed state leading) byte = 0 := by
    rcases wrong with ⟨known,wrong⟩ | ⟨known,wrong⟩
    · exact scalar_wrong_wire_mask _ byte true tag.val wire known wrong (depthEq.trans depth) inside newTag kind
    · exact bytes_wrong_wire_mask _ byte true tag.val wire known wrong (depthEq.trans depth) inside newTag kind
  rw [span]
  exact rejected_terminal_tail state leading tail byte (core_schema_wire_reject _ byte currentModes terminal guard)

/-- Outer enum/request/response wrong-wire branches reject independently of
payload contents. Native source errors retain their existing dispatcher proof. -/
theorem outer_wrong_wire_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (tag : U32) (wire : WireType)
    (modes : state.modes = lane 0) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (depth : state.depth = 0) (inner : state.inner = 0)
    (wrong : (tag.val = 1 ∧ wire ≠ .Varint) ∨ ((tag.val = 2 ∨ tag.val = 3) ∧ wire ≠ .LengthDelimited))
    (sourceSuccess : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,wire),after)) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨native,run,accepted⟩ := native_key_success_varint before after tag wire sourceSuccess
  obtain ⟨leading,byte,tail,span,suffix,bound,terminal,tagEq,knownEq,depthEq,inside,currentModes,currentPositions,decoded⟩ :=
    outer_varint_terminal state before after native 0 (by decide) modes positions value inner run
  have newTag : Word64.concrete.shift (coreDecoded (feed state leading) byte) 3 = Word64.concrete.const tag.val := by
    rw [decoded]; exact native_key_tag native tag wire accepted
  have kind : Word64.concrete.band (coreDecoded (feed state leading) byte) 7 = Word64.concrete.const (wireNumber wire) := by
    rw [decoded]; exact native_key_kind native tag wire accepted
  have guard : schemaWireMask (feed state leading) byte = 0 := by
    rcases wrong with ⟨known,wrong⟩ | ⟨known,wrong⟩
    · exact scalar_wrong_wire_mask _ byte false tag.val wire known wrong (depthEq.trans depth) inside newTag kind
    · exact bytes_wrong_wire_mask _ byte false tag.val wire known wrong (depthEq.trans depth) inside newTag kind
  rw [span]
  exact rejected_terminal_tail state leading tail byte (core_schema_wire_reject _ byte currentModes terminal guard)

#print axioms bounded_inner_wrong_wire_reject
#print axioms outer_wrong_wire_reject
end ChatResponseReference.StreamingV1
