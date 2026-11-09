import ChatResponseReferenceWork.StreamingV1.BoundedTerminal
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkipKey

/-- Actual key success grounds both the actual varint execution and the actual
post-varint native validation. The key validator does not move the cursor. -/
theorem native_key_success_varint (before after : Slice U8) (tag : U32) (wire : WireType)
    (sourceSuccess : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,wire),after)) :
    ∃ native,
      LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after) ∧
      keyResult native = .Ok (tag,wire) := by
  obtain ⟨decoded,suffix,run,_,_,keyRun⟩ := decode_key_reference before
  rw [sourceSuccess] at keyRun
  cases decoded with
  | Err error => simp [finishResult] at keyRun
  | Ok native =>
    have accepted : keyResult native = .Ok (tag,wire) := (congrArg Prod.fst (Result.ok.inj keyRun)).symm
    have suffixEq : after = suffix := congrArg Prod.snd (Result.ok.inj keyRun)
    rw [←suffixEq] at run
    exact ⟨native,run,accepted⟩

/-- Successful native key dispatch inside the bounded response installs the
actual source ID/status scalar flag and body/message/header kind flags. -/
theorem bounded_inner_key_recognition (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (tag : U32) (wire : WireType) (remaining : Nat)
    (capacity : remaining ≤ 4096) (physical : remaining ≤ before.length)
    (fits : before.length-remaining ≤ after.length)
    (modes : state.modes = lane 0) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (depth : state.depth = 0) (inner : state.inner = 255)
    (counter : state.responseRemaining = BitVec.ofNat 64 remaining) (shape : state.kinds.length = 4)
    (sourceSuccess : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,wire),after)) :
    ∃ leading byte tail,
      contents before = leading ++ byte::tail ∧ contents after = tail ∧
      let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
        (feed state leading) byte).state
      next.scalarKnown = (if tag.val = 1 ∨ tag.val = 2 then 255 else 0) ∧
      next.kinds = [0,if tag.val = 4 then 255 else 0,if tag.val = 3 then 255 else 0,if tag.val = 5 then 255 else 0] := by
  obtain ⟨native,run,accepted⟩ := native_key_success_varint before after tag wire sourceSuccess
  obtain ⟨leading,byte,tail,span,suffix,bound,terminal,tagEq,knownEq,depthEq,inside,currentModes,currentPositions,decoded⟩ :=
    bounded_varint_terminal state before after native remaining 0 (by decide) capacity physical fits modes positions value inner counter run
  have newTag : Word64.concrete.shift (coreDecoded (feed state leading) byte) 3 = BitVec.ofNat 64 tag.val := by
    rw [decoded]
    exact native_key_tag native tag wire accepted
  have scalar := key_scalar_recognition (feed state leading) byte tag true currentModes (depthEq.trans depth) inside terminal newTag
  have kinds := key_field_recognition (feed state leading) byte tag true currentModes (depthEq.trans depth) inside
    (feed_kinds_shape state leading shape) terminal newTag
  exact ⟨leading,byte,tail,span,suffix,scalar,kinds⟩

/-- The corresponding actual source enum/response classification at the outer
message boundary; source request presence is a separate validation condition. -/
theorem outer_key_recognition (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (tag : U32) (wire : WireType)
    (modes : state.modes = lane 0) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (depth : state.depth = 0) (inner : state.inner = 0) (shape : state.kinds.length = 4)
    (sourceSuccess : LoopSupportSkip.encoding.decode_key sliceBuf before = .ok (.Ok (tag,wire),after)) :
    ∃ leading byte tail,
      contents before = leading ++ byte::tail ∧ contents after = tail ∧
      let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
        (feed state leading) byte).state
      next.scalarKnown = (if tag.val = 1 then 255 else 0) ∧
      next.kinds = [if tag.val = 3 then 255 else 0,0,0,0] := by
  obtain ⟨native,run,accepted⟩ := native_key_success_varint before after tag wire sourceSuccess
  obtain ⟨leading,byte,tail,span,suffix,bound,terminal,tagEq,knownEq,depthEq,inside,currentModes,currentPositions,decoded⟩ :=
    outer_varint_terminal state before after native 0 (by decide) modes positions value inner run
  have newTag : Word64.concrete.shift (coreDecoded (feed state leading) byte) 3 = BitVec.ofNat 64 tag.val := by
    rw [decoded]
    exact native_key_tag native tag wire accepted
  have scalar := key_scalar_recognition (feed state leading) byte tag false currentModes (depthEq.trans depth) inside terminal newTag
  have kinds := key_field_recognition (feed state leading) byte tag false currentModes (depthEq.trans depth) inside
    (feed_kinds_shape state leading shape) terminal newTag
  exact ⟨leading,byte,tail,span,suffix,scalar,kinds⟩

#print axioms native_key_success_varint
#print axioms bounded_inner_key_recognition
#print axioms outer_key_recognition
end ChatResponseReference.StreamingV1
