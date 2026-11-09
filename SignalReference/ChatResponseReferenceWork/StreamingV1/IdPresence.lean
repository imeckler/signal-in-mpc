import ChatResponseReferenceWork.StreamingV1.ScalarDispatch
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice

/-- The actual ID update sets presence even when the full64 ID value is zero. -/
theorem core_id_present_terminal (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (modes : state.modes = lane 1)
    (known : state.scalarKnown = 255) (inner : state.inner = 255) (tag : state.tag = 1)
    (terminal : VarintDecode.Spqr.terminates byte = true) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.idPresent = 255 := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by
    rw [terminal_exact byte,terminal]; rfl
  have tagMask : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.tag 1 = 255 := by rw [tag]; rfl
  change TlsWebSocketUpgrade.either ByteAuth.concrete state.idPresent
    (ByteAuth.concrete.and
      (ByteAuth.concrete.and
        (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 1)
          (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7))) state.scalarKnown)
      (ByteAuth.concrete.and state.inner (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.tag 1))) = 255
  rw [modes,known,inner,tagMask,ended]
  change TlsWebSocketUpgrade.either ByteAuth.concrete state.idPresent 255 = 255
  unfold TlsWebSocketUpgrade.either
  have notHot : ByteAuth.concrete.not 255 = 0 := rfl
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  rw [notHot,andZero]
  rfl

def IdUpdateSpan (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (expected : BitVec 64) : Prop :=
  ∃ leading byte tail,
    contents before = leading ++ byte::tail ∧ contents after = tail ∧
    let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (feed state leading) byte).state
    next.id = expected ∧ next.idPresent = 255

theorem bounded_scalar_id_full_update (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (remaining : Nat)
    (capacity : remaining ≤ 4096) (physical : remaining ≤ before.length)
    (fits : before.length-remaining ≤ after.length)
    (modes : state.modes = lane 1) (positions : state.positions = oneHot 0) (value : state.value = 0)
    (inner : state.inner = 255) (counter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (known : state.scalarKnown = 255) (tag : state.tag = 1)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    IdUpdateSpan state before after native.bv := by
  obtain ⟨leading,byte,tail,span,suffix,bound,terminal,tagEq,knownEq,inside,currentModes,currentPositions,decoded⟩ :=
    bounded_scalar_terminal state before after native remaining capacity physical fits modes positions value inner counter sourceSuccess
  have result := core_id_terminal (feed state leading) leading.length (by omega) byte currentModes currentPositions
    (knownEq.trans known) inside (tagEq.trans tag) terminal
  refine ⟨leading,byte,tail,span,suffix,result.trans ?_,?_⟩
  · unfold coreDecoded at decoded
    rw [currentPositions,contribution_one_hot leading.length (by omega) byte] at decoded
    exact decoded
  · exact core_id_present_terminal _ byte currentModes (knownEq.trans known) inside (tagEq.trans tag) terminal

#print axioms core_id_present_terminal
#print axioms bounded_scalar_id_full_update
end ChatResponseReference.StreamingV1
