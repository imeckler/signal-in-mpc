import ChatResponseReferenceWork.StreamingUnknownV1.GroupKeyStack
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey

/-- Exact actual terminal depth transition for every native wire class. This
includes rejected-state mutation; validity and matching are separate guards. -/
theorem native_key_depth_transition (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (native : U64) (tag : U32) (wire : WireType) (modes : state.modes = lane 0)
    (terminal : VarintDecode.Spqr.terminates byte = true)
    (decoded : coreDecoded state byte = native.bv) (accepted : keyResult native = .Ok (tag,wire)) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.depth =
      if wireNumber wire = 3 then Word64.concrete.add state.depth 1
      else if wireNumber wire = 4 then Word64.concrete.sub state.depth 1 else state.depth := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by rw [terminal_exact byte,terminal]; rfl
  have kind : Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7) = Word64.concrete.const (wireNumber wire) := by
    rw [decoded]; exact native_key_kind native tag wire accepted
  change Word64.concrete.select
    (ByteAuth.concrete.and (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0)
      (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
      (TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7)) 3))
    (Word64.concrete.add state.depth 1)
    (Word64.concrete.select
      (ByteAuth.concrete.and (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0)
        (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7)))
        (TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7)) 4))
      (Word64.concrete.sub state.depth 1) state.depth) = _
  rw [modes,ended,kind]
  have done : ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete (lane 0) 0) 255 = 255 := rfl
  have hotAnd (x : BitVec 8) : ByteAuth.concrete.and 255 x = x := BitVec.allOnes_and
  have startMask : TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.const (wireNumber wire)) 3 =
      if wireNumber wire = 3 then 255 else 0 := by cases wire <;> rfl
  have endMask : TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.const (wireNumber wire)) 4 =
      if wireNumber wire = 4 then 255 else 0 := by cases wire <;> rfl
  simp only [done,hotAnd,startMask,endMask]
  by_cases starts : wireNumber wire = 3
  · simp only [if_pos starts,Word64.select_accept]
  · simp only [if_neg starts,Word64.select_reject]
    by_cases ends : wireNumber wire = 4
    · simp only [if_pos ends,Word64.select_accept]
    · simp only [if_neg ends,Word64.select_reject]

#print axioms native_key_depth_transition
end ChatResponseReference.StreamingUnknownV1
