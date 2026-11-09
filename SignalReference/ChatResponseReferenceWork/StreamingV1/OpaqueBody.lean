import ChatResponseReferenceWork.StreamingV1.ScalarFieldRefinement
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 1000000

/-- Arbitrary body bytes are emitted under exactly the actual next-valid mask;
body payload is not interpreted as keys, scalar values or UTF8. -/
theorem opaque_body_event (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 3) (kinds : state.kinds = [0,255,0,0]) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).bodyData =
      (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.valid := by
  change ByteAuth.concrete.and _ (ByteAuth.concrete.and
    (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 3)
    (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 1)) = _
  have body : ByteAuth.concrete.and
      (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 3)
      (TlsWebSocketUpgrade.get ByteAuth.concrete state.kinds 1) = 255 := by rw [modes,kinds]; rfl
  rw [body]
  have hot (x : BitVec 8) : ByteAuth.concrete.and x 255 = x := BitVec.and_allOnes
  exact hot _

/-- Actual opaque input consumes one payload byte regardless of its high bit. -/
theorem opaque_skip_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 3) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.skip =
      Word64.concrete.sub state.skip 1 := by
  change Word64.concrete.select
    (ByteAuth.concrete.and
      (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0) _) _) _
    (Word64.concrete.select
      (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2) _) _
      (Word64.concrete.select (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 3)
        (Word64.concrete.sub state.skip 1) state.skip)) = _
  rw [modes]
  have keyOff : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 3) 0 = 0 := rfl
  have lengthOff : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 3) 2 = 0 := rfl
  have bytesOn : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 3) 3 = 255 := rfl
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  rw [keyOff,lengthOff,bytesOn]
  simp only [zeroAnd,Word64.select_reject,Word64.select_accept]

/-- At the last opaque byte Core returns to key mode; all prior opaque bytes
remain opaque. This applies to fixed skips and all byte/string field payloads. -/
theorem opaque_mode_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 3) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.modes =
      if state.skip = BitVec.ofNat 64 1 then lane 0 else lane 3 := by
  have ends : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.skip 1 =
      if state.skip = BitVec.ofNat 64 1 then 255 else 0 := by unfold TlsChatResponse.weq; rw [word_eq_value]; rfl
  simp only [TlsChatResponse.step]
  rw [modes,ends]
  by_cases last : state.skip = BitVec.ofNat 64 1 <;>
    simp [last,lane,TlsWebSocketUpgrade.get,TlsWebSocketUpgrade.either,ByteAuth.concrete,Word64.concrete] <;> rfl

#print axioms opaque_body_event
#print axioms opaque_skip_step
#print axioms opaque_mode_step
end ChatResponseReference.StreamingV1
