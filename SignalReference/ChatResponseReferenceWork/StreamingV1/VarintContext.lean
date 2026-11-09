import ChatResponseReferenceWork.StreamingV1.ScalarRecognition
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
set_option maxHeartbeats 1000000

private theorem terminal_zero (byte : BitVec 8) (continues : VarintDecode.Spqr.terminates byte = false) :
    ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 0 := by rw [terminal_exact byte,continues]; rfl
private theorem and_zero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
private theorem zero_and (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and

theorem nonterminal_tag (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (continues : VarintDecode.Spqr.terminates byte = false) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.tag = state.tag := by
  change Word64.concrete.select
    (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0)
      (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7))) _ state.tag = state.tag
  rw [terminal_zero byte continues,and_zero,Word64.select_reject]

theorem nonterminal_known (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (continues : VarintDecode.Spqr.terminates byte = false) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.scalarKnown = state.scalarKnown := by
  change TlsInner.select ByteAuth.concrete
    (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0)
      (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7))) _ state.scalarKnown = state.scalarKnown
  rw [terminal_zero byte continues,and_zero,TlsInner.select_reject]

theorem nonterminal_inner (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (continues : VarintDecode.Spqr.terminates byte = false)
    (notClosing : ByteAuth.concrete.and state.inner
      (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1) = 0) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.inner = state.inner := by
  change TlsInner.select ByteAuth.concrete
    (ByteAuth.concrete.and
      (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2)
        (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7))) _ ) _
    (TlsInner.select ByteAuth.concrete
      (ByteAuth.concrete.and state.inner (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1)) 0 state.inner) = state.inner
  rw [terminal_zero byte continues,and_zero,zero_and,notClosing,TlsInner.select_reject,TlsInner.select_reject]

theorem nonterminal_remaining (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (continues : VarintDecode.Spqr.terminates byte = false) (inner : state.inner = 255) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.responseRemaining =
      Word64.concrete.sub state.responseRemaining 1 := by
  change Word64.concrete.select
    (ByteAuth.concrete.and
      (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 2)
        (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7))) _ ) _
    (Word64.concrete.select state.inner (Word64.concrete.sub state.responseRemaining 1) state.responseRemaining) = _
  rw [terminal_zero byte continues,and_zero,zero_and,inner,Word64.select_reject,Word64.select_accept]

theorem nonterminal_depth (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (continues : VarintDecode.Spqr.terminates byte = false) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.depth = state.depth := by
  change Word64.concrete.select
    (ByteAuth.concrete.and
      (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0)
        (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7))) _) _
    (Word64.concrete.select
      (ByteAuth.concrete.and
        (ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0)
          (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7))) _) _ state.depth) = state.depth
  rw [terminal_zero byte continues,and_zero,zero_and,zero_and,Word64.select_reject,Word64.select_reject]

#print axioms nonterminal_tag
#print axioms nonterminal_known
#print axioms nonterminal_inner
#print axioms nonterminal_remaining
#print axioms nonterminal_depth
end ChatResponseReference.StreamingV1
