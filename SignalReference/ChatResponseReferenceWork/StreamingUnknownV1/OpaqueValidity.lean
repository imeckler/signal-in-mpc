import ChatResponseReferenceWork.StreamingUnknownV1.Attempt
import ChatResponseReferenceWork.StreamingV1.OpaqueContext
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

private theorem zero_and (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
private theorem and_zero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
private theorem hot_and (x : BitVec 8) : ByteAuth.concrete.and 255 x = x := BitVec.allOnes_and
private theorem right_hot (x : BitVec 8) : ByteAuth.concrete.and x 255 = x := BitVec.and_allOnes
private theorem not_zero : ByteAuth.concrete.not 0 = 255 := rfl
private theorem not_hot : ByteAuth.concrete.not 255 = 0 := rfl
private theorem either_zero : TlsWebSocketUpgrade.either ByteAuth.concrete 0 0 = 0 := rfl
private theorem either_hot_zero : TlsWebSocketUpgrade.either ByteAuth.concrete 255 0 = 255 := rfl
private theorem either_zero_hot : TlsWebSocketUpgrade.either ByteAuth.concrete 0 255 = 255 := rfl

/-- Arbitrary byte payload preserves actual validity with budget available and a
safe child end: either not closing, or the opaque field ends at depth zero. -/
theorem unknown_opaque_byte_valid (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 3) (kinds : state.kinds = [0,0,0,0])
    (valid : state.valid = 255) (seen : state.seen = 255) (finished : state.finished = 0)
    (budget : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.budget 0 = 0)
    (depth : state.depth = 0)
    (closeSafe : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1 = 0 ∨
      state.skip = BitVec.ofNat 64 1) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.valid = 255 := by
  have p0 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 3) 0 = 0 := rfl
  have p1 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 3) 1 = 0 := rfl
  have p2 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 3) 2 = 0 := rfl
  have p3 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 3) 3 = 255 := rfl
  have active : TlsWebSocketUpgrade.any ByteAuth.concrete ((lane 3).take 3) = 0 := rfl
  have k2 : TlsWebSocketUpgrade.get ByteAuth.concrete [0,0,0,0] 2 = 0 := rfl
  have k3 : TlsWebSocketUpgrade.get ByteAuth.concrete [0,0,0,0] 3 = 0 := rfl
  have depthZero : TlsChatResponse.weq Word64.concrete ByteAuth.concrete 0 0 = 255 := rfl
  rcases closeSafe with notClosing | last
  · simp only [TlsChatResponse.step]
    rw [valid,seen,finished,modes,kinds,budget,notClosing]
    simp only [p0,p1,p2,p3,k2,k3,active,zero_and,and_zero,hot_and,right_hot,not_zero,not_hot,either_zero,Word64.select_reject]
  · have lastMask : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.skip 1 = 255 := by rw [last]; rfl
    simp only [TlsChatResponse.step]
    rw [valid,seen,finished,modes,kinds,budget,depth,lastMask]
    simp only [p0,p1,p2,p3,k2,k3,active,zero_and,and_zero,hot_and,right_hot,not_zero,not_hot,either_zero,Word64.select_reject]
    simp only [TlsWebSocketUpgrade.get,List.getElem?_cons_zero,Option.getD_some,depthZero,
      either_hot_zero,either_zero_hot,zero_and,and_zero,hot_and,right_hot,not_zero,not_hot,either_zero]

#print axioms unknown_opaque_byte_valid
end ChatResponseReference.StreamingUnknownV1
