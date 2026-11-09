import ChatResponseReferenceWork.StreamingUnknownV1.FixedIteration
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def actualFixedOn (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8) : BitVec 8 :=
  TlsWebSocketUpgrade.either ByteAuth.concrete
    (TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7)) 1)
    (TlsChatResponse.weq Word64.concrete ByteAuth.concrete (Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7)) 5)

/-- Actual failed fixed-length guard rejects at the key, independently of other
source/cache validity clauses or payload contents. -/
theorem core_fixed_key_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (modes : state.modes = lane 0) (terminal : VarintDecode.Spqr.terminates byte = true)
    (fixedOn : actualFixedOn state byte = 255) (bad : actualFixedGood state byte = 0) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.valid = 0 := by
  have ended : ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7) = 255 := by rw [terminal_exact byte,terminal]; rfl
  have p0 : TlsWebSocketUpgrade.get ByteAuth.concrete (lane 0) 0 = 255 := rfl
  have hotAnd (x : BitVec 8) : ByteAuth.concrete.and 255 x = x := BitVec.allOnes_and
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  have notZero : ByteAuth.concrete.not 0 = 255 := rfl
  have notHot : ByteAuth.concrete.not 255 = 0 := rfl
  have one : Word64.concrete.const 1 = (1 : BitVec 64) := rfl
  unfold actualFixedOn coreDecoded at fixedOn
  unfold actualFixedGood availableLength coreDecoded at bad
  dsimp only at bad
  simp only [TlsChatResponse.step]
  rw [modes,ended]
  simp only [one,p0,hotAnd]
  rw [fixedOn,bad]
  simp only [hotAnd,notZero,notHot,zeroAnd,andZero]

#print axioms core_fixed_key_reject
end ChatResponseReference.StreamingUnknownV1
