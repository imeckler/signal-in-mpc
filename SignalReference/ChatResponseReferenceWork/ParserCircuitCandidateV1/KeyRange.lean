import ChatResponseReferenceWork.ParserCircuitCandidateV1.ControlMasks
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def decodedValue (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8) : BitVec 64 :=
  VarintDecode.Spqr.concrete.orWord state.value (TlsChatResponse.contribution VarintDecode.Spqr.concrete ByteAuth.concrete state.positions byte)
def keyActivity (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8) : BitVec 8 :=
  ByteAuth.concrete.and (TlsWebSocketUpgrade.get ByteAuth.concrete state.modes 0)
    (ByteAuth.concrete.not (ByteAuth.concrete.maskBit byte 7))

/-- Malformed key range can write a high tag into rejected intermediate scratch;
this theorem preserves its rejection rather than assuming all writes are narrow. -/
theorem key_range_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (active : keyActivity state byte = 255) (tooLarge : 4294967295 < (decodedValue state byte).toNat) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.valid = 0 := by
  have range : Word64.concrete.ule (decodedValue state byte) (Word64.concrete.const 4294967295) = 0 := by
    rw [Word64.ule_value]
    exact if_neg (by simpa only [show (Word64.concrete.const 4294967295).toNat = 4294967295 from rfl] using Nat.not_le_of_gt tooLarge)
  change ByteAuth.concrete.and state.valid
    (ByteAuth.concrete.and state.seen (ByteAuth.concrete.and (ByteAuth.concrete.not state.finished)
      (ByteAuth.concrete.and _ (ByteAuth.concrete.and _
        (ByteAuth.concrete.and
          (ByteAuth.concrete.not (ByteAuth.concrete.and (keyActivity state byte)
            (ByteAuth.concrete.not (ByteAuth.concrete.and
              (Word64.concrete.ule (decodedValue state byte) (Word64.concrete.const 4294967295)) _)))) _))))) = 0
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  have notZero : ByteAuth.concrete.not 0 = 255 := rfl
  have hot : ByteAuth.concrete.and 255 255 = 255 := rfl
  have notHot : ByteAuth.concrete.not 255 = 0 := rfl
  rw [range,zeroAnd,active,notZero,hot,notHot]
  simp only [zeroAnd,andZero]

theorem nonrejected_key_tag_narrow (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (active : keyActivity state byte = 255)
    (valid : (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.valid ≠ 0) :
    NarrowWord (Word64.concrete.shift (decodedValue state byte) 3) := by
  have range : (decodedValue state byte).toNat ≤ 4294967295 := by
    by_cases large : 4294967295 < (decodedValue state byte).toNat
    · exact False.elim (valid (key_range_reject state byte active large))
    · omega
  apply narrow_of_bound
  change ((decodedValue state byte) >>> 3).toNat < 2^32
  rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  have bound := Nat.div_le_self (decodedValue state byte).toNat (2^3)
  omega

#print axioms key_range_reject
#print axioms nonrejected_key_tag_narrow
end ChatResponseReference.ParserCircuitCandidateV1
