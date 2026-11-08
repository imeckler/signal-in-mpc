import ProtoParseWork.FullParserV3Work.FieldErrorProjection
import ProtoParseWork.FullParserV3Work.KnownMessageScan
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipKey
open SignalMessageIntegration DispatcherIntegration
set_option maxHeartbeats 3000000

private theorem choose_accept (x y : BitVec 8) : Unpad.chooseByte ByteAuth.concrete 255 x y = x := by
  change ((255 : BitVec 8) &&& (x ^^^ y)) ^^^ y = x
  simp only [show (255 : BitVec 8) = BitVec.allOnes 8 from rfl,BitVec.allOnes_and,BitVec.xor_assoc,BitVec.xor_self,BitVec.xor_zero]
private theorem choose_reject (x y : BitVec 8) : Unpad.chooseByte ByteAuth.concrete 0 x y = y := by
  change ((0 : BitVec 8) &&& (x ^^^ y)) ^^^ y = y
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and]
  have hz : (0 : BitVec 8).getLsbD i = false := by simp [BitVec.getLsbD]
  rw [hz]
  cases y.getLsbD i <;> rfl

theorem valid_known_scalar_wrong (key : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hd : state.depth = 0)
    (ht : key.value >>> 3 = 2 ∨ key.value >>> 3 = 3) (hk : key.value &&& 7 ≠ 0) : validKnownMask key state = 0 := by
  have htop : Word64.eq Word64.concrete ByteAuth.concrete state.depth 0 = 255 := by rw [hd,word_eq_value]; exact if_pos rfl
  have htag : Word64.concrete.ule (key.value >>> 3) 6 = 255 := by rcases ht with h | h <;> simp only [h] <;> decide
  have hscalar : Word64.bor ByteAuth.concrete (Word64.eq Word64.concrete ByteAuth.concrete (key.value >>> 3) 2)
      (Word64.eq Word64.concrete ByteAuth.concrete (key.value >>> 3) 3) = 255 := by rcases ht with h | h <;> simp only [h] <;> decide
  have hkind : Word64.eq Word64.concrete ByteAuth.concrete (key.value &&& 7) 0 = 0 := by rw [word_eq_value]; exact if_neg hk
  unfold validKnownMask
  rw [htop,htag,hscalar,hkind,choose_accept]
  rfl

theorem valid_known_bytes_wrong (key : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hd : state.depth = 0)
    (ht : key.value >>> 3 = 1 ∨ key.value >>> 3 = 4 ∨ key.value >>> 3 = 5 ∨ key.value >>> 3 = 6)
    (hk : key.value &&& 7 ≠ 2) : validKnownMask key state = 0 := by
  have htop : Word64.eq Word64.concrete ByteAuth.concrete state.depth 0 = 255 := by rw [hd,word_eq_value]; exact if_pos rfl
  have htag : Word64.concrete.ule (key.value >>> 3) 6 = 255 := by rcases ht with h | h | h | h <;> simp only [h] <;> decide
  have hscalar : Word64.bor ByteAuth.concrete (Word64.eq Word64.concrete ByteAuth.concrete (key.value >>> 3) 2)
      (Word64.eq Word64.concrete ByteAuth.concrete (key.value >>> 3) 3) = 0 := by rcases ht with h | h | h | h <;> simp only [h] <;> decide
  have hkind : Word64.eq Word64.concrete ByteAuth.concrete (key.value &&& 7) 2 = 0 := by rw [word_eq_value]; exact if_neg hk
  unfold validKnownMask
  rw [htop,htag,hscalar,hkind,choose_reject]
  rfl

namespace Observed

theorem scalar_wrong_parameter (key : ProtoParse.Decoded (BitVec 8) (BitVec 64)) (tag : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (ht : ScalarTag tag)
    (htag : key.value >>> 3 = BitVec.ofNat 64 tag.val) (hkind : key.value &&& 7 = BitVec.ofNat 64 (LibSignalReference.Candidate.ProstSkipKey.wireNumber kind)) :
    statusView (.Err (fieldError (LibSignalReference.Candidate.ProstField.decodeError
      (.UnexpectedWireType (toFieldWire (signalWire kind)) .Varint)))) = some (⟨5,wirePair key⟩ : ErrorMeta (BitVec 64)) := by
  unfold wirePair
  change _ = some (⟨5,(key.value &&& (7 : BitVec 64)) + Word64.concrete.select
    (Word64.bor ByteAuth.concrete (Word64.eq Word64.concrete ByteAuth.concrete (key.value >>> 3) 2)
      (Word64.eq Word64.concrete ByteAuth.concrete (key.value >>> 3) 3)) 0 16⟩ : ErrorMeta (BitVec 64))
  rw [htag,hkind]
  rcases ht with rfl | rfl
  all_goals cases kind <;> rfl

theorem bytes_wrong_parameter (key : ProtoParse.Decoded (BitVec 8) (BitVec 64)) (tag : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (ht : BytesTag tag)
    (htag : key.value >>> 3 = BitVec.ofNat 64 tag.val) (hkind : key.value &&& 7 = BitVec.ofNat 64 (LibSignalReference.Candidate.ProstSkipKey.wireNumber kind)) :
    statusView (.Err (LibSignalReference.Candidate.ProstBytes.decodeError
      (.UnexpectedWireType (toBytesWire (signalWire kind)) .LengthDelimited))) = some (⟨5,wirePair key⟩ : ErrorMeta (BitVec 64)) := by
  unfold wirePair
  change _ = some (⟨5,(key.value &&& (7 : BitVec 64)) + Word64.concrete.select
    (Word64.bor ByteAuth.concrete (Word64.eq Word64.concrete ByteAuth.concrete (key.value >>> 3) 2)
      (Word64.eq Word64.concrete ByteAuth.concrete (key.value >>> 3) 3)) 0 16⟩ : ErrorMeta (BitVec 64))
  rw [htag,hkind]
  rcases ht with rfl | rfl | rfl | rfl
  all_goals cases kind <;> rfl

#print axioms scalar_wrong_parameter
#print axioms bytes_wrong_parameter
end Observed
#print axioms valid_known_scalar_wrong
#print axioms valid_known_bytes_wrong
end FullParserV3
