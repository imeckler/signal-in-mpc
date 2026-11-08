import ProtoParseWork.FullParserV3Work.PayloadFailureCursor
import ProtoParseWork.FullParserV3Work.ErrorProjection
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 3000000

theorem wrong_is_not_valid (known expected : BitVec 8) : ByteAuth.concrete.and known (ByteAuth.concrete.not expected) =
    ByteAuth.concrete.not (Word64.bor ByteAuth.concrete (ByteAuth.concrete.not known) expected) := by
  change known &&& ~~~expected = ~~~((~~~known ^^^ expected) ^^^ (~~~known &&& expected))
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases known.getLsbD i <;> cases expected.getLsbD i <;> rfl

/-- Exact InvalidVarint constructor/payload classification after a valid header,
with actual known-wire acceptance and recursion budget checked independently. -/
theorem classify_payload_varint_error (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hk : key.ok = 255)
    (hr : key.value.toNat ≤ 4294967295) (ht : key.value >>> 3 ≠ 0)
    (hkind : key.value &&& 7 = 0 ∨ key.value &&& 7 = 2)
    (hd : state.depth.toNat ≤ 99) (hv : validKnownMask key state = 255) (hp : payload.ok = 0) :
    classify Word64.concrete ByteAuth.concrete key payload state = ⟨1,0⟩ := by
  have hrange : Word64.concrete.ule key.value (Word64.concrete.const 4294967295) = 255 := by rw [Word64.ule_value]; exact if_pos hr
  have htag : Word64.eq Word64.concrete ByteAuth.concrete (Word64.concrete.shift key.value 3) (Word64.concrete.const 0) = 0 := by rw [word_eq_value]; exact if_neg ht
  have hvalid : Word64.concrete.ule (Word64.concrete.band key.value (Word64.concrete.const 7)) (Word64.concrete.const 5) = 255 := by
    change Word64.concrete.ule (key.value &&& 7) 5 = 255
    rcases hkind with h | h <;> simp only [h] <;> decide
  have hbelow : Word64.concrete.ule state.depth (Word64.concrete.const 99) = 255 := by rw [Word64.ule_value]; exact if_pos hd
  have h4 : Word64.eq Word64.concrete ByteAuth.concrete (Word64.concrete.band key.value (Word64.concrete.const 7)) (Word64.concrete.const 4) = 0 := by
    change Word64.eq Word64.concrete ByteAuth.concrete (key.value &&& 7) 4 = 0
    rcases hkind with h | h <;> simp only [h] <;> decide
  have h01 : Word64.bor ByteAuth.concrete
      (Word64.eq Word64.concrete ByteAuth.concrete (Word64.concrete.band key.value (Word64.concrete.const 7)) (Word64.concrete.const 0))
      (Word64.eq Word64.concrete ByteAuth.concrete (Word64.concrete.band key.value (Word64.concrete.const 7)) (Word64.concrete.const 2)) = 255 := by
    change Word64.bor ByteAuth.concrete (Word64.eq Word64.concrete ByteAuth.concrete (key.value &&& 7) 0)
      (Word64.eq Word64.concrete ByteAuth.concrete (key.value &&& 7) 2) = 255
    rcases hkind with h | h <;> simp only [h] <;> decide
  have hwrong : ByteAuth.concrete.and (ByteAuth.concrete.and
      (Word64.eq Word64.concrete ByteAuth.concrete state.depth (Word64.concrete.const 0))
      (Word64.concrete.ule (Word64.concrete.shift key.value 3) (Word64.concrete.const 6)))
      (ByteAuth.concrete.not (Unpad.chooseByte ByteAuth.concrete
        (Word64.bor ByteAuth.concrete
          (Word64.eq Word64.concrete ByteAuth.concrete (Word64.concrete.shift key.value 3) (Word64.concrete.const 2))
          (Word64.eq Word64.concrete ByteAuth.concrete (Word64.concrete.shift key.value 3) (Word64.concrete.const 3)))
        (Word64.eq Word64.concrete ByteAuth.concrete (Word64.concrete.band key.value (Word64.concrete.const 7)) (Word64.concrete.const 0))
        (Word64.eq Word64.concrete ByteAuth.concrete (Word64.concrete.band key.value (Word64.concrete.const 7)) (Word64.concrete.const 2)))) = 0 := by
    rw [wrong_is_not_valid]
    change ByteAuth.concrete.not (validKnownMask key state) = 0
    rw [hv]
    rfl
  dsimp only [classify]
  simp only [hk,hrange,htag,hvalid,hbelow,h4,h01,hwrong,hp,Word64.select_accept,Word64.select_reject]
  rfl

#print axioms wrong_is_not_valid
#print axioms classify_payload_varint_error
end FullParserV3.Observed
