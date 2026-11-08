import ProtoParseWork.FullParserV3Work.PayloadErrorProjection
import ProtoParseWork.FullParserV3Work.NonPayloadPlan
open TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 3000000

def skipErrorCode (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) : BitVec 64 :=
  let kind := key.value &&& 7
  let isKind := fun n => Word64.eq Word64.concrete ByteAuth.concrete kind (BitVec.ofNat 64 n)
  Word64.concrete.select (isKind 4) 8 (Word64.concrete.select (Word64.concrete.ule state.depth 99)
    (Word64.concrete.select (Word64.bor ByteAuth.concrete (isKind 0) (isKind 2))
      (Word64.concrete.select payload.ok 6 1) 6) 7)

def wirePair (key : ProtoParse.Decoded (BitVec 8) (BitVec 64)) : BitVec 64 :=
  (key.value &&& 7) + Word64.concrete.select (Word64.bor ByteAuth.concrete
    (Word64.eq Word64.concrete ByteAuth.concrete (key.value >>> 3) 2)
    (Word64.eq Word64.concrete ByteAuth.concrete (key.value >>> 3) 3)) 0 16

def fieldClassify (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) : ErrorMeta (BitVec 64) :=
  let wrong := ByteAuth.concrete.and (ByteAuth.concrete.and
    (Word64.eq Word64.concrete ByteAuth.concrete state.depth 0) (Word64.concrete.ule (key.value >>> 3) 6))
    (ByteAuth.concrete.not (Unpad.chooseByte ByteAuth.concrete
      (Word64.bor ByteAuth.concrete (Word64.eq Word64.concrete ByteAuth.concrete (key.value >>> 3) 2)
        (Word64.eq Word64.concrete ByteAuth.concrete (key.value >>> 3) 3))
      (Word64.eq Word64.concrete ByteAuth.concrete (key.value &&& 7) 0)
      (Word64.eq Word64.concrete ByteAuth.concrete (key.value &&& 7) 2)))
  ⟨Word64.concrete.select wrong 5 (skipErrorCode key payload state),Word64.concrete.select wrong (wirePair key) 0⟩

/-- Header validation is erased only after all its checks are proved true;
the remaining field classifier preserves the exact constructor parameter. -/
theorem classify_valid_header (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hk : key.ok = 255)
    (hr : key.value.toNat ≤ 4294967295) (ht : key.value >>> 3 ≠ 0) (hkind : (key.value &&& 7).toNat ≤ 5) :
    classify Word64.concrete ByteAuth.concrete key payload state = fieldClassify key payload state := by
  have hrange : Word64.concrete.ule key.value (Word64.concrete.const 4294967295) = 255 := by rw [Word64.ule_value]; exact if_pos hr
  have htag : Word64.eq Word64.concrete ByteAuth.concrete (Word64.concrete.shift key.value 3) (Word64.concrete.const 0) = 0 := by rw [word_eq_value]; exact if_neg ht
  have hvalid : Word64.concrete.ule (Word64.concrete.band key.value (Word64.concrete.const 7)) (Word64.concrete.const 5) = 255 := by rw [Word64.ule_value]; exact if_pos hkind
  dsimp only [classify]
  simp only [hk,hrange,htag,hvalid,Word64.select_accept,Word64.select_reject]
  rfl

theorem field_classify_wrong_wire (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hv : validKnownMask key state = 0) :
    fieldClassify key payload state = ⟨5,wirePair key⟩ := by
  unfold fieldClassify
  rw [wrong_is_not_valid]
  change (⟨Word64.concrete.select (ByteAuth.concrete.not (validKnownMask key state)) 5 _,
    Word64.concrete.select (ByteAuth.concrete.not (validKnownMask key state)) _ 0⟩ : ErrorMeta (BitVec 64)) = _
  rw [hv]
  simp only [show ByteAuth.concrete.not 0 = 255 from rfl,Word64.select_accept]

theorem field_classify_known_wire (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hv : validKnownMask key state = 255) :
    fieldClassify key payload state = ⟨skipErrorCode key payload state,0⟩ := by
  unfold fieldClassify
  rw [wrong_is_not_valid]
  change (⟨Word64.concrete.select (ByteAuth.concrete.not (validKnownMask key state)) 5 _,
    Word64.concrete.select (ByteAuth.concrete.not (validKnownMask key state)) _ 0⟩ : ErrorMeta (BitVec 64)) = _
  rw [hv]
  simp only [show ByteAuth.concrete.not 255 = 0 from rfl,Word64.select_reject]

theorem skip_code_recursion (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (h4 : key.value &&& 7 ≠ 4) (hd : 99 < state.depth.toNat) :
    skipErrorCode key payload state = 7 := by
  have hk : Word64.eq Word64.concrete ByteAuth.concrete (key.value &&& 7) (BitVec.ofNat 64 4) = 0 := by rw [word_eq_value]; exact if_neg h4
  have hl : Word64.concrete.ule state.depth 99 = 0 := by rw [Word64.ule_value]; exact if_neg (by change ¬state.depth.toNat ≤ 99; omega)
  simp only [skipErrorCode,hk,hl,Word64.select_reject]

theorem skip_code_end (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (h4 : key.value &&& 7 = 4) : skipErrorCode key payload state = 8 := by
  have hk : Word64.eq Word64.concrete ByteAuth.concrete (key.value &&& 7) (BitVec.ofNat 64 4) = 255 := by rw [word_eq_value]; exact if_pos h4
  simp only [skipErrorCode,hk,Word64.select_accept]

theorem skip_code_fixed (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hkind : key.value &&& 7 = 1 ∨ key.value &&& 7 = 5)
    (hd : state.depth.toNat ≤ 99) : skipErrorCode key payload state = 6 := by
  have h0 : Word64.eq Word64.concrete ByteAuth.concrete (key.value &&& 7) (BitVec.ofNat 64 0) = 0 := by rw [word_eq_value]; apply if_neg; rcases hkind with h | h <;> rw [h] <;> decide
  have h2 : Word64.eq Word64.concrete ByteAuth.concrete (key.value &&& 7) (BitVec.ofNat 64 2) = 0 := by rw [word_eq_value]; apply if_neg; rcases hkind with h | h <;> rw [h] <;> decide
  have h4 : Word64.eq Word64.concrete ByteAuth.concrete (key.value &&& 7) (BitVec.ofNat 64 4) = 0 := by rw [word_eq_value]; apply if_neg; rcases hkind with h | h <;> rw [h] <;> decide
  have hl : Word64.concrete.ule state.depth 99 = 255 := by rw [Word64.ule_value]; exact if_pos hd
  simp only [skipErrorCode,h0,h2,h4,hl,Word64.bor,show ByteAuth.concrete.and 0 0 = 0 from rfl,
    show ByteAuth.concrete.xor 0 0 = 0 from rfl,Word64.select_reject,Word64.select_accept]

theorem skip_code_length_underflow (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hkind : key.value &&& 7 = 2)
    (hd : state.depth.toNat ≤ 99) (hp : payload.ok = 255) : skipErrorCode key payload state = 6 := by
  have h0 : Word64.eq Word64.concrete ByteAuth.concrete (key.value &&& 7) (BitVec.ofNat 64 0) = 0 := by rw [word_eq_value]; apply if_neg; rw [hkind]; decide
  have h2 : Word64.eq Word64.concrete ByteAuth.concrete (key.value &&& 7) (BitVec.ofNat 64 2) = 255 := by rw [word_eq_value]; exact if_pos hkind
  have h4 : Word64.eq Word64.concrete ByteAuth.concrete (key.value &&& 7) (BitVec.ofNat 64 4) = 0 := by rw [word_eq_value]; apply if_neg; rw [hkind]; decide
  have hl : Word64.concrete.ule state.depth 99 = 255 := by rw [Word64.ule_value]; exact if_pos hd
  simp only [skipErrorCode,h0,h2,h4,hl,hp,Word64.bor,show ByteAuth.concrete.and 0 255 = 0 from rfl,
    show ByteAuth.concrete.xor 0 255 = 255 from rfl,show ByteAuth.concrete.xor 255 0 = 255 from rfl,
    Word64.select_reject,Word64.select_accept]

#print axioms classify_valid_header
#print axioms field_classify_wrong_wire
#print axioms field_classify_known_wire
#print axioms skip_code_recursion
#print axioms skip_code_end
#print axioms skip_code_fixed
#print axioms skip_code_length_underflow
end FullParserV3.Observed
