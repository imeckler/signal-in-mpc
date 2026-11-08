import ProtoParseWork.FullParserV3Work.PlanFailure
open TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 2000000

private theorem and_zero_left (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
private theorem and_zero_right (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero

theorem plan_invalid_range (capacity : Nat) (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hr : 4294967295 < key.value.toNat) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 0 := by
  have he : Word64.concrete.ule key.value (Word64.concrete.const 4294967295) = 0 := by
    rw [Word64.ule_value]; exact if_neg (by change ¬key.value.toNat ≤ 4294967295; omega)
  simp only [ProtoParse.plan,he,and_zero_left,and_zero_right]

theorem plan_invalid_tag (capacity : Nat) (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (ht : key.value >>> 3 = 0) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 0 := by
  have he : Word64.eq Word64.concrete ByteAuth.concrete (Word64.concrete.shift key.value 3) (Word64.concrete.const 0) = 255 := by
    rw [word_eq_value]; exact if_pos ht
  have hn : ByteAuth.concrete.not 255 = 0 := rfl
  simp only [ProtoParse.plan,he,hn,and_zero_left,and_zero_right]

theorem plan_invalid_wire (capacity : Nat) (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hw : 5 < key.value.toNat % 8) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 0 := by
  have hkind (n : Nat) (hn : n ≤ 5) :
      Word64.eq Word64.concrete ByteAuth.concrete (Word64.concrete.band key.value (Word64.concrete.const 7)) (Word64.concrete.const n) = 0 := by
    rw [word_eq_value]
    apply if_neg
    intro he
    have hv := congrArg BitVec.toNat he
    change (key.value &&& 7).toNat = (BitVec.ofNat 64 n).toNat at hv
    rw [kind_nat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at hv
    omega
  simp only [ProtoParse.plan,hkind 0 (by decide),hkind 1 (by decide),hkind 2 (by decide),
    hkind 3 (by decide),hkind 4 (by decide),hkind 5 (by decide),and_zero_left,and_zero_right,
    Word64.bor,show ByteAuth.concrete.xor 0 0 = 0 from rfl]

theorem bad_key_plan (capacity : Nat) (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hb : ¬(key.value.toNat ≤ 4294967295 ∧ 8 ≤ key.value.toNat ∧ key.value.toNat % 8 ≤ 5)) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 0 := by
  by_cases hr : key.value.toNat ≤ 4294967295
  · by_cases ht : 8 ≤ key.value.toNat
    · exact plan_invalid_wire capacity key payload state (by omega)
    · exact plan_invalid_tag capacity key payload state ((shift_zero key.value).mpr (by omega))
  · exact plan_invalid_range capacity key payload state (by omega)

/-- Failed key validation consumes its successful varint and cannot initialize a
message field, regardless of the low tag bits of an invalid over-wide key. -/
theorem key_validation_plan_cursor (capacity position : Nat) (lastClear : BitVec 8)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hk : key.ok = 255)
    (hb : ¬(key.value.toNat ≤ 4294967295 ∧ 8 ≤ key.value.toNat ∧ key.value.toNat % 8 ≤ 5)) :
    let p := ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete capacity position lastClear key payload state
    p.ok = 0 ∧ p.tag = 0 ∧ p.stop = key.stop := by
  have hp := bad_key_plan capacity key payload state hb
  have hm : (keyFields Word64.concrete ByteAuth.concrete key).ok = 0 := by
    rw [key_mask,hk,if_neg hb]
    rfl
  have hkey : ByteAuth.concrete.and key.ok
      (ByteAuth.concrete.and (Word64.concrete.ule key.value (Word64.concrete.const 4294967295))
        (ByteAuth.concrete.and (ByteAuth.concrete.not (Word64.eq Word64.concrete ByteAuth.concrete
          (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).tag (Word64.concrete.const 0)))
          (Word64.concrete.ule (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).kind (Word64.concrete.const 5)))) = 0 := hm
  dsimp only [ProtoParse.planWithCursor]
  simp only [hp,hkey,and_zero_left,Word64.select_reject]
  rw [hk]
  simp only [Word64.select_accept]
  simp
  rfl

#print axioms bad_key_plan
#print axioms key_validation_plan_cursor
end FullParserV3
