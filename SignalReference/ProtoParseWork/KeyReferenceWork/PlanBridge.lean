import ProtoParseWork.KeyReferenceWork.KeyCircuit

namespace LibSignalReference.Candidate.ProstKey
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
set_option maxHeartbeats 400000

private theorem byte_zero_and (x : BitVec 8) : 0 &&& x = 0 := BitVec.zero_and
private theorem byte_and_zero (x : BitVec 8) : x &&& 0 = 0 := BitVec.and_zero
private theorem byte_xor_zero (x : BitVec 8) : x ^^^ 0 = x := BitVec.xor_zero

/-- Invalid wire type6/7 cannot satisfy any actual plan payload branch. -/
theorem plan_invalid_kind (capacity : Nat) (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hk : 5 < (key.value &&& 7).toNat) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 0 := by
  have hkind (n : Nat) (hn : n ≤ 5) :
      Word64.eq Word64.concrete ByteAuth.concrete
        (Word64.concrete.band key.value (Word64.concrete.const 7)) (Word64.concrete.const n) = 0 := by
    rw [word_eq_value]
    apply if_neg
    intro he
    have hh := congrArg BitVec.toNat he
    change (key.value &&& 7).toNat = n % 2^64 at hh
    rw [Nat.mod_eq_of_lt (by omega : n < 2^64)] at hh
    omega
  simp only [ProtoParse.plan]
  simp only [hkind 0 (by decide),hkind 1 (by decide),hkind 2 (by decide),
    hkind 3 (by decide),hkind 4 (by decide),hkind 5 (by decide)]
  simp only [Word64.bor,ByteAuth.concrete,
    byte_zero_and,byte_and_zero,byte_xor_zero]

theorem plan_invalid_value (capacity : Nat) (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (h : ¬(key.value.toNat ≤ 4294967295 ∧ 8 ≤ key.value.toNat ∧ key.value.toNat % 8 ≤ 5)) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 0 := by
  by_cases hr : key.value.toNat ≤ 4294967295
  · by_cases ht : 8 ≤ key.value.toNat
    · apply plan_invalid_kind
      rw [kind_nat]
      omega
    · have hz : (key.value >>> 3) = 0 := (shift_zero _).mpr (by omega)
      have he : Word64.eq Word64.concrete ByteAuth.concrete
          (Word64.concrete.shift key.value 3) (Word64.concrete.const 0) = 255 := by
        rw [word_eq_value]
        exact if_pos hz
      simp only [ProtoParse.plan]
      rw [he]
      change key.ok &&& (_ &&& ((0 : BitVec 8) &&& _)) = 0
      simp only [byte_zero_and,byte_and_zero]
  · have hu : Word64.concrete.ule key.value (Word64.concrete.const 4294967295) = 0 := by
      rw [Word64.ule_value]
      exact if_neg hr
    simp only [ProtoParse.plan]
    rw [hu]
    change key.ok &&& ((0 : BitVec 8) &&& _) = 0
    simp only [byte_zero_and,byte_and_zero]

/-- The existing strict parser rejects every key rejected by this component,
independently of payload, field selection or group state. -/
theorem plan_key_rejects (capacity : Nat) (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (h : (keyFields Word64.concrete ByteAuth.concrete key).ok = 0) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 0 := by
  by_cases hv : key.value.toNat ≤ 4294967295 ∧ 8 ≤ key.value.toNat ∧ key.value.toNat % 8 ≤ 5
  · rw [key_mask,if_pos hv] at h
    have hz : key.ok = 0 := by simpa only [show (255 : BitVec 8) = BitVec.allOnes 8 by rfl,BitVec.and_allOnes] using h
    change key.ok &&& _ = 0
    rw [hz]
    exact BitVec.zero_and
  · exact plan_invalid_value capacity key payload state hv

#print axioms plan_invalid_kind
#print axioms plan_invalid_value
#print axioms plan_key_rejects
end LibSignalReference.Candidate.ProstKey
