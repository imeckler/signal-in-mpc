import TopFieldWork.Fields

namespace LibSignalReference.Candidate.ProstTopField
open TlsMpc TlsMpc.Signal
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 500000

theorem fixed64_unknown_top (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hkey : key.ok = 255) (hvalue : key.value.toNat ≤ 4294967295)
    (htag : key.value >>> 3 ≠ 0) (hkind : key.value &&& 7 = 1)
    (hdepth : state.depth = 0) (hunknown : 6 < (key.value >>> 3).toNat) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok =
      Word64.concrete.ule (key.stop + 8) (BitVec.ofNat 64 capacity) := by
  have hu : Word64.concrete.ule (Word64.concrete.shift key.value 3) (Word64.concrete.const 6) = 0 := by
    rw [Word64.ule_value]
    exact if_neg (by change ¬(key.value >>> 3).toNat ≤ 6; omega)
  simp only [ProtoParse.plan,hu,word_eq_value,Word64.ule_value]
  simp_all [Word64.concrete,ByteAuth.concrete,Word64.bor,Unpad.chooseByte,
    show (255#8) = BitVec.allOnes 8 by rfl, BitVec.and_allOnes,BitVec.allOnes_and,BitVec.xor_assoc]

theorem fixed32_unknown_top (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hkey : key.ok = 255) (hvalue : key.value.toNat ≤ 4294967295)
    (htag : key.value >>> 3 ≠ 0) (hkind : key.value &&& 7 = 5)
    (hdepth : state.depth = 0) (hunknown : 6 < (key.value >>> 3).toNat) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok =
      Word64.concrete.ule (key.stop + 4) (BitVec.ofNat 64 capacity) := by
  have hu : Word64.concrete.ule (Word64.concrete.shift key.value 3) (Word64.concrete.const 6) = 0 := by
    rw [Word64.ule_value]
    exact if_neg (by change ¬(key.value >>> 3).toNat ≤ 6; omega)
  simp only [ProtoParse.plan,hu,word_eq_value,Word64.ule_value]
  simp_all [Word64.concrete,ByteAuth.concrete,Word64.bor,Unpad.chooseByte,
    show (255#8) = BitVec.allOnes 8 by rfl, BitVec.and_allOnes,BitVec.allOnes_and,BitVec.xor_assoc]

theorem length_unknown_top (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hkey : key.ok = 255) (hvalue : key.value.toNat ≤ 4294967295)
    (htag : key.value >>> 3 ≠ 0) (hkind : key.value &&& 7 = 2)
    (hdepth : state.depth = 0) (hunknown : 6 < (key.value >>> 3).toNat) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok =
      payload.ok &&& Word64.concrete.ule payload.value (BitVec.ofNat 64 capacity - payload.stop) := by
  have hu : Word64.concrete.ule (Word64.concrete.shift key.value 3) (Word64.concrete.const 6) = 0 := by
    rw [Word64.ule_value]
    exact if_neg (by change ¬(key.value >>> 3).toNat ≤ 6; omega)
  simp only [ProtoParse.plan,hu,word_eq_value,Word64.ule_value]
  simp_all [Word64.concrete,ByteAuth.concrete,Word64.bor,Unpad.chooseByte,
    show (255#8) = BitVec.allOnes 8 by rfl, BitVec.and_allOnes,BitVec.allOnes_and,BitVec.xor_assoc]

theorem varint_unknown_top (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hkey : key.ok = 255) (hvalue : key.value.toNat ≤ 4294967295)
    (htag : key.value >>> 3 ≠ 0) (hkind : key.value &&& 7 = 0)
    (hdepth : state.depth = 0) (hunknown : 6 < (key.value >>> 3).toNat) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok =
      payload.ok := by
  have hu : Word64.concrete.ule (Word64.concrete.shift key.value 3) (Word64.concrete.const 6) = 0 := by
    rw [Word64.ule_value]
    exact if_neg (by change ¬(key.value >>> 3).toNat ≤ 6; omega)
  simp only [ProtoParse.plan,hu,word_eq_value,Word64.ule_value]
  simp_all [Word64.concrete,ByteAuth.concrete,Word64.bor,Unpad.chooseByte,
    show (255#8) = BitVec.allOnes 8 by rfl, BitVec.and_allOnes,BitVec.allOnes_and,BitVec.xor_assoc]


/-- Recognized scalar tags2/3 require wire type0 before payload interpretation. -/
theorem scalar_wire_reject (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hdepth : state.depth = 0) (htag : key.value >>> 3 = 2 ∨ key.value >>> 3 = 3)
    (hkind : key.value &&& 7 ≠ 0) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 0 := by
  rcases htag with htag | htag <;>
    simp only [ProtoParse.plan,word_eq_value,Word64.ule_value] <;>
    simp_all [Word64.concrete,ByteAuth.concrete,Word64.bor,Unpad.chooseByte]

/-- Recognized byte tags1/4/5/6 require wire type2. -/
theorem bytes_wire_reject (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hdepth : state.depth = 0)
    (htag : key.value >>> 3 = 1 ∨ key.value >>> 3 = 4 ∨ key.value >>> 3 = 5 ∨ key.value >>> 3 = 6)
    (hkind : key.value &&& 7 ≠ 2) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 0 := by
  rcases htag with htag | htag | htag | htag <;>
    simp only [ProtoParse.plan,word_eq_value,Word64.ule_value] <;>
    simp_all [Word64.concrete,ByteAuth.concrete,Word64.bor,Unpad.chooseByte]


theorem scalar_top_mask (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hkey : key.ok = 255) (hvalue : key.value.toNat ≤ 4294967295)
    (hdepth : state.depth = 0) (htag : key.value >>> 3 = 2 ∨ key.value >>> 3 = 3)
    (hkind : key.value &&& 7 = 0) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = payload.ok := by
  rcases htag with htag | htag <;>
    simp only [ProtoParse.plan,word_eq_value,Word64.ule_value] <;>
    simp_all [Word64.concrete,ByteAuth.concrete,Word64.bor,Unpad.chooseByte,
      show (255#8) = BitVec.allOnes 8 by rfl,BitVec.and_allOnes,BitVec.allOnes_and,BitVec.xor_assoc]

theorem bytes_top_mask (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hkey : key.ok = 255) (hvalue : key.value.toNat ≤ 4294967295)
    (hdepth : state.depth = 0)
    (htag : key.value >>> 3 = 1 ∨ key.value >>> 3 = 4 ∨ key.value >>> 3 = 5 ∨ key.value >>> 3 = 6)
    (hkind : key.value &&& 7 = 2) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok =
      payload.ok &&& Word64.concrete.ule payload.value (BitVec.ofNat 64 capacity - payload.stop) := by
  rcases htag with htag | htag | htag | htag <;>
    simp only [ProtoParse.plan,word_eq_value,Word64.ule_value] <;>
    simp_all [Word64.concrete,ByteAuth.concrete,Word64.bor,Unpad.chooseByte,
      show (255#8) = BitVec.allOnes 8 by rfl,BitVec.and_allOnes,BitVec.allOnes_and,BitVec.xor_assoc]

theorem top_end_reject (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hdepth : state.depth = 0) (hkind : key.value &&& 7 = 4) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 0 := by
  simp only [ProtoParse.plan,word_eq_value,Word64.ule_value]
  simp_all [Word64.concrete,ByteAuth.concrete,Word64.bor,Unpad.chooseByte]

#print axioms fixed64_unknown_top
#print axioms fixed32_unknown_top
#print axioms length_unknown_top
#print axioms varint_unknown_top
#print axioms scalar_wire_reject
#print axioms bytes_wire_reject
#print axioms scalar_top_mask
#print axioms bytes_top_mask
#print axioms top_end_reject
end LibSignalReference.Candidate.ProstTopField
