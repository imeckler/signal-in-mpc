import SkipPlanWork.KeyCircuit

namespace LibSignalReference.Candidate.ProstSkipPlan
open TlsMpc TlsMpc.Signal
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 500000

/-- Inside a group every field is skipped, including tags recognized at top level. -/
theorem fixed64_in_group (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hkey : key.ok = 255) (hvalue : key.value.toNat ≤ 4294967295)
    (htag : key.value >>> 3 ≠ 0) (hkind : key.value &&& 7 = 1)
    (hdepth : state.depth ≠ 0) (hlimit : state.depth.toNat ≤ 99) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok =
      Word64.concrete.ule (key.stop + 8) (BitVec.ofNat 64 capacity) := by
  simp only [ProtoParse.plan,word_eq_value,Word64.ule_value]
  simp_all [Word64.concrete,ByteAuth.concrete,Word64.bor,Unpad.chooseByte,
    show (255#8) = BitVec.allOnes 8 by rfl, BitVec.and_allOnes,BitVec.allOnes_and,BitVec.xor_assoc]

 theorem fixed64_stop (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hkind : key.value &&& 7 = 1) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).stop =
      key.stop + 8 := by
  simp only [ProtoParse.plan,word_eq_value]
  simp_all [Word64.concrete]
  simp only [show (18446744073709551615#64) = BitVec.allOnes 64 by rfl,BitVec.allOnes_and]

/-- Inside a group every field is skipped, including tags recognized at top level. -/
theorem fixed32_in_group (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hkey : key.ok = 255) (hvalue : key.value.toNat ≤ 4294967295)
    (htag : key.value >>> 3 ≠ 0) (hkind : key.value &&& 7 = 5)
    (hdepth : state.depth ≠ 0) (hlimit : state.depth.toNat ≤ 99) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok =
      Word64.concrete.ule (key.stop + 4) (BitVec.ofNat 64 capacity) := by
  simp only [ProtoParse.plan,word_eq_value,Word64.ule_value]
  simp_all [Word64.concrete,ByteAuth.concrete,Word64.bor,Unpad.chooseByte,
    show (255#8) = BitVec.allOnes 8 by rfl, BitVec.and_allOnes,BitVec.allOnes_and,BitVec.xor_assoc]

 theorem fixed32_stop (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hkind : key.value &&& 7 = 5) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).stop =
      key.stop + 4 := by
  simp only [ProtoParse.plan,word_eq_value]
  simp_all [Word64.concrete]
  simp only [show (18446744073709551615#64) = BitVec.allOnes 64 by rfl,BitVec.allOnes_and]

/-- Inside a group every field is skipped, including tags recognized at top level. -/
theorem length_in_group (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hkey : key.ok = 255) (hvalue : key.value.toNat ≤ 4294967295)
    (htag : key.value >>> 3 ≠ 0) (hkind : key.value &&& 7 = 2)
    (hdepth : state.depth ≠ 0) (hlimit : state.depth.toNat ≤ 99) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok =
      payload.ok &&& Word64.concrete.ule payload.value (BitVec.ofNat 64 capacity - payload.stop) := by
  simp only [ProtoParse.plan,word_eq_value,Word64.ule_value]
  simp_all [Word64.concrete,ByteAuth.concrete,Word64.bor,Unpad.chooseByte,
    show (255#8) = BitVec.allOnes 8 by rfl, BitVec.and_allOnes,BitVec.allOnes_and,BitVec.xor_assoc]

/-- Inside a group every field is skipped, including tags recognized at top level. -/
theorem varint_in_group (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hkey : key.ok = 255) (hvalue : key.value.toNat ≤ 4294967295)
    (htag : key.value >>> 3 ≠ 0) (hkind : key.value &&& 7 = 0)
    (hdepth : state.depth ≠ 0) (hlimit : state.depth.toNat ≤ 99) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok =
      payload.ok := by
  simp only [ProtoParse.plan,word_eq_value,Word64.ule_value]
  simp_all [Word64.concrete,ByteAuth.concrete,Word64.bor,Unpad.chooseByte,
    show (255#8) = BitVec.allOnes 8 by rfl, BitVec.and_allOnes,BitVec.allOnes_and,BitVec.xor_assoc]

/-- The bounded parser's fixed-width test is an ordinary remaining-length check;
the word addition cannot wrap under the public capacity bound. -/
theorem fixed_bounds (start : BitVec 64) (capacity width : Nat)
    (hs : start.toNat ≤ capacity) (hc : capacity ≤ 512) (hw : width ≤ 8) :
    Word64.concrete.ule (start + BitVec.ofNat 64 width) (BitVec.ofNat 64 capacity) =
      if width ≤ capacity - start.toNat then 255 else 0 := by
  rw [Word64.ule_value]
  have hc64 : capacity < 2^64 := by omega
  have hw64 : width < 2^64 := by omega
  have hsum : start.toNat + width < 2^64 := by omega
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hc64,
    Nat.mod_eq_of_lt hw64,Nat.mod_eq_of_lt hsum]
  have he : (start.toNat + width ≤ capacity) ↔ (width ≤ capacity - start.toNat) := by omega
  simp only [he]


theorem recursion_reject (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hdepth : 99 < state.depth.toNat) (hkind : key.value &&& 7 ≠ 4) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok = 0 := by
  have hb : Word64.concrete.ule state.depth (Word64.concrete.const 99) = 0 := by
    rw [Word64.ule_value]
    exact if_neg (by change ¬state.depth.toNat ≤ 99; omega)
  have hk : Word64.eq Word64.concrete ByteAuth.concrete
      (Word64.concrete.band key.value (Word64.concrete.const 7)) (Word64.concrete.const 4) = 0 := by
    rw [word_eq_value]
    exact if_neg hkind
  simp only [ProtoParse.plan,hb,hk]
  simp [Word64.bor,ByteAuth.concrete]

theorem length_stop (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hkind : key.value &&& 7 = 2) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).stop =
      payload.stop + payload.value := by
  simp only [ProtoParse.plan,word_eq_value]
  simp_all [Word64.concrete]
  simp only [show (18446744073709551615#64) = BitVec.allOnes 64 by rfl,BitVec.allOnes_and]

theorem varint_stop (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hkind : key.value &&& 7 = 0) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).stop =
      payload.stop := by
  simp only [ProtoParse.plan,word_eq_value]
  simp_all [Word64.concrete]
  simp only [show (18446744073709551615#64) = BitVec.allOnes 64 by rfl,BitVec.allOnes_and]

theorem length_bounds (start value : BitVec 64) (capacity : Nat)
    (hs : start.toNat ≤ capacity) (hc : capacity ≤ 512) :
    Word64.concrete.ule value (BitVec.ofNat 64 capacity - start) =
      if value.toNat ≤ capacity - start.toNat then 255 else 0 := by
  rw [Word64.ule_value]
  have hcap : capacity < 2^64 := by omega
  have hn : 2^64 - start.toNat + capacity = 2^64 + (capacity - start.toNat) := by omega
  simp only [BitVec.toNat_sub,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hcap,hn,Nat.add_mod,
    Nat.mod_self,Nat.zero_add,Nat.mod_eq_of_lt (by omega : capacity - start.toNat < 2^64)]

#print axioms fixed64_in_group
#print axioms fixed64_stop
#print axioms fixed32_in_group
#print axioms fixed32_stop
#print axioms fixed_bounds
#print axioms length_in_group
#print axioms varint_in_group
#print axioms recursion_reject
#print axioms length_stop
#print axioms varint_stop
#print axioms length_bounds

end LibSignalReference.Candidate.ProstSkipPlan
