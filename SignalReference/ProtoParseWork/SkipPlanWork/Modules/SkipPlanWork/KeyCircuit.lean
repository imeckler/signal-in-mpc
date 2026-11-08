import SkipTranslatorWork.KeyReference

namespace LibSignalReference.Candidate.ProstSkipKey
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
open LibSignalReference.Candidate.ProstSkipSlice
set_option maxHeartbeats 400000

structure KeyFields (B W : Type) where
  ok : B
  stop : W
  tag : W
  kind : W

def KeyFields.map (f : B → B') (fw : W → W') (k : KeyFields B W) : KeyFields B' W' :=
  ⟨f k.ok,fw k.stop,fw k.tag,fw k.kind⟩

/-- The scalar key checks used by ProtoParse.plan, isolated from payload and
known-field validation. This is a circuit component, never a Rust replacement. -/
def keyFields (o : Word64.Ops B W) (a : ByteAuth.Ops B) (key : ProtoParse.Decoded B W) : KeyFields B W :=
  let tag := o.shift key.value 3
  let kind := o.band key.value (o.const 7)
  ⟨a.and key.ok (a.and (o.ule key.value (o.const 4294967295))
      (a.and (a.not (Word64.eq o a tag (o.const 0))) (o.ule kind (o.const 5)))),key.stop,tag,kind⟩

theorem word_eq_value (x y : BitVec 64) :
    Word64.eq Word64.concrete ByteAuth.concrete x y = if x = y then 255 else 0 := by
  unfold Word64.eq
  rw [ByteAuth.equalMask_value]
  have h : Word64.bytes Word64.concrete x = Word64.bytes Word64.concrete y ↔ x = y := by
    constructor
    · intro he
      have hp := congrArg Word64.concrete.pack he
      change Word64.concrete.pack (VarintDecode.Spqr.valueBytes x) =
        Word64.concrete.pack (VarintDecode.Spqr.valueBytes y) at hp
      simpa only [pack_valueBytes] using hp
    · intro he; rw [he]
  simp only [h]

theorem shift_zero (v : BitVec 64) : (v >>> 3) = 0 ↔ v.toNat < 8 := by
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow] at hn
    change v.toNat / 8 = 0 at hn
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    change v.toNat / 8 = 0
    omega

theorem kind_nat (v : BitVec 64) : (v &&& 7).toNat = v.toNat % 8 := by
  change v.toNat &&& (2^3-1) = v.toNat % 8
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem key_mask (key : ProtoParse.Decoded (BitVec 8) (BitVec 64)) :
    (keyFields Word64.concrete ByteAuth.concrete key).ok =
      key.ok &&& (if key.value.toNat ≤ 4294967295 ∧ 8 ≤ key.value.toNat ∧ key.value.toNat % 8 ≤ 5 then 255 else 0) := by
  unfold keyFields
  change key.ok &&& (Word64.concrete.ule key.value (BitVec.ofNat 64 4294967295) &&&
    ((~~~Word64.eq Word64.concrete ByteAuth.concrete (key.value >>> 3) 0) &&&
      Word64.concrete.ule (key.value &&& 7) 5)) = _
  simp only [Word64.ule_value,word_eq_value,shift_zero,kind_nat]
  change key.ok &&& ((if key.value.toNat ≤ 4294967295 then 255 else 0) &&&
    ((~~~(if key.value.toNat < 8 then (255 : BitVec 8) else 0)) &&&
      (if key.value.toNat % 8 ≤ 5 then 255 else 0))) = _
  by_cases hr : key.value.toNat ≤ 4294967295 <;>
    by_cases ht : 8 ≤ key.value.toNat <;>
    by_cases hk : key.value.toNat % 8 ≤ 5 <;>
    simp only [hr,ht,hk,show key.value.toNat < 8 ↔ ¬8 ≤ key.value.toNat by omega,
      not_true_eq_false,not_false_eq_true,if_true,if_false,true_and,false_and,and_false]
  all_goals rfl

theorem keyFields_map {o : Word64.Ops B W} {o' : Word64.Ops B' W'}
    {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}
    (ho : Word64.Hom o o' f fw) (ha : ByteAuth.Hom a a' f) (key : ProtoParse.Decoded B W) :
    (keyFields o a key).map f fw = keyFields o' a' (key.map f fw) := by
  simp only [keyFields,KeyFields.map,ProtoParse.Decoded.map,ha.and,ha.not,ho.ule,ho.shift,ho.band,
    ho.const,Word64.eq_map ho ha]

theorem plan_key_fields (capacity : Nat) (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).tag =
      (keyFields Word64.concrete ByteAuth.concrete key).tag ∧
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).kind =
      (keyFields Word64.concrete ByteAuth.concrete key).kind := ⟨rfl,rfl⟩

#print axioms word_eq_value
#print axioms key_mask
#print axioms keyFields_map
end LibSignalReference.Candidate.ProstSkipKey
