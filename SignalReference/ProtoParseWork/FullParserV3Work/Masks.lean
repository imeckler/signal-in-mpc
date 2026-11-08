import ProtoParseWork.FullParserV3Work.FieldProjection
import ProtoParseWork.FullParserV3Work.DecoderTable
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipKey
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxHeartbeats 2000000

def Mask (x : BitVec 8) : Prop := x = 0 ∨ x = 255
instance (x : BitVec 8) : Decidable (Mask x) := inferInstanceAs (Decidable (x = 0 ∨ x = 255))

theorem mask_and {x y : BitVec 8} (hx : Mask x) (hy : Mask y) : Mask (ByteAuth.concrete.and x y) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide

theorem mask_xor {x y : BitVec 8} (hx : Mask x) (hy : Mask y) : Mask (ByteAuth.concrete.xor x y) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide

theorem mask_not {x : BitVec 8} (hx : Mask x) : Mask (ByteAuth.concrete.not x) := by
  rcases hx with rfl | rfl <;> decide

theorem mask_or {x y : BitVec 8} (hx : Mask x) (hy : Mask y) : Mask (Word64.bor ByteAuth.concrete x y) :=
  mask_xor (mask_xor hx hy) (mask_and hx hy)

theorem mask_eq (x y : BitVec 64) : Mask (Word64.eq Word64.concrete ByteAuth.concrete x y) := by
  rw [word_eq_value]; split <;> decide

theorem mask_ule (x y : BitVec 64) : Mask (Word64.concrete.ule x y) := by
  rw [Word64.ule_value]; split <;> decide

theorem mask_choose {m x y : BitVec 8} (hm : Mask m) (hx : Mask x) (hy : Mask y) :
    Mask (Unpad.chooseByte ByteAuth.concrete m x y) := by
  unfold Unpad.chooseByte
  exact mask_xor (mask_and hm (mask_xor hx hy)) hy

/-- Boolean masks are derived from the actual total varint reference, rather
than assumed for decoder output. -/
theorem prefix_mask (bytes : Slice U8) :
    Mask (ProtoParse.decodePrefix VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (contents bytes) 0).ok := by
  obtain ⟨result,after,_,hp,_⟩ := decode_full_reference bytes
  cases result with
  | Ok value => obtain ⟨count,_,_,hr,_⟩ := hp; rw [hr]; exact Or.inr rfl
  | Err e => exact Or.inl hp.2

theorem plan_mask (capacity : Nat) (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hk : Mask key.ok) (hp : Mask payload.ok) :
    Mask (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok := by
  dsimp only [ProtoParse.plan]
  apply mask_and hk
  apply mask_and (mask_ule _ _)
  apply mask_and (mask_not (mask_eq _ _))
  apply mask_and
  · exact mask_or (mask_not (mask_and (mask_eq _ _) (mask_ule _ _)))
      (mask_choose (mask_or (mask_eq _ _) (mask_eq _ _)) (mask_eq _ _) (mask_eq _ _))
  · apply mask_or
    · apply mask_and (mask_ule _ _)
      apply mask_or (mask_and (mask_eq _ _) hp)
      apply mask_or (mask_and (mask_eq _ _) (mask_ule _ _))
      apply mask_or (mask_and (mask_eq _ _) (mask_and hp (mask_ule _ _)))
      exact mask_or (mask_eq _ _) (mask_and (mask_eq _ _) (mask_ule _ _))
    · exact mask_and (mask_eq _ _) (mask_and (mask_not (mask_eq _ _)) (mask_eq _ _))

theorem planWithCursor_mask (capacity position : Nat) (lastClear : BitVec 8)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hk : Mask key.ok) (hp : Mask payload.ok) :
    Mask (ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete capacity position lastClear key payload state).ok :=
  plan_mask capacity key payload state hk hp

#print axioms prefix_mask
#print axioms plan_mask
#print axioms planWithCursor_mask
end FullParserV3
