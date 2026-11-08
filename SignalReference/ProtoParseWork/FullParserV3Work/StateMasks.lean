import ProtoParseWork.FullParserV3Work.Masks
open TlsMpc TlsMpc.Signal
namespace FullParserV3
set_option maxHeartbeats 2000000

def FieldMasks (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64))) : Prop :=
  ∀ i (hi : i < fields.length), Mask fields[i].present

theorem select_field_mask (m : BitVec 8) (yes no : ProtoParse.Field (BitVec 8) (BitVec 64))
    (hm : Mask m) (hy : Mask yes.present) (hn : Mask no.present) :
    Mask (ProtoParse.selectField Word64.concrete ByteAuth.concrete m yes no).present :=
  mask_choose hm hy hn

theorem initialize_masks (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64)))
    (enabled : BitVec 8) (tag : BitVec 64) (he : Mask enabled) (hf : FieldMasks fields) :
    FieldMasks (ProtoParse.initializeFields Word64.concrete ByteAuth.concrete enabled tag fields) := by
  intro i hi
  have hi' : i < fields.length := by simpa only [ProtoParse.initializeFields,List.length_map,List.length_zipIdx] using hi
  simp only [ProtoParse.initializeFields,List.getElem_map,List.getElem_zipIdx,Nat.zero_add]
  exact select_field_mask _ _ _ (mask_and he (mask_eq _ _))
    (select_field_mask _ _ _ (hf i hi') (hf i hi') (Or.inr rfl)) (hf i hi')

theorem write_masks (fields : List (ProtoParse.Field (BitVec 8) (BitVec 64)))
    (enabled : BitVec 8) (tag : BitVec 64) (payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (he : Mask enabled) (hf : FieldMasks fields) :
    FieldMasks (ProtoParse.writeFields Word64.concrete ByteAuth.concrete enabled tag payload fields) := by
  intro i hi
  have hi' : i < fields.length := by simpa only [ProtoParse.writeFields,List.length_map,List.length_zipIdx] using hi
  simp only [ProtoParse.writeFields,List.getElem_map,List.getElem_zipIdx,Nat.zero_add]
  exact select_field_mask _ _ _ (mask_and he (mask_eq _ _)) (Or.inr rfl) (hf i hi')

theorem apply_masks (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (position : Nat) (p : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (hs : Mask state.ok) (hp : Mask p.ok) (hf : FieldMasks state.fields) :
    Mask (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state).ok ∧
    FieldMasks (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state).fields := by
  constructor
  · exact mask_and hs (mask_not (mask_and (mask_eq _ _) (mask_not hp)))
  · apply write_masks
    · exact mask_and (mask_and (mask_and hs (mask_eq _ _)) hp) (mask_eq _ _)
    · apply initialize_masks
      · exact mask_and (mask_and hs (mask_eq _ _)) (mask_eq _ _)
      · exact hf

#print axioms initialize_masks
#print axioms write_masks
#print axioms apply_masks
end FullParserV3
