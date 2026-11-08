import ProtoParseWork.FullParserV3Work.StateMasks
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkipBuf
open LibSignalReference.Candidate.ProstTopField
set_option maxHeartbeats 2000000

def DecoderMasks (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64))) : Prop :=
  ∀ i (hi : i < rows.length), Mask rows[i].ok

theorem decoder_masks_drop (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64)))
    (start : Nat) (hr : DecoderMasks rows) : DecoderMasks (rows.drop start) := by
  intro i hi
  have hb : start+i < rows.length := by simp only [List.length_drop] at hi; omega
  simpa only [List.getElem_drop] using hr (start+i) hb

theorem decoder_masks_take (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64)))
    (count : Nat) (hr : DecoderMasks rows) : DecoderMasks (rows.take count) := by
  intro i hi
  have hb : i < rows.length := by simp only [List.length_take] at hi; omega
  simpa only [List.getElem_take] using hr i hb

theorem lookup_mask (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64)))
    (index : BitVec 64) (start : Nat) (hr : DecoderMasks rows) :
    Mask (ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete index start rows).ok := by
  induction rows generalizing start with
  | nil => exact Or.inl rfl
  | cons row rest ih =>
    apply mask_choose (mask_eq _ _)
    · exact hr 0 (by simp)
    · apply ih
      intro i hi
      exact hr (i+1) (by simp; omega)

theorem table_masks (bytes : Slice U8) : DecoderMasks
    (ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)) := by
  intro i hi
  have hb : i < (contents bytes).length := by simpa only [table_length] using hi
  rw [table_get _ _ hb,decode_prefix_drop,← contents_drop]
  exact prefix_mask (drop bytes i)

theorem step_masks (capacity position : Nat)
    (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64)))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hr : DecoderMasks rows) (hs : Mask state.ok) (hf : FieldMasks state.fields) :
    Mask (ProtoParse.step Word64.concrete ByteAuth.concrete capacity rows state position).ok ∧
    FieldMasks (ProtoParse.step Word64.concrete ByteAuth.concrete capacity rows state position).fields := by
  apply apply_masks state position _ hs _ hf
  apply planWithCursor_mask
  · by_cases hp : position < rows.length
    · simp only [List.getElem?_eq_getElem hp,Option.getD_some]
      exact hr position hp
    · simp only [List.getElem?_eq_none (by omega : rows.length ≤ position),Option.getD_none]
      exact Or.inl rfl
  · exact lookup_mask _ _ _ (decoder_masks_take _ _ (decoder_masks_drop _ _ hr))

theorem scan_masks (capacity : Nat) (positions : List Nat)
    (rows : List (ProtoParse.Decoded (BitVec 8) (BitVec 64)))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hr : DecoderMasks rows) (hs : Mask state.ok) (hf : FieldMasks state.fields) :
    let result := positions.foldl (ProtoParse.step Word64.concrete ByteAuth.concrete capacity rows) state
    Mask result.ok ∧ FieldMasks result.fields := by
  induction positions generalizing state with
  | nil => exact ⟨hs,hf⟩
  | cons p rest ih =>
    have h := step_masks capacity p rows state hr hs hf
    exact ih _ h.1 h.2

theorem parse_masks (bytes : Slice U8) :
    let result := ProtoParse.parseBody VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)
    Mask result.ok ∧ FieldMasks result.fields := by
  apply scan_masks _ _ _ _ (table_masks bytes) (Or.inr rfl)
  intro i hi
  simp only [ProtoParse.initial,List.getElem_replicate]
  exact Or.inl rfl

#print axioms table_masks
#print axioms step_masks
#print axioms scan_masks
#print axioms parse_masks
end FullParserV3
