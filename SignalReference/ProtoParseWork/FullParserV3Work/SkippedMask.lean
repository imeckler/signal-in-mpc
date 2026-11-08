import ProtoParseWork.FullParserV3Work.PayloadPlan
import ProtoParseWork.FullParserV3Work.UnknownFields
import ProtoParseWork.FullParserV3Work.RejectedScan
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipBuf
set_option maxHeartbeats 2000000

private theorem u32_nat64 (tag : U32) : (BitVec.ofNat 64 tag.val).toNat = tag.val := by
  have hb : tag.val < 2^64 := by have h := tag.bv.isLt; simp only [UScalar.bv_toNat] at h; omega
  exact Nat.mod_eq_of_lt hb

theorem skipped_row_allowed (bytes middle : Slice U8) (position : Nat) (tag : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hp : position < bytes.length) (ha : state.depth ≠ 0 ∨ 6 < tag.val)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle)) :
    state.depth ≠ 0 ∨ 6 < (((rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩).value >>> 3).toNat := by
  rcases ha with hd | ht
  · exact Or.inl hd
  · obtain ⟨_,_,_,_,_,_,_,_,_,htag,_,_⟩ := actual_key_row bytes middle position tag kind hp hk
    apply Or.inr
    rw [htag,u32_nat64]
    exact ht

theorem skipped_initialization (state : ProtoParse.State (BitVec 8) (BitVec 64)) (tag : U32)
    (hl : state.fields.length = 6) (ha : state.depth ≠ 0 ∨ 6 < tag.val) :
    (if state.depth = 0 then ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255
      (BitVec.ofNat 64 tag.val) state.fields else state.fields) = state.fields := by
  by_cases hd : state.depth = 0
  · rw [if_pos hd]
    apply initialize_unknown state.fields _ (by omega)
    rw [u32_nat64]
    exact ha.resolve_left (not_not.mpr hd)
  · exact if_neg hd

namespace Observed
open SignalMessageIntegration DispatcherIntegration

theorem active_fields_congr (bytes after : Slice U8) (error : prost.error.DecodeError)
    (before result : State (BitVec 8) (BitVec 64)) (left right : List (ProtoParse.Field (BitVec 8) (BitVec 64)))
    (he : left = right) (h : ActiveRejection bytes after error before result left) :
    ActiveRejection bytes after error before result right := he ▸ h

#print axioms active_fields_congr
end Observed
#print axioms skipped_row_allowed
#print axioms skipped_initialization
end FullParserV3
