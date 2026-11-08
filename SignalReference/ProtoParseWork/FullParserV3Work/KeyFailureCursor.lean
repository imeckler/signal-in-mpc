import ProtoParseWork.FullParserV3Work.PlanFailure
import ProtoParseWork.FullParserV3Work.CursorGuard
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkipBuf
open LibSignalReference.Candidate.ProstTopField
set_option maxHeartbeats 2000000

/-- V2's active malformed-key cursor is exactly the actual Prost varint failure
suffix, on both dispatch paths. It is not the masked external output. -/
theorem actual_key_varint_failure_cursor (bytes after : Slice U8) (position : Nat)
    (error : LoopSupportSkip.error.DecodeError)
    (payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hd : LoopSupportSkip.encoding.varint.decode_varint sliceBuf (drop bytes position) = .ok (.Err error,after)) :
    let rows := ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)
    let key := rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
    let lastClear := (rows[bytes.length-1]?.getD ⟨0,BitVec.ofNat 64 (bytes.length-1),0⟩).ok
    let p := ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete bytes.length position lastClear key payload state
    p.ok = 0 ∧ p.tag = 0 ∧ after = drop bytes p.stop.toNat ∧ p.stop.toNat ≤ bytes.length := by
  dsimp only
  have hl : (contents bytes).length = bytes.length := List.length_map _
  have hk := table_actual_error bytes after position error hp hd
  have hrow : position < (ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)).length := by rw [table_length,hl]; exact hp
  rw [List.getElem?_eq_getElem hrow,Option.getD_some]
  obtain ⟨ho,ht,hs⟩ := plan_varint_key_failure bytes.length position
    ((ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes))[bytes.length-1]?.getD
      ⟨0,BitVec.ofNat 64 (bytes.length-1),0⟩).ok _ payload state hk
  refine ⟨ho,ht,?_,?_⟩
  all_goals rw [hs,key_fast_mask bytes position hp]
  all_goals split_ifs with hf
  · rw [Word64.select_accept]
    have hn : (BitVec.ofNat 64 position).toNat = position := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    rw [hn]
    obtain ⟨r,rest,hr,_,he⟩ := decode_full_reference (drop bytes position)
    rw [hd] at hr
    cases hr
    simpa only [ErrorPost,if_pos hf] using he
  · rw [Word64.select_reject]
    have hn : (BitVec.ofNat 64 (position+min 10 (bytes.length-position))).toNat = position+min 10 (bytes.length-position) := by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    rw [hn]
    obtain ⟨r,rest,hr,_,he⟩ := decode_full_reference (drop bytes position)
    rw [hd] at hr
    cases hr
    simpa only [ErrorPost,if_neg hf,drop_length,drop_add] using he
  · rw [Word64.select_accept,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Word64.select_reject,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega

#print axioms actual_key_varint_failure_cursor
end FullParserV3
