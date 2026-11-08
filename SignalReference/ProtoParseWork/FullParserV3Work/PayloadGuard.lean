import ProtoParseWork.FullParserV3Work.CursorGuard
import ProtoParseWork.FullParserV3Work.ScanState
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxHeartbeats 2000000

theorem payload_length_guard (capacity cursor : Nat) (hc : cursor ≤ capacity) (hcap : capacity ≤ 512) :
    Word64.concrete.ule (BitVec.ofNat 64 cursor + Word64.concrete.const 11) (Word64.concrete.const capacity) =
      if capacity > cursor+10 then 255 else 0 := by
  rw [Word64.ule_value]
  have hcursor : (BitVec.ofNat 64 cursor).toNat = cursor := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have hcapacity : (Word64.concrete.const capacity).toNat = capacity := by change capacity % 2^64 = capacity; exact Nat.mod_eq_of_lt (by omega)
  have hsum : (BitVec.ofNat 64 cursor + Word64.concrete.const 11).toNat = cursor+11 := by
    rw [BitVec.toNat_add,hcursor]
    change (cursor+11) % 2^64 = cursor+11
    exact Nat.mod_eq_of_lt (by omega)
  rw [hsum,hcapacity]
  have he : cursor+11 ≤ capacity ↔ capacity > cursor+10 := by omega
  simp only [he]

theorem payload_fast_mask (bytes : Slice U8) (cursor : Nat) (hc : cursor < bytes.length) (hcap : bytes.length ≤ 512) :
    Word64.bor ByteAuth.concrete
      (Word64.concrete.ule (BitVec.ofNat 64 cursor + Word64.concrete.const 11) (Word64.concrete.const bytes.length))
      (((rowsOf bytes)[bytes.length-1]?.getD ⟨0,BitVec.ofNat 64 (bytes.length-1),0⟩).ok) =
    if FastGuard (drop bytes cursor) then 255 else 0 := by
  rw [payload_length_guard bytes.length cursor (by omega) hcap,table_last_clear_slice bytes (by omega)]
  simp only [fast_guard_drop bytes cursor hc]
  by_cases hf : bytes.length > cursor+10 <;> by_cases hl : (byte bytes (bytes.length-1)).val < 128
  all_goals simp only [hf,hl,true_or,false_or,or_true,or_false,if_true,if_false]
  all_goals rfl

theorem payload_slow_stop (capacity cursor : Nat) (hc : cursor ≤ capacity) (hcap : capacity ≤ 512) :
    Word64.concrete.select
      (Word64.concrete.ule (BitVec.ofNat 64 cursor + Word64.concrete.const 10) (Word64.concrete.const capacity))
      (BitVec.ofNat 64 cursor + Word64.concrete.const 10) (Word64.concrete.const capacity) =
    BitVec.ofNat 64 (cursor + min 10 (capacity-cursor)) := by
  have hcursor : (BitVec.ofNat 64 cursor).toNat = cursor := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have hcapacity : (Word64.concrete.const capacity).toNat = capacity := by change capacity % 2^64 = capacity; exact Nat.mod_eq_of_lt (by omega)
  have hsum : (BitVec.ofNat 64 cursor + Word64.concrete.const 10).toNat = cursor+10 := by
    rw [BitVec.toNat_add,hcursor]
    change (cursor+10) % 2^64 = cursor+10
    exact Nat.mod_eq_of_lt (by omega)
  rw [Word64.ule_value,hsum,hcapacity]
  by_cases hf : cursor+10 ≤ capacity
  · rw [if_pos hf,Word64.select_accept,Nat.min_eq_left (by omega)]
    change BitVec.ofNat 64 cursor + BitVec.ofNat 64 10 = _
    simp only [BitVec.ofNat_add]
  · rw [if_neg hf,Word64.select_reject,Nat.min_eq_right (by omega)]
    have he : cursor+(capacity-cursor) = capacity := by omega
    rw [he]
    rfl

#print axioms payload_length_guard
#print axioms payload_fast_mask
#print axioms payload_slow_stop
end FullParserV3
