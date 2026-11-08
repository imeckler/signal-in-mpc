import ProtoParseWork.FullParserV3Work.KeyValidationPlan
import ProtoParseWork.FullParserV3Work.ScanState
import ProtoParseWork.FullParserV3Work.KeyFailureCursor
import ProtoParseWork.FullParserV3Work.KeyErrorTable
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkipBuf
open LibSignalReference.Candidate.ProstTopField LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 3000000

private theorem key_error_invalid (value : U64) (error : LoopSupportSkip.error.DecodeError)
    (he : keyResult value = .Err error) : ¬ValidValue value := by
  intro hv
  obtain ⟨kind,hk,_⟩ := key_success value hv
  rw [he] at hk
  cases hk

theorem actual_key_validation_failure_cursor (bytes after : Slice U8) (position : Nat)
    (value : U64) (error : LoopSupportSkip.error.DecodeError)
    (payload : ProtoParse.Decoded (BitVec 8) (BitVec 64)) (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hd : LoopSupportSkip.encoding.varint.decode_varint sliceBuf (drop bytes position) = .ok (.Ok value,after))
    (he : keyResult value = .Err error) :
    let rows := rowsOf bytes
    let key := rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
    let lastClear := (rows[bytes.length-1]?.getD ⟨0,BitVec.ofNat 64 (bytes.length-1),0⟩).ok
    let p := ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete bytes.length position lastClear key payload state
    p.ok = 0 ∧ p.tag = 0 ∧ after = drop bytes p.stop.toNat ∧ p.stop.toNat ≤ bytes.length := by
  obtain ⟨count,hc,h10,hb,ha,hrow⟩ := table_actual_success bytes after position value hp hd
  have hposRows : position < (rowsOf bytes).length := by rw [table_length]; simpa only [contents,List.length_map] using hp
  have hkeyRow : (rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩ = ⟨255,BitVec.ofNat 64 (position+count),value.bv⟩ := by
    rw [List.getElem?_eq_getElem hposRows,Option.getD_some]
    exact hrow
  dsimp only
  rw [hkeyRow]
  have hbad : ¬(value.bv.toNat ≤ 4294967295 ∧ 8 ≤ value.bv.toNat ∧ value.bv.toNat % 8 ≤ 5) := by
    simpa only [UScalar.bv_toNat,ValidValue] using key_error_invalid value error he
  obtain ⟨ho,ht,hs⟩ := key_validation_plan_cursor bytes.length position
    ((rowsOf bytes)[bytes.length-1]?.getD ⟨0,BitVec.ofNat 64 (bytes.length-1),0⟩).ok
    ⟨255,BitVec.ofNat 64 (position+count),value.bv⟩ payload state rfl hbad
  refine ⟨ho,ht,?_,?_⟩
  all_goals rw [hs]
  · simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : position+count < 2^64)] using ha
  · simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : position+count < 2^64)]
    exact hb

/-- All actual key rejection paths agree with v2's unmasked error cursor and
sanitized tag, including InvalidKey/InvalidWireType/InvalidTag and fast/slow
varint failures. Constructor and complete parameter projection is exact too. -/
theorem actual_key_rejection_plan (bytes after : Slice U8) (position : Nat)
    (error : LoopSupportSkip.error.DecodeError)
    (payload : ProtoParse.Decoded (BitVec 8) (BitVec 64)) (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hd : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Err error,after)) :
    let rows := rowsOf bytes
    let key := rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
    let lastClear := (rows[bytes.length-1]?.getD ⟨0,BitVec.ofNat 64 (bytes.length-1),0⟩).ok
    let p := ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete bytes.length position lastClear key payload state
    p.ok = 0 ∧ p.tag = 0 ∧ after = drop bytes p.stop.toNat ∧ p.stop.toNat ≤ bytes.length ∧
      Observed.statusView (.Err (SignalMessageIntegration.skipError error)) =
        some (Observed.classify Word64.concrete ByteAuth.concrete key payload state) := by
  have hm : Observed.statusView (.Err (SignalMessageIntegration.skipError error)) = some (Observed.classify
      Word64.concrete ByteAuth.concrete ((rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩) payload state) := by
    rw [List.getElem?_eq_getElem (by rw [table_length]; simpa only [contents,List.length_map] using hp),Option.getD_some]
    exact Observed.actual_key_error_at bytes after position error payload state hp hd
  obtain ⟨result,remaining,hv,_,_,hk⟩ := decode_key_reference (drop bytes position)
  rw [hd] at hk
  have hr := Result.ok.inj hk
  cases result with
  | Err e =>
    have he : e = error := (core.result.Result.Err.inj (congrArg Prod.fst hr)).symm
    have ha : remaining = after := (congrArg Prod.snd hr).symm
    have hv' : LoopSupportSkip.encoding.varint.decode_varint sliceBuf (drop bytes position) = .ok (.Err error,after) := by simpa only [he,ha] using hv
    have h := actual_key_varint_failure_cursor bytes after position error payload state hp hcap hv'
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,hm⟩
  | Ok value =>
    have he : keyResult value = .Err error := (congrArg Prod.fst hr).symm
    have ha : remaining = after := (congrArg Prod.snd hr).symm
    have h := actual_key_validation_failure_cursor bytes remaining position value error payload state hp hcap hv he
    simpa only [ha] using (And.intro h.1 (And.intro h.2.1 (And.intro h.2.2.1 (And.intro h.2.2.2 hm))))

#print axioms actual_key_validation_failure_cursor
#print axioms actual_key_rejection_plan
end FullParserV3
