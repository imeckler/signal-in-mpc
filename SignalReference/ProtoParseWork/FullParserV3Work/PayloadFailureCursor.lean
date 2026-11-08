import ProtoParseWork.FullParserV3Work.PayloadErrorMask
import ProtoParseWork.FullParserV3Work.UnknownShadow
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 3000000

private theorem select_same (mask : BitVec 8) (value : BitVec 64) : Word64.concrete.select mask value value = value := by
  change ((BitVec.replicate 8 mask &&& value) ^^^ (~~~BitVec.replicate 8 mask &&& value)) = value
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases (BitVec.replicate 8 mask).getLsbD i <;> cases value.getLsbD i <;> rfl

/-- Exact payload-varint rejection cursor, including EOF, fast nonconsumption
and the short slow path. Header/wire validity remains explicitly discharged
by actual branch composition; no decoder or termination hypothesis is assumed. -/
theorem actual_payload_failure_cursor (bytes middle after : Slice U8) (position : Nat) (tag : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (error : LoopSupportSkip.error.DecodeError)
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle))
    (hd : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Err error,after))
    (hkind : kind = .Varint ∨ kind = .LengthDelimited) (hdepth : state.depth.toNat ≤ 99)
    (hknown : validKnownMask ((rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩) state = 255) :
    let rows := rowsOf bytes
    let key := rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
    let payload := ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1) ((rows.drop (position+1)).take 10)
    let p := ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete bytes.length position
      (rows[bytes.length-1]?.getD ⟨0,BitVec.ofNat 64 (bytes.length-1),0⟩).ok key payload state
    p.ok = 0 ∧ p.tag = key.value >>> 3 ∧ after = drop bytes p.stop.toNat ∧ p.stop.toNat ≤ bytes.length := by
  let rows := rowsOf bytes
  let key := rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
  let payload := ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1) ((rows.drop (position+1)).take 10)
  let lastClear := (rows[bytes.length-1]?.getD ⟨0,BitVec.ofNat 64 (bytes.length-1),0⟩).ok
  let p := ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete bytes.length position lastClear key payload state
  obtain ⟨kc,_,_,hkb,hrest,_,hkstop,_,_,_,hwire,hkmask⟩ := actual_key_row bytes middle position tag kind hp hk
  have hwire' : key.value &&& 7 = 0 ∨ key.value &&& 7 = 2 := by
    rcases hkind with rfl | rfl
    · exact Or.inl hwire
    · exact Or.inr hwire
  have hpay : payload.ok = 0 := actual_payload_error_mask bytes middle after position tag kind error hp hcap hk hd
  have hbad := plan_payload_error bytes.length key payload state hpay hwire'
  have hstop := payload_varint_failure_stop bytes.length position lastClear key payload state hkmask hknown hdepth hwire' hpay hbad
  have hword : p.stop = BitVec.ofNat 64 (if FastGuard (drop bytes (position+kc)) then position+kc else position+kc+min 10 (bytes.length-(position+kc))) := by
    rw [hstop,hkstop,payload_slow_stop bytes.length (position+kc) hkb hcap]
    by_cases hmore : position+kc < bytes.length
    · rw [payload_fast_mask bytes (position+kc) hmore hcap]
      split_ifs <;> first | exact Word64.select_accept _ _ | exact Word64.select_reject _ _
    · have he : position+kc = bytes.length := by omega
      rw [he]
      simp only [Nat.sub_self,Nat.min_zero,Nat.add_zero,ite_self]
      exact select_same _ _
  have hbound : (if FastGuard (drop bytes (position+kc)) then position+kc else position+kc+min 10 (bytes.length-(position+kc))) ≤ bytes.length := by
    split <;> omega
  have hnat : p.stop.toNat = (if FastGuard (drop bytes (position+kc)) then position+kc else position+kc+min 10 (bytes.length-(position+kc))) := by
    rw [hword,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have hafter : after = if FastGuard middle then middle else drop middle (min 10 middle.length) := by
    obtain ⟨r,remaining,hr,_,he⟩ := decode_full_reference middle
    rw [hd] at hr
    cases hr
    exact he
  refine ⟨hbad,plan_valid_tag _ _ _ _ _ _ hkmask,?_,?_⟩
  · rw [hnat]
    rw [hrest] at hafter
    split_ifs with hf
    · simpa only [if_pos hf] using hafter
    · simpa only [if_neg hf,drop_length,drop_add] using hafter
  · rw [hnat]
    exact hbound

#print axioms actual_payload_failure_cursor
end FullParserV3
