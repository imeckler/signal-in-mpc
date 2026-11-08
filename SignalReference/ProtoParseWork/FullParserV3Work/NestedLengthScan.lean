import ProtoParseWork.FullParserV3Work.NestedFixedScan
import ProtoParseWork.FullParserV3Work.NumericLeaf
import ProtoParseWork.FullParserV3Work.Intervals
import ProtoParseWork.FullParserV3Work.SkipTotality
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkipBuf
open LibSignalReference.Candidate.ProstTopField LibSignalReference.Candidate.ProstSkipKey
open LibSignalReference.Candidate.ProstSkipPlan LibSignalReference.Candidate.ProstSkip
set_option maxHeartbeats 3000000

private theorem length_success_decode (before after : Slice U8) (tag count : U32)
    (hs : LoopSupportSkip.encoding.skip_field sliceBuf .LengthDelimited tag before ⟨count⟩ = .ok (.Ok (),after)) :
    ∃ value remaining, LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok value,remaining) ∧
      value.val ≤ remaining.length ∧ after = drop remaining value.val := by
  have hc : count ≠ 0#u32 := by intro hz; subst count; rw [recursion_limit_first] at hs; cases hs
  obtain ⟨r,remaining,hr,_,_⟩ := varint_total before
  cases r with
  | Err error => rw [length_delimited_error before remaining error tag count hc hr] at hs; cases hs
  | Ok value =>
    rw [length_delimited_after before remaining value tag count hc hr] at hs
    have hfit : value.val ≤ remaining.length := by
      by_contra hn
      simp only [fixedResult,if_pos (by omega : remaining.length < value.val)] at hs
      cases hs
    simp only [fixedResult,if_neg (by omega : ¬remaining.length < value.val)] at hs
    exact ⟨value,remaining,hr,hfit,(congrArg Prod.snd (Result.ok.inj hs)).symm⟩

/-- Actual successful nested length-delimited skipping, including empty payloads,
agrees with the entire public scan interval and all preserved field state. -/
theorem nested_length_scan (bytes middle after : Slice U8) (position : Nat) (tag count : U32)
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hpos : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hs : state.ok = 255) (hn : state.next = BitVec.ofNat 64 position)
    (hd : state.depth ≠ 0) (hlimit : state.depth.toNat ≤ 99)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,.LengthDelimited),middle))
    (hskip : LoopSupportSkip.encoding.skip_field sliceBuf .LengthDelimited tag middle ⟨count⟩ = .ok (.Ok (),after)) :
    let rows := ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)
    ∃ finish, position < finish ∧ finish ≤ bytes.length ∧ after = drop bytes finish ∧
      let result := ProtoParse.step Word64.concrete ByteAuth.concrete bytes.length rows state position
      result.ok = 255 ∧ result.next = BitVec.ofNat 64 finish ∧ result.depth = state.depth ∧
      result.fields = state.fields ∧
      (List.range' position (finish-position)).foldl
        (ProtoParse.step Word64.concrete ByteAuth.concrete bytes.length rows) state = result := by
  obtain ⟨value,payloadAfter,hv,hfit,hfinal⟩ := length_success_decode middle after tag count hskip
  dsimp only
  let rows := ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)
  let key := rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
  have keyData : ∃ count, 1 ≤ count ∧ count ≤ 10 ∧ position+count ≤ bytes.length ∧
      middle = drop bytes (position+count) ∧ key.ok = 255 ∧
      key.stop = BitVec.ofNat 64 (position+count) ∧ key.value.toNat ≤ 4294967295 ∧ key.value >>> 3 ≠ 0 ∧
      key.value >>> 3 = BitVec.ofNat 64 tag.val ∧ key.value &&& 7 = 2 ∧
      (keyFields Word64.concrete ByteAuth.concrete key).ok = 255 := actual_key_row bytes middle position tag .LengthDelimited hpos hk
  obtain ⟨kc,hk1,hk10,hkb,hrest,hkok,hkstop,hkrange,hknz,_,hkind,hkmask⟩ := keyData
  have hnonempty : 0 < middle.length := by
    obtain ⟨r,rest,hr,_,hlt⟩ := varint_total middle
    rw [hv] at hr
    cases hr
    have h := hlt value rfl
    omega
  have hstart : position+kc < bytes.length := by rw [hrest,drop_length] at hnonempty; omega
  have hv' : LoopSupportSkip.encoding.varint.decode_varint sliceBuf (drop bytes (position+kc)) = .ok (.Ok value,payloadAfter) := by simpa only [hrest] using hv
  obtain ⟨pc,hp1,_,hpb,hafter,hpayload⟩ := payload_actual_success bytes payloadAfter position kc value hk1 hk10 hstart (by omega) hv'
  let payload := ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1) ((rows.drop (position+1)).take 10)
  have hpay : payload = ⟨255,BitVec.ofNat 64 (position+kc+pc),value.bv⟩ := by
    dsimp only [payload]
    rw [hkstop]
    exact hpayload
  let p := ProtoParse.plan Word64.concrete ByteAuth.concrete bytes.length key payload state
  have hstartNat : (BitVec.ofNat 64 (position+kc+pc)).toNat = position+kc+pc := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have hfitAbs : value.val ≤ bytes.length-(position+kc+pc) := by rw [hafter,drop_length] at hfit; exact hfit
  have hbound : position+kc+pc+value.val ≤ bytes.length := by omega
  have hgood : p.ok = 255 := by
    rw [length_in_group bytes.length key payload state hkok hkrange hknz hkind hd hlimit,hpay]
    change 255 &&& Word64.concrete.ule value.bv
      (BitVec.ofNat 64 bytes.length - BitVec.ofNat 64 (position+kc+pc)) = 255
    rw [length_bounds _ _ bytes.length (by rw [hstartNat]; omega) hcap]
    simp only [UScalar.bv_toNat,hstartNat,if_pos hfitAbs]
    rfl
  have hstop : p.stop = BitVec.ofNat 64 (position+kc+pc+value.val) := by
    rw [length_stop bytes.length key payload state hkind,hpay]
    have hb : value.val < 2^64 := by have h := value.bv.isLt; simpa only [UScalar.bv_toNat] using h
    have hval : value.bv = BitVec.ofNat 64 value.val := by
      apply BitVec.eq_of_toNat_eq
      simp only [UScalar.bv_toNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hb]
    change BitVec.ofNat 64 (position+kc+pc) + value.bv = _
    rw [hval]
    simp only [BitVec.ofNat_add]
  have hpkind : p.kind = 2 := hkind
  have hstep : ProtoParse.step Word64.concrete ByteAuth.concrete bytes.length rows state position =
      ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state := by
    change ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position
      (ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete bytes.length position _ key payload state) state = _
    rw [successful_plan _ _ _ _ _ _ hkmask hgood]
  have hleaf := apply_nested_leaf position p state hs hgood hn hd (by rw [hpkind]; decide) (by rw [hpkind]; decide)
  have hnext : (ProtoParse.step Word64.concrete ByteAuth.concrete bytes.length rows state position).next =
      BitVec.ofNat 64 (position+kc+pc+value.val) := by rw [hstep,hleaf.2.1,hstop]
  refine ⟨position+kc+pc+value.val,by omega,hbound,?_,?_,hnext,?_,?_,?_⟩
  · rw [hfinal,hafter,drop_add]
  · rw [hstep]; exact hleaf.1
  · rw [hstep]; exact hleaf.2.2.1
  · rw [hstep]; exact hleaf.2.2.2
  · exact scan_step_interval bytes.length position (position+kc+pc+value.val) rows state _ rfl hnext (by omega) hbound hcap

#print axioms nested_length_scan
end FullParserV3
