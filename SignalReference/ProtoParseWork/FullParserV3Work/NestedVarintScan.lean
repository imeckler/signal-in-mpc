import ProtoParseWork.FullParserV3Work.KeyRow
import ProtoParseWork.FullParserV3Work.NumericLeaf
import ProtoParseWork.FullParserV3Work.Intervals
import ProtoParseWork.FullParserV3Work.SkipTotality
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkipBuf
open LibSignalReference.Candidate.ProstTopField LibSignalReference.Candidate.ProstSkipKey
open LibSignalReference.Candidate.ProstSkipPlan
set_option maxHeartbeats 3000000

/-- One arbitrary successful nested varint field is consumed by exactly its
public scan interval. Both decoder correspondences are discharged from actual
Rust calls; payload bytes cannot mutate top-level fields. -/
theorem nested_varint_scan (bytes middle after : Slice U8) (position : Nat) (tag : U32) (value : U64)
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hpos : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hs : state.ok = 255) (hn : state.next = BitVec.ofNat 64 position)
    (hd : state.depth ≠ 0) (hlimit : state.depth.toNat ≤ 99)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,.Varint),middle))
    (hv : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok value,after)) :
    let rows := ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)
    ∃ finish, position < finish ∧ finish ≤ bytes.length ∧ after = drop bytes finish ∧
      let result := ProtoParse.step Word64.concrete ByteAuth.concrete bytes.length rows state position
      result.ok = 255 ∧ result.next = BitVec.ofNat 64 finish ∧ result.depth = state.depth ∧
      result.fields = state.fields ∧
      (List.range' position (finish-position)).foldl
        (ProtoParse.step Word64.concrete ByteAuth.concrete bytes.length rows) state = result := by
  dsimp only
  let rows := ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)
  let key := rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
  have keyData : ∃ count, 1 ≤ count ∧ count ≤ 10 ∧ position+count ≤ bytes.length ∧
      middle = drop bytes (position+count) ∧ key.ok = 255 ∧
      key.stop = BitVec.ofNat 64 (position+count) ∧ key.value.toNat ≤ 4294967295 ∧ key.value >>> 3 ≠ 0 ∧
      key.value >>> 3 = BitVec.ofNat 64 tag.val ∧ key.value &&& 7 = 0 ∧
      (keyFields Word64.concrete ByteAuth.concrete key).ok = 255 := actual_key_row bytes middle position tag .Varint hpos hk
  obtain ⟨kc,hk1,hk10,hkb,hrest,hkok,hkstop,hkrange,hknz,_,hkind,hkmask⟩ := keyData
  have hnonempty : 0 < middle.length := by
    obtain ⟨r,rest,hr,_,hlt⟩ := varint_total middle
    rw [hv] at hr
    cases hr
    have h := hlt value rfl
    omega
  have hstart : position+kc < bytes.length := by rw [hrest,drop_length] at hnonempty; omega
  have hv' : LoopSupportSkip.encoding.varint.decode_varint sliceBuf (drop bytes (position+kc)) = .ok (.Ok value,after) := by simpa only [hrest] using hv
  obtain ⟨pc,hp1,_,hpb,hafter,hpayload⟩ := payload_actual_success bytes after position kc value hk1 hk10 hstart (by omega) hv'
  let payload := ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1) ((rows.drop (position+1)).take 10)
  have hpay : payload = ⟨255,BitVec.ofNat 64 (position+kc+pc),value.bv⟩ := by
    dsimp only [payload]
    rw [hkstop]
    exact hpayload
  let p := ProtoParse.plan Word64.concrete ByteAuth.concrete bytes.length key payload state
  have hgood : p.ok = 255 := by
    rw [varint_in_group bytes.length key payload state hkok hkrange hknz hkind hd hlimit,hpay]
  have hstop : p.stop = BitVec.ofNat 64 (position+kc+pc) := by
    rw [varint_stop bytes.length key payload state hkind,hpay]
  have hpkind : p.kind = 0 := hkind
  have hstep : ProtoParse.step Word64.concrete ByteAuth.concrete bytes.length rows state position =
      ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state := by
    change ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position
      (ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete bytes.length position _ key payload state) state = _
    rw [successful_plan _ _ _ _ _ _ hkmask hgood]
  have hleaf := apply_nested_leaf position p state hs hgood hn hd (by rw [hpkind]; decide) (by rw [hpkind]; decide)
  have hnext : (ProtoParse.step Word64.concrete ByteAuth.concrete bytes.length rows state position).next =
      BitVec.ofNat 64 (position+kc+pc) := by rw [hstep,hleaf.2.1,hstop]
  refine ⟨position+kc+pc,by omega,hpb,hafter,?_,hnext,?_,?_,?_⟩
  · rw [hstep]; exact hleaf.1
  · rw [hstep]; exact hleaf.2.2.1
  · rw [hstep]; exact hleaf.2.2.2
  · exact scan_step_interval bytes.length position (position+kc+pc) rows state _ rfl hnext (by omega) hpb hcap

#print axioms nested_varint_scan
end FullParserV3
