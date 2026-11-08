import ProtoParseWork.FullParserV3Work.NestedVarintScan
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkipBuf
open LibSignalReference.Candidate.ProstTopField LibSignalReference.Candidate.ProstSkipKey
open LibSignalReference.Candidate.ProstSkipPlan LibSignalReference.Candidate.ProstSkip
set_option maxHeartbeats 3000000

def FixedWidth (kind : LoopSupportSkip.encoding.wire_type.WireType) (width : Nat) : Prop :=
  (kind = .SixtyFourBit ∧ width = 8) ∨ (kind = .ThirtyTwoBit ∧ width = 4)

private theorem fixed_skip_rule (kind : LoopSupportSkip.encoding.wire_type.WireType)
    (width : Nat) (tag count : U32) (bytes : Slice U8) (hw : FixedWidth kind width) (hc : count ≠ 0#u32) :
    LoopSupportSkip.encoding.skip_field sliceBuf kind tag bytes ⟨count⟩ = .ok (fixedResult bytes width) := by
  rcases hw with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact fixed64_reference _ _ _ hc
  · exact fixed32_reference _ _ _ hc

private theorem fixed_plan_rule (capacity : Nat)
    (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (width : Nat) (hw : FixedWidth kind width)
    (hk : key.ok = 255) (hr : key.value.toNat ≤ 4294967295) (ht : key.value >>> 3 ≠ 0)
    (hkind : key.value &&& 7 = BitVec.ofNat 64 (wireNumber kind))
    (hd : state.depth ≠ 0) (hl : state.depth.toNat ≤ 99) :
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).ok =
      Word64.concrete.ule (key.stop + BitVec.ofNat 64 width) (BitVec.ofNat 64 capacity) ∧
    (ProtoParse.plan Word64.concrete ByteAuth.concrete capacity key payload state).stop = key.stop + BitVec.ofNat 64 width := by
  rcases hw with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨fixed64_in_group _ _ _ _ hk hr ht hkind hd hl,fixed64_stop _ _ _ _ hkind⟩
  · exact ⟨fixed32_in_group _ _ _ _ hk hr ht hkind hd hl,fixed32_stop _ _ _ _ hkind⟩

/-- Both actual fixed-width skip branches agree with their entire public scan
interval, including exact suffix and preservation of all top-level fields. -/
theorem nested_fixed_scan (bytes middle after : Slice U8) (position : Nat) (tag count : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (width : Nat) (hw : FixedWidth kind width)
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hpos : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hs : state.ok = 255) (hn : state.next = BitVec.ofNat 64 position)
    (hd : state.depth ≠ 0) (hlimit : state.depth.toNat ≤ 99)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle))
    (hv : LoopSupportSkip.encoding.skip_field sliceBuf kind tag middle ⟨count⟩ = .ok (.Ok (),after)) :
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
  have keyData : ∃ kc, 1 ≤ kc ∧ kc ≤ 10 ∧ position+kc ≤ bytes.length ∧
      middle = drop bytes (position+kc) ∧ key.ok = 255 ∧ key.stop = BitVec.ofNat 64 (position+kc) ∧
      key.value.toNat ≤ 4294967295 ∧ key.value >>> 3 ≠ 0 ∧ key.value >>> 3 = BitVec.ofNat 64 tag.val ∧
      key.value &&& 7 = BitVec.ofNat 64 (wireNumber kind) ∧
      (keyFields Word64.concrete ByteAuth.concrete key).ok = 255 := actual_key_row bytes middle position tag kind hpos hk
  obtain ⟨kc,hk1,_,hkb,hrest,hkok,hkstop,hkrange,hknz,_,hkind,hkmask⟩ := keyData
  have hc : count ≠ 0#u32 := by
    intro hz
    subst count
    rw [recursion_limit_first] at hv
    cases hv
  rw [fixed_skip_rule kind width tag count middle hw hc] at hv
  have hfit : width ≤ middle.length := by
    by_contra h
    simp only [fixedResult,if_pos (by omega : middle.length < width)] at hv
    cases hv
  have hafter : after = drop middle width := by
    simp only [fixedResult,if_neg (by omega : ¬middle.length < width)] at hv
    exact (congrArg Prod.snd (Result.ok.inj hv)).symm
  have hwidth : width ≤ 8 := by rcases hw with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide
  have hbound : position+kc+width ≤ bytes.length := by rw [hrest,drop_length] at hfit; omega
  let payload := ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1) ((rows.drop (position+1)).take 10)
  let p := ProtoParse.plan Word64.concrete ByteAuth.concrete bytes.length key payload state
  have hr := fixed_plan_rule bytes.length key payload state kind width hw hkok hkrange hknz hkind hd hlimit
  have hstartNat : key.stop.toNat = position+kc := by
    rw [hkstop,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have hgood : p.ok = 255 := by
    rw [hr.1,fixed_bounds key.stop bytes.length width (by omega) hcap hwidth]
    simp only [hstartNat,if_pos (by omega : width ≤ bytes.length-(position+kc))]
  have hstop : p.stop = BitVec.ofNat 64 (position+kc+width) := by
    rw [hr.2,hkstop]
    simp only [BitVec.ofNat_add]
  have hpkind : p.kind = BitVec.ofNat 64 (wireNumber kind) := hkind
  have h3 : p.kind ≠ 3 := by rw [hpkind]; rcases hw with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> decide
  have h4 : p.kind ≠ 4 := by rw [hpkind]; rcases hw with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> decide
  have hstep : ProtoParse.step Word64.concrete ByteAuth.concrete bytes.length rows state position =
      ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state := by
    change ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position
      (ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete bytes.length position _ key payload state) state = _
    rw [successful_plan _ _ _ _ _ _ hkmask hgood]
  have hleaf := apply_nested_leaf position p state hs hgood hn hd h3 h4
  have hnext : (ProtoParse.step Word64.concrete ByteAuth.concrete bytes.length rows state position).next =
      BitVec.ofNat 64 (position+kc+width) := by rw [hstep,hleaf.2.1,hstop]
  refine ⟨position+kc+width,by omega,hbound,?_,?_,hnext,?_,?_,?_⟩
  · rw [hafter,hrest,drop_add]
  · rw [hstep]; exact hleaf.1
  · rw [hstep]; exact hleaf.2.2.1
  · rw [hstep]; exact hleaf.2.2.2
  · exact scan_step_interval bytes.length position (position+kc+width) rows state _ rfl hnext (by omega) hbound hcap

#print axioms nested_fixed_scan
end FullParserV3
