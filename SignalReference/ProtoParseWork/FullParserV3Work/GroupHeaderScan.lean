import ProtoParseWork.FullParserV3Work.GroupNumeric
import ProtoParseWork.FullParserV3Work.NestedLengthScan
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipSlice LibSignalReference.Candidate.ProstSkipBuf
open LibSignalReference.Candidate.ProstTopField LibSignalReference.Candidate.ProstSkipKey
open LibSignalReference.Candidate.ProstSkipPlan
set_option maxHeartbeats 3000000

/-- An actual StartGroup key pushes exactly its Rust tag into the live numeric
frame prefix, including an unknown top-level group. The header's whole public
scan interval is accounted for before group-body induction. -/
theorem group_start_scan (bytes middle : Slice U8) (position : Nat) (tag : U32) (tags : List U32)
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hpos : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hs : state.ok = 255) (hn : state.next = BitVec.ofNat 64 position)
    (hf : Frames state.depth state.stack tags) (hcursor : tags.length ≤ position)
    (hlimit : tags.length ≤ 99) (hstack : state.stack.length = min 100 bytes.length)
    (hfields : state.fields.length ≤ 6) (hskip : state.depth ≠ 0 ∨ 6 < tag.val)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,.StartGroup),middle)) :
    let rows := ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)
    ∃ finish, position < finish ∧ finish ≤ bytes.length ∧ middle = drop bytes finish ∧
      let result := ProtoParse.step Word64.concrete ByteAuth.concrete bytes.length rows state position
      result.ok = 255 ∧ result.next = BitVec.ofNat 64 finish ∧
      Frames result.depth result.stack (tags++[tag]) ∧ result.fields = state.fields ∧
      result.stack.length = min 100 bytes.length ∧ (tags++[tag]).length ≤ finish ∧
      (List.range' position (finish-position)).foldl
        (ProtoParse.step Word64.concrete ByteAuth.concrete bytes.length rows) state = result := by
  dsimp only
  let rows := ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)
  let key := rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
  have keyData : ∃ kc, 1 ≤ kc ∧ kc ≤ 10 ∧ position+kc ≤ bytes.length ∧
      middle = drop bytes (position+kc) ∧ key.ok = 255 ∧ key.stop = BitVec.ofNat 64 (position+kc) ∧
      key.value.toNat ≤ 4294967295 ∧ key.value >>> 3 ≠ 0 ∧ key.value >>> 3 = BitVec.ofNat 64 tag.val ∧
      key.value &&& 7 = 3 ∧ (keyFields Word64.concrete ByteAuth.concrete key).ok = 255 :=
    actual_key_row bytes middle position tag .StartGroup hpos hk
  obtain ⟨kc,hk1,_,hkb,hrest,hkok,hkstop,hkrange,hknz,htag,hkind,hkmask⟩ := keyData
  have hdepthNat : state.depth.toNat = tags.length := by
    rw [hf.depth_eq,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have htagBound : tag.val < 2^64 := by have h := tag.bv.isLt; simp only [UScalar.bv_toNat] at h; omega
  have hskip' : state.depth ≠ 0 ∨ 6 < (key.value >>> 3).toNat := by
    rcases hskip with hd | ht
    · exact Or.inl hd
    · apply Or.inr
      rw [htag,BitVec.toNat_ofNat,Nat.mod_eq_of_lt htagBound]
      exact ht
  have hroom : tags.length < state.stack.length := by rw [hstack]; omega
  let payload := ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1) ((rows.drop (position+1)).take 10)
  let p := ProtoParse.plan Word64.concrete ByteAuth.concrete bytes.length key payload state
  have hgood : p.ok = 255 := start_skip_plan _ _ _ _ hkok hkrange hknz hkind (by omega) hskip'
  have hpkind : p.kind = 3 := hkind
  have hptag : p.tag = BitVec.ofNat 64 tag.val := htag
  have hstop : p.stop = BitVec.ofNat 64 (position+kc) := by
    rw [group_stop bytes.length key payload state (Or.inl hkind),hkstop]
  have hstep : ProtoParse.step Word64.concrete ByteAuth.concrete bytes.length rows state position =
      ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state := by
    change ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position
      (ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete bytes.length position _ key payload state) state = _
    rw [successful_plan _ _ _ _ _ _ hkmask hgood]
  have hnext : (ProtoParse.step Word64.concrete ByteAuth.concrete bytes.length rows state position).next =
      BitVec.ofNat 64 (position+kc) := by rw [hstep,apply_next position p state hs hgood hn,hstop]
  refine ⟨position+kc,by omega,hkb,hrest,?_,hnext,?_,?_,?_,?_,?_⟩
  · rw [hstep]; exact apply_success_ok position p state hs hgood hn
  · rw [hstep]; exact apply_start_frames position p state tags tag hf hroom hs hgood hn hpkind hptag
  · rw [hstep]; exact apply_skip_fields position p state hs hgood hn hfields hskip'
  · rw [hstep,apply_start_stack position p state hs hgood hn hpkind,write_stack_length,hstack]
  · simp only [List.length_append,List.length_singleton]; omega
  · exact scan_step_interval bytes.length position (position+kc) rows state _ rfl hnext (by omega) hkb hcap

/-- A matching actual EndGroup key restores the exact prior live frame prefix.
The depth100 closing case is included; closing does not enter child recursion. -/
theorem group_end_scan (bytes after : Slice U8) (position : Nat) (tag : U32) (tags : List U32)
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hpos : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hs : state.ok = 255) (hn : state.next = BitVec.ofNat 64 position)
    (hf : Frames state.depth state.stack (tags++[tag]))
    (hcursor : (tags++[tag]).length ≤ position) (hstack : state.stack.length = min 100 bytes.length)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,.EndGroup),after)) :
    let rows := ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)
    ∃ finish, position < finish ∧ finish ≤ bytes.length ∧ after = drop bytes finish ∧
      let result := ProtoParse.step Word64.concrete ByteAuth.concrete bytes.length rows state position
      result.ok = 255 ∧ result.next = BitVec.ofNat 64 finish ∧
      Frames result.depth result.stack tags ∧ result.fields = state.fields ∧
      result.stack.length = min 100 bytes.length ∧ tags.length ≤ finish ∧
      (List.range' position (finish-position)).foldl
        (ProtoParse.step Word64.concrete ByteAuth.concrete bytes.length rows) state = result := by
  dsimp only
  let rows := ProtoParse.table VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes)
  let key := rows[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩
  have keyData : ∃ kc, 1 ≤ kc ∧ kc ≤ 10 ∧ position+kc ≤ bytes.length ∧
      after = drop bytes (position+kc) ∧ key.ok = 255 ∧ key.stop = BitVec.ofNat 64 (position+kc) ∧
      key.value.toNat ≤ 4294967295 ∧ key.value >>> 3 ≠ 0 ∧ key.value >>> 3 = BitVec.ofNat 64 tag.val ∧
      key.value &&& 7 = 4 ∧ (keyFields Word64.concrete ByteAuth.concrete key).ok = 255 :=
    actual_key_row bytes after position tag .EndGroup hpos hk
  obtain ⟨kc,hk1,_,hkb,hrest,hkok,hkstop,hkrange,hknz,htag,hkind,hkmask⟩ := keyData
  have hbound : tags.length+1 ≤ 100 := by simpa only [List.length_append,List.length_singleton] using hf.bound.trans hf.limit
  have hdepthNat : state.depth.toNat = tags.length+1 := by
    have hb : (tags++[tag]).length < 2^64 := by simp only [List.length_append,List.length_singleton]; omega
    rw [hf.depth_eq,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hb]
    simp only [List.length_append,List.length_singleton]
  have hd : state.depth ≠ 0 := by intro hz; rw [hz] at hdepthNat; change 0 = tags.length+1 at hdepthNat; omega
  let payload := ProtoParse.lookupDecoded Word64.concrete ByteAuth.concrete key.stop (position+1) ((rows.drop (position+1)).take 10)
  let p := ProtoParse.plan Word64.concrete ByteAuth.concrete bytes.length key payload state
  have hgood : p.ok = 255 := by
    rw [end_in_group bytes.length key payload state hkok hkrange hknz hkind hd,frames_top tag hf,htag]
    exact if_pos rfl
  have hpkind : p.kind = 4 := hkind
  have hstop : p.stop = BitVec.ofNat 64 (position+kc) := by
    rw [group_stop bytes.length key payload state (Or.inr hkind),hkstop]
  have hstep : ProtoParse.step Word64.concrete ByteAuth.concrete bytes.length rows state position =
      ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state := by
    change ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position
      (ProtoParse.planWithCursor Word64.concrete ByteAuth.concrete bytes.length position _ key payload state) state = _
    rw [successful_plan _ _ _ _ _ _ hkmask hgood]
  have hnext : (ProtoParse.step Word64.concrete ByteAuth.concrete bytes.length rows state position).next =
      BitVec.ofNat 64 (position+kc) := by rw [hstep,apply_next position p state hs hgood hn,hstop]
  refine ⟨position+kc,by omega,hkb,hrest,?_,hnext,?_,?_,?_,?_,?_⟩
  · rw [hstep]; exact apply_success_ok position p state hs hgood hn
  · rw [hstep]; exact apply_end_frames position p state tags tag hf hs hgood hn hpkind
  · rw [hstep]; exact nested_fields_unchanged position p state hd
  · rw [hstep,apply_end_stack position p state hpkind,hstack]
  · simp only [List.length_append,List.length_singleton] at hcursor; omega
  · exact scan_step_interval bytes.length position (position+kc) rows state _ rfl hnext (by omega) hkb hcap

#print axioms group_end_scan

#print axioms group_start_scan
end FullParserV3
