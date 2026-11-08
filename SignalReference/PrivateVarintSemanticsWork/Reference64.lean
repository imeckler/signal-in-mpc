import PrivateVarintSemanticsWork.Reference

namespace LibSignalReference.Candidate.PrivateVarint
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
open LibSignalReference.Candidate.ProstEncoding
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem group_value64 (word : BitVec 64) (index : Nat) (hi : index<10) :
    OpenResult.get ByteAuth.concrete (Varint64.groups Varint64.concrete word) index =
      BitVec.ofNat 8 (word.toNat / 128^index % 128) := by
  simp only [Varint64.groups,OpenResult.get,List.getElem?_map,List.getElem?_range hi,
    Option.map_some,Option.getD_some,Varint64.concrete,ByteAuth.concrete]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.extractLsb'_toNat,BitVec.toNat_ofNat]
  have hm (n : Nat) : n &&& 127=n%128 := by
    simpa using Nat.and_two_pow_sub_one_eq_mod n 7
  have mask : (127 : BitVec 8).toNat=127 := by decide
  simp only [mask,Nat.shiftRight_eq_div_pow,hm]
  have hp : 2^(7*index)=128^index := by rw [Nat.pow_mul]
  rw [hp]
  omega

theorem groups_values64 (word : BitVec 64) :
    Varint64.groups Varint64.concrete word =
      (List.range 10).map (fun index => BitVec.ofNat 8 (word.toNat/128^index%128)) := by
  unfold Varint64.groups
  apply List.map_congr_left
  intro index hi
  have hb := List.mem_range.mp hi
  simpa only [Varint64.groups,OpenResult.get,List.getElem?_map,List.getElem?_range hb,
    Option.map_some,Option.getD_some] using group_value64 word index hb

theorem groups_naturals64 (word : BitVec 64) :
    (Varint64.groups Varint64.concrete word).map BitVec.toNat =
      (List.range 10).map (fun index => word.toNat/128^index%128) := by
  rw [groups_values64,List.map_map]
  apply List.map_congr_left
  intro index hi
  simp only [Function.comp_def,BitVec.toNat_ofNat]
  omega

theorem canonical_width_bounds64 (word : BitVec 64) (width : Nat)
    (hw : 0<width) (hl : width≤10)
    (canonical : Varint64.canonicalGroups (Varint64.groups Varint64.concrete word) width) :
    word.toNat<128^width ∧ (width=1 ∨ 128^(width-1)≤word.toNat) := by
  have hz := congrArg (List.map BitVec.toNat) canonical.1
  simp only [List.map_drop,List.map_replicate,groups_naturals64] at hz
  have ht : width=1 ∨ word.toNat/128^(width-1)%128≠0 := by
    rcases canonical.2 with h|h
    · exact Or.inl h
    · right
      intro hn
      apply h
      rw [group_value64 word (width-1) (by omega),hn]
      rfl
  have wordBound : word.toNat<18446744073709551616 := word.isLt
  have widths : width=1 ∨ width=2 ∨ width=3 ∨ width=4 ∨ width=5 ∨
      width=6 ∨ width=7 ∨ width=8 ∨ width=9 ∨ width=10 := by omega
  rcases widths with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [List.range_succ] at hz ht ⊢ <;> omega

theorem encode_fixed64 (word : BitVec 64) (width : Nat) (hl : width≤10) :
    Varint64.encode Varint64.concrete ByteAuth.concrete word width = fixedBytes word.toNat width := by
  unfold Varint64.encode Varint.encodeGroups fixedBytes
  apply List.map_congr_left
  intro index hi
  have hb := List.mem_range.mp hi
  rw [group_value64 word index (by omega)]
  by_cases hc : index+1<width
  · simpa only [if_pos hc,ByteAuth.concrete] using
      byte_xor_continuation (word.toNat/128^index%128) (by omega)
  · simp only [if_neg hc,ByteAuth.concrete,BitVec.xor_zero,Nat.add_zero]

theorem encode_publicNat64 (word : BitVec 64) (width : Nat) (hw : 0<width) (hl : width≤10)
    (canonical : Varint64.canonicalGroups (Varint64.groups Varint64.concrete word) width) :
    Varint64.encode Varint64.concrete ByteAuth.concrete word width = Varint.publicNat ByteAuth.concrete word.toNat := by
  obtain ⟨upper,lower⟩ := canonical_width_bounds64 word width hw hl canonical
  rw [encode_fixed64 word width hl,Varint.publicNat]
  exact (publicNatLoop_fixed 10 width word.toNat hw hl upper lower).symm

theorem canonical_uint64_exists (word : BitVec 64) :
    ∃ width, 0<width ∧ width≤10 ∧
      Varint64.canonicalGroups (Varint64.groups Varint64.concrete word) width := by
  have wordBound : word.toNat<18446744073709551616 := word.isLt
  by_cases h1 : word.toNat<128
  · refine ⟨1,by omega,by omega,?_⟩
    rw [groups_values64]
    simp [Varint64.canonicalGroups,List.range_succ,OpenResult.get,ByteAuth.concrete]
    simp only [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.reducePow]
    omega
  by_cases h2 : word.toNat<16384
  · refine ⟨2,by omega,by omega,?_⟩
    rw [groups_values64]
    simp [Varint64.canonicalGroups,List.range_succ,OpenResult.get,ByteAuth.concrete]
    simp only [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.reducePow]
    omega
  by_cases h3 : word.toNat<2097152
  · refine ⟨3,by omega,by omega,?_⟩
    rw [groups_values64]
    simp [Varint64.canonicalGroups,List.range_succ,OpenResult.get,ByteAuth.concrete]
    simp only [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.reducePow]
    omega
  by_cases h4 : word.toNat<268435456
  · refine ⟨4,by omega,by omega,?_⟩
    rw [groups_values64]
    simp [Varint64.canonicalGroups,List.range_succ,OpenResult.get,ByteAuth.concrete]
    simp only [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.reducePow]
    omega
  by_cases h5 : word.toNat<34359738368
  · refine ⟨5,by omega,by omega,?_⟩
    rw [groups_values64]
    simp [Varint64.canonicalGroups,List.range_succ,OpenResult.get,ByteAuth.concrete]
    simp only [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.reducePow]
    omega
  by_cases h6 : word.toNat<4398046511104
  · refine ⟨6,by omega,by omega,?_⟩
    rw [groups_values64]
    simp [Varint64.canonicalGroups,List.range_succ,OpenResult.get,ByteAuth.concrete]
    simp only [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.reducePow]
    omega
  by_cases h7 : word.toNat<562949953421312
  · refine ⟨7,by omega,by omega,?_⟩
    rw [groups_values64]
    simp [Varint64.canonicalGroups,List.range_succ,OpenResult.get,ByteAuth.concrete]
    simp only [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.reducePow]
    omega
  by_cases h8 : word.toNat<72057594037927936
  · refine ⟨8,by omega,by omega,?_⟩
    rw [groups_values64]
    simp [Varint64.canonicalGroups,List.range_succ,OpenResult.get,ByteAuth.concrete]
    simp only [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.reducePow]
    omega
  by_cases h9 : word.toNat<9223372036854775808
  · refine ⟨9,by omega,by omega,?_⟩
    rw [groups_values64]
    simp [Varint64.canonicalGroups,List.range_succ,OpenResult.get,ByteAuth.concrete]
    simp only [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.reducePow]
    omega
  · refine ⟨10,by omega,by omega,?_⟩
    rw [groups_values64]
    simp [Varint64.canonicalGroups,List.range_succ,OpenResult.get,ByteAuth.concrete]
    simp only [BitVec.toNat_eq,BitVec.toNat_ofNat,Nat.reducePow]
    omega

theorem actual_uint64_private_wire (value : U64) (width : Nat)
    (hw : 0<width) (hl : width≤10)
    (canonical : Varint64.canonicalGroups (Varint64.groups Varint64.concrete value.bv) width)
    (buf : alloc.vec.Vec U8) (hsize : buf.length+10≤Usize.max) :
    ∃ after, _root_.ProstEncoding.encoding.varint.encode_varint vecDictionary value buf = .ok after ∧
      PrivateBuffer.output ByteAuth.concrete (PrivateVarint.uint64 Varint64.concrete ByteAuth.concrete value.bv) =
        255 :: (BitVec.ofNat 8 (width/256) :: BitVec.ofNat 8 width ::
          ((vecContents after).drop (vecContents buf).length ++ List.replicate (10-width) 0)) := by
  have enc : Varint64.encode Varint64.concrete ByteAuth.concrete value.bv width =
      Varint.publicNat ByteAuth.concrete value.val := by
    simpa only [UScalar.bv_toNat] using encode_publicNat64 value.bv width hw hl canonical
  obtain ⟨after,ha,hv⟩ := vec_encode_appends value buf hsize
  refine ⟨after,ha,?_⟩
  rw [hv,List.drop_left,←enc]
  exact PrivateVarint.uint64_wire value.bv width hw hl canonical

theorem actual_uint64_private_wire_total (value : U64)
    (buf : alloc.vec.Vec U8) (hsize : buf.length+10≤Usize.max) :
    ∃ after, _root_.ProstEncoding.encoding.varint.encode_varint vecDictionary value buf = .ok after ∧
      let written := (vecContents after).drop (vecContents buf).length
      PrivateBuffer.output ByteAuth.concrete (PrivateVarint.uint64 Varint64.concrete ByteAuth.concrete value.bv) =
        255 :: (BitVec.ofNat 8 (written.length/256) :: BitVec.ofNat 8 written.length ::
          (written ++ List.replicate (10-written.length) 0)) := by
  obtain ⟨width,hw,hl,canonical⟩ := canonical_uint64_exists value.bv
  have enc : Varint64.encode Varint64.concrete ByteAuth.concrete value.bv width =
      Varint.publicNat ByteAuth.concrete value.val := by
    simpa only [UScalar.bv_toNat] using encode_publicNat64 value.bv width hw hl canonical
  obtain ⟨after,ha,hv⟩ := vec_encode_appends value buf hsize
  refine ⟨after,ha,?_⟩
  simp only [hv,List.drop_left,←enc]
  have len : (Varint64.encode Varint64.concrete ByteAuth.concrete value.bv width).length=width := by
    simp [Varint64.encode,Varint.encodeGroups]
  simp only [len]
  exact PrivateVarint.uint64_wire value.bv width hw hl canonical

open _root_.Std.Tactic.BVDecide

theorem compiled_actual_uint64_private_wire_total (value : U64)
    (buf : alloc.vec.Vec U8) (hsize : buf.length+10≤Usize.max)
    (secret : BVExpr 64) (assign : BVExpr.Assignment) (hsecret : secret.eval assign=value.bv) :
    let wire := PrivateBuffer.output ByteAuth.symbolic (PrivateVarint.uint64 Varint64.symbolic ByteAuth.symbolic secret)
    ∃ after, _root_.ProstEncoding.encoding.varint.encode_varint vecDictionary value buf = .ok after ∧
      let written := (vecContents after).drop (vecContents buf).length
      ∀ (index : Nat) (hi : index<8*wire.length),
        AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr wire)).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr wire)).vec.get index hi)) =
        (ByteCircuit.joinValue (255 :: (BitVec.ofNat 8 (written.length/256) :: BitVec.ofNat 8 written.length ::
          (written ++ List.replicate (10-written.length) 0)))).getLsbD index := by
  obtain ⟨after,ha,wireEq⟩ := actual_uint64_private_wire_total value buf hsize
  refine ⟨after,ha,?_⟩
  dsimp only at wireEq ⊢
  intro index hi
  rw [PrivateVarint.compiled_uint64_correct secret assign index hi,hsecret,wireEq]

theorem compiled_actual_uint32_private_wire_total (value : U32)
    (buf : alloc.vec.Vec U8) (hsize : buf.length+10≤Usize.max)
    (secret : BVExpr 32) (assign : BVExpr.Assignment) (hsecret : secret.eval assign=value.bv) :
    let wire := PrivateBuffer.output ByteAuth.symbolic (PrivateVarint.uint32 Sha256.symbolic ByteAuth.symbolic secret)
    ∃ after, _root_.ProstEncoding.encoding.varint.encode_varint vecDictionary (UScalar.cast .U64 value) buf = .ok after ∧
      let written := (vecContents after).drop (vecContents buf).length
      ∀ (index : Nat) (hi : index<8*wire.length),
        AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr wire)).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr wire)).vec.get index hi)) =
        (ByteCircuit.joinValue (255 :: (BitVec.ofNat 8 (written.length/256) :: BitVec.ofNat 8 written.length ::
          (written ++ List.replicate (5-written.length) 0)))).getLsbD index := by
  obtain ⟨after,ha,wireEq⟩ := actual_uint32_private_wire_total value buf hsize
  refine ⟨after,ha,?_⟩
  dsimp only at wireEq ⊢
  intro index hi
  rw [PrivateVarint.compiled_uint32_correct secret assign index hi,hsecret,wireEq]

end LibSignalReference.Candidate.PrivateVarint
