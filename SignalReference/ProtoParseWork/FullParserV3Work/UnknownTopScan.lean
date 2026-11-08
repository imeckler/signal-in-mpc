import ProtoParseWork.FullParserV3Work.UnknownShadow
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 3000000

/-- Transfers already proved actual nested leaf transitions through the exact
numeric shadow equality. The production result retains its own zero depth,
complete fields and original scratch stack. -/
private theorem transfer_unknown_leaf (bytes middle after : Slice U8) (position : Nat) (tag : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512) (hat : StateAt bytes position state [])
    (ht : 6 < tag.val) (h3 : kind ≠ .StartGroup) (h4 : kind ≠ .EndGroup)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle))
    (hnested : ∃ finish, position < finish ∧ finish ≤ bytes.length ∧ after = drop bytes finish ∧
      (stepOf bytes {state with depth := 1} position).ok = 255 ∧
      (stepOf bytes {state with depth := 1} position).next = BitVec.ofNat 64 finish) : SkipScan bytes position state after [] := by
  obtain ⟨_,_,_,_,_,_,_,_,_,htag,hkind,hkmask⟩ := actual_key_row bytes middle position tag kind hp hk
  have hb : tag.val < 2^64 := by have h := tag.bv.isLt; simp only [UScalar.bv_toNat] at h; omega
  have htag' : 6 < (((rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩).value >>> 3).toNat := by
    rw [htag,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hb]; exact ht
  have hk3 : ((rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩).value &&& 7 ≠ 3 := by
    rw [hkind]; cases kind <;> simp_all [wireNumber]
  have hk4 : ((rowsOf bytes)[position]?.getD ⟨0,BitVec.ofNat 64 position,0⟩).value &&& 7 ≠ 4 := by
    rw [hkind]; cases kind <;> simp_all [wireNumber]
  have ho := unknown_step_shadow bytes.length position (rowsOf bytes) state hat.frames.depth_eq
    (by rw [hat.fields_size]) htag' hk3 hk4 hkmask
  obtain ⟨finish,hp',hb',ha,hs,hn⟩ := hnested
  have hok : (stepOf bytes state position).ok = 255 := ho.1.trans hs
  have hnext : (stepOf bytes state position).next = BitVec.ofNat 64 finish := ho.2.1.trans hn
  have hd : (stepOf bytes state position).depth = state.depth := ho.2.2.1.trans hat.frames.depth_eq.symm
  exact package_leaf_scan bytes after position finish state [] hat hp' hb' ha hok hnext hd ho.2.2.2.1 ho.2.2.2.2
    (scan_step_interval bytes.length position finish (rowsOf bytes) state _ rfl hnext hp' hb' hcap)

theorem unknown_varint_scan (bytes middle after : Slice U8) (position : Nat) (tag : U32) (value : U64)
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512) (hat : StateAt bytes position state []) (ht : 6 < tag.val)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,.Varint),middle))
    (hv : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok value,after)) : SkipScan bytes position state after [] := by
  apply transfer_unknown_leaf bytes middle after position tag .Varint state hp hcap hat ht (by intro h; cases h) (by intro h; cases h) hk
  obtain ⟨finish,hp',hb,ha,hs,hn,_,_,_⟩ := nested_varint_scan bytes middle after position tag value {state with depth := 1}
    hp hcap hat.ok hat.cursor (by change (1 : BitVec 64) ≠ 0; decide) (by change (1 : BitVec 64).toNat ≤ 99; decide) hk hv
  exact ⟨finish,hp',hb,ha,hs,hn⟩

theorem unknown_fixed_scan (bytes middle after : Slice U8) (position : Nat) (tag count : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (width : Nat) (hw : FixedWidth kind width)
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512) (hat : StateAt bytes position state []) (ht : 6 < tag.val)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle))
    (hv : LoopSupportSkip.encoding.skip_field sliceBuf kind tag middle ⟨count⟩ = .ok (.Ok (),after)) : SkipScan bytes position state after [] := by
  have h3 : kind ≠ .StartGroup := by rcases hw with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> intro h <;> cases h
  have h4 : kind ≠ .EndGroup := by rcases hw with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> intro h <;> cases h
  apply transfer_unknown_leaf bytes middle after position tag kind state hp hcap hat ht h3 h4 hk
  obtain ⟨finish,hp',hb,ha,hs,hn,_,_,_⟩ := nested_fixed_scan bytes middle after position tag count kind width hw {state with depth := 1}
    hp hcap hat.ok hat.cursor (by change (1 : BitVec 64) ≠ 0; decide) (by change (1 : BitVec 64).toNat ≤ 99; decide) hk hv
  exact ⟨finish,hp',hb,ha,hs,hn⟩

theorem unknown_length_scan (bytes middle after : Slice U8) (position : Nat) (tag count : U32)
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512) (hat : StateAt bytes position state []) (ht : 6 < tag.val)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,.LengthDelimited),middle))
    (hv : LoopSupportSkip.encoding.skip_field sliceBuf .LengthDelimited tag middle ⟨count⟩ = .ok (.Ok (),after)) : SkipScan bytes position state after [] := by
  apply transfer_unknown_leaf bytes middle after position tag .LengthDelimited state hp hcap hat ht (by intro h; cases h) (by intro h; cases h) hk
  obtain ⟨finish,hp',hb,ha,hs,hn,_,_,_⟩ := nested_length_scan bytes middle after position tag count {state with depth := 1}
    hp hcap hat.ok hat.cursor (by change (1 : BitVec 64) ≠ 0; decide) (by change (1 : BitVec 64).toNat ≤ 99; decide) hk hv
  exact ⟨finish,hp',hb,ha,hs,hn⟩

#print axioms unknown_varint_scan
#print axioms unknown_fixed_scan
#print axioms unknown_length_scan
end FullParserV3
