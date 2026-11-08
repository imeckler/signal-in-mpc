import ProtoParseWork.FullParserV3Work.ScanState
import ProtoParseWork.FullParserV3Work.SkipStrict
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipBuf
set_option maxHeartbeats 3000000

theorem budget_depth_limit {bytes position state tags} (hat : StateAt bytes position state tags)
    (count : U32) (hc : count ≠ 0#u32) (hbudget : count.val+tags.length = 100) : state.depth.toNat ≤ 99 := by
  have hn : 0 < count.val := by
    by_contra h
    apply hc
    apply UScalar.eq_of_val_eq
    change count.val = 0
    omega
  rw [hat.depth_nat]
  omega

theorem varint_skip_scan (bytes middle after : Slice U8) (position : Nat) (tag count : U32) (value : U64)
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (tags : List U32)
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hat : StateAt bytes position state tags) (hn : tags ≠ [])
    (hc : count ≠ 0#u32) (hbudget : count.val+tags.length = 100)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,.Varint),middle))
    (hv : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok value,after)) :
    SkipScan bytes position state after tags := by
  obtain ⟨finish,hp',hb,ha,hs,hn',hd,hf,hscan⟩ := nested_varint_scan bytes middle after position tag value state
    hp hcap hat.ok hat.cursor (hat.nested hn) (budget_depth_limit hat count hc hbudget) hk hv
  exact package_leaf_scan bytes after position finish state tags hat hp' hb ha hs hn' hd hf
    (actual_nonstart_stack bytes middle position tag .Varint state hp (by intro h; cases h) hk) hscan

theorem fixed_skip_scan (bytes middle after : Slice U8) (position : Nat) (tag count : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (width : Nat) (hw : FixedWidth kind width)
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (tags : List U32)
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hat : StateAt bytes position state tags) (hn : tags ≠ [])
    (hc : count ≠ 0#u32) (hbudget : count.val+tags.length = 100)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle))
    (hv : LoopSupportSkip.encoding.skip_field sliceBuf kind tag middle ⟨count⟩ = .ok (.Ok (),after)) :
    SkipScan bytes position state after tags := by
  obtain ⟨finish,hp',hb,ha,hs,hn',hd,hf,hscan⟩ := nested_fixed_scan bytes middle after position tag count kind width hw state
    hp hcap hat.ok hat.cursor (hat.nested hn) (budget_depth_limit hat count hc hbudget) hk hv
  have hkind : kind ≠ .StartGroup := by rcases hw with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> intro h <;> cases h
  exact package_leaf_scan bytes after position finish state tags hat hp' hb ha hs hn' hd hf
    (actual_nonstart_stack bytes middle position tag kind state hp hkind hk) hscan

theorem length_skip_scan (bytes middle after : Slice U8) (position : Nat) (tag count : U32)
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (tags : List U32)
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hat : StateAt bytes position state tags) (hn : tags ≠ [])
    (hc : count ≠ 0#u32) (hbudget : count.val+tags.length = 100)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,.LengthDelimited),middle))
    (hv : LoopSupportSkip.encoding.skip_field sliceBuf .LengthDelimited tag middle ⟨count⟩ = .ok (.Ok (),after)) :
    SkipScan bytes position state after tags := by
  obtain ⟨finish,hp',hb,ha,hs,hn',hd,hf,hscan⟩ := nested_length_scan bytes middle after position tag count state
    hp hcap hat.ok hat.cursor (hat.nested hn) (budget_depth_limit hat count hc hbudget) hk hv
  exact package_leaf_scan bytes after position finish state tags hat hp' hb ha hs hn' hd hf
    (actual_nonstart_stack bytes middle position tag .LengthDelimited state hp (by intro h; cases h) hk) hscan

#print axioms varint_skip_scan
#print axioms fixed_skip_scan
#print axioms length_skip_scan
end FullParserV3
