import ProtoParseWork.FullParserV3Work.SkippedMask
import ProtoParseWork.FullParserV3Work.PayloadActive
import ProtoParseWork.FullParserV3Work.FixedRejectionStep
import ProtoParseWork.FullParserV3Work.LengthRejectionStep
import ProtoParseWork.FullParserV3Work.RecursionRejectionStep
import ProtoParseWork.FullParserV3Work.SkipScanLeaves
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
open SignalMessageIntegration DispatcherIntegration
open LibSignalReference.Candidate.ProstSkipBuf
set_option maxHeartbeats 3000000

/-- Every real skipped payload-decoder failure agrees with the entire remaining
scan. Nested known-looking tags and top-level unknown tags retain all fields. -/
theorem skipped_payload_failure (bytes middle after : Slice U8) (position : Nat) (tag count : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (error : LoopSupportSkip.error.DecodeError)
    (state : State (BitVec 8) (BitVec 64)) (tags : List U32) (hp : position < bytes.length) (hcap : bytes.length ≤ 512)
    (hat : StateAt bytes position state.parser tags) (hc : count ≠ 0#u32) (hbudget : count.val+tags.length = 100)
    (ha : state.parser.depth ≠ 0 ∨ 6 < tag.val) (hkind : kind = .Varint ∨ kind = .LengthDelimited)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle))
    (hd : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Err error,after)) :
    RejectedScan bytes position state after (skipError error) state.parser.fields := by
  have hknown := valid_known_skip _ state.parser (skipped_row_allowed bytes middle position tag kind state.parser hp ha hk)
  have hi := skipped_initialization state.parser tag hat.fields_size ha
  apply active_remaining_scan bytes after position (skipError error) state state.parser.fields tags hp hat.frames
  intro positions
  exact active_fields_congr bytes after (skipError error) state _ _ _ hi
    (payload_active bytes middle after position tag kind error state hp hcap hat.ok hat.cursor hk hd hkind
      (budget_depth_limit hat count hc hbudget) hknown positions)

theorem skipped_length_failure (bytes middle rest after : Slice U8) (position : Nat) (tag count : U32)
    (raw : U64) (error : LoopSupportSkip.error.DecodeError) (state : State (BitVec 8) (BitVec 64)) (tags : List U32)
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512) (hat : StateAt bytes position state.parser tags)
    (hc : count ≠ 0#u32) (hbudget : count.val+tags.length = 100) (ha : state.parser.depth ≠ 0 ∨ 6 < tag.val)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,.LengthDelimited),middle))
    (hd : LoopSupportSkip.encoding.varint.decode_varint sliceBuf middle = .ok (.Ok raw,rest))
    (hskip : LoopSupportSkip.encoding.skip_field sliceBuf .LengthDelimited tag middle ⟨count⟩ = .ok (.Err error,after)) :
    RejectedScan bytes position state after (skipError error) state.parser.fields := by
  have hknown := valid_known_skip _ state.parser (skipped_row_allowed bytes middle position tag .LengthDelimited state.parser hp ha hk)
  have hi := skipped_initialization state.parser tag hat.fields_size ha
  apply active_remaining_scan bytes after position (skipError error) state state.parser.fields tags hp hat.frames
  intro positions
  exact active_fields_congr bytes after (skipError error) state _ _ _ hi
    (actual_length_rejection_step bytes middle rest after position tag count raw error state hp hcap hat.ok hat.cursor
      (budget_depth_limit hat count hc hbudget) hc hknown hk hd hskip positions)

theorem skipped_fixed_failure (bytes middle after : Slice U8) (position : Nat) (tag count : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (width : Nat) (hw : FixedWidth kind width)
    (error : LoopSupportSkip.error.DecodeError) (state : State (BitVec 8) (BitVec 64)) (tags : List U32)
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512) (hat : StateAt bytes position state.parser tags)
    (hc : count ≠ 0#u32) (hbudget : count.val+tags.length = 100) (ha : state.parser.depth ≠ 0 ∨ 6 < tag.val)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle))
    (hskip : LoopSupportSkip.encoding.skip_field sliceBuf kind tag middle ⟨count⟩ = .ok (.Err error,after)) :
    RejectedScan bytes position state after (skipError error) state.parser.fields :=
  active_remaining_scan bytes after position (skipError error) state state.parser.fields tags hp hat.frames
    (actual_fixed_rejection_step bytes middle after position tag count kind width hw error state hp hcap hat.ok hat.cursor
      hat.fields_size (budget_depth_limit hat count hc hbudget) hc
      (skipped_row_allowed bytes middle position tag kind state.parser hp ha hk) hk hskip)

theorem skipped_limit_failure (bytes middle after : Slice U8) (position : Nat) (tag : U32)
    (kind : LoopSupportSkip.encoding.wire_type.WireType) (hn : kind ≠ .EndGroup)
    (error : LoopSupportSkip.error.DecodeError) (state : State (BitVec 8) (BitVec 64)) (tags : List U32)
    (hp : position < bytes.length) (hcap : bytes.length ≤ 512) (hat : StateAt bytes position state.parser tags)
    (hbudget : tags.length = 100)
    (hk : LoopSupportSkip.encoding.decode_key sliceBuf (drop bytes position) = .ok (.Ok (tag,kind),middle))
    (hskip : LoopSupportSkip.encoding.skip_field sliceBuf kind tag middle ⟨0#u32⟩ = .ok (.Err error,after)) :
    RejectedScan bytes position state after (skipError error) state.parser.fields :=
  active_remaining_scan bytes after position (skipError error) state state.parser.fields tags hp hat.frames
    (actual_recursion_rejection_step bytes middle after position tag kind hn error state hp hcap hat.ok hat.cursor
      (hat.depth_nat.trans hbudget) hk hskip)

#print axioms skipped_payload_failure
#print axioms skipped_length_failure
#print axioms skipped_fixed_failure
#print axioms skipped_limit_failure
end FullParserV3.Observed
