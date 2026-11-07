import SkipTranslatorWork.SkipGroup

namespace LibSignalReference.Candidate.ProstSkip
open Aeneas Aeneas.Std LoopSupportSkip
open LibSignalReference.Candidate.ProstSkipBuf
set_option maxHeartbeats 500000

inductive SkipMode where
  | field (kind : encoding.wire_type.WireType)
  | group

/-- Recursive protobuf skip grammar. Decoder premises are about the separately refined
varint/key functions; no premise calls skip_field or the circuit. Recursion decreases
exactly once per group child, and end tags are checked before that decrease. -/
inductive SkipSemantics : SkipMode → U32 → U32 → Slice U8 →
    (core.result.Result Unit error.DecodeError × Slice U8) → Prop where
  | limit (kind tag bytes) : SkipSemantics (.field kind) tag 0#u32 bytes
      (.Err (decodeError .RecursionLimitReached),bytes)
  | endField {tag count bytes} (hc : count ≠ 0#u32) :
      SkipSemantics (.field .EndGroup) tag count bytes
        (.Err (decodeError .UnexpectedEndGroupTag),bytes)
  | fixed32 {tag count bytes} (hc : count ≠ 0#u32) :
      SkipSemantics (.field .ThirtyTwoBit) tag count bytes (fixedResult bytes 4)
  | fixed64 {tag count bytes} (hc : count ≠ 0#u32) :
      SkipSemantics (.field .SixtyFourBit) tag count bytes (fixedResult bytes 8)
  | varint {tag count before after value} (hc : count ≠ 0#u32)
      (hd : encoding.varint.decode_varint sliceBuf before = .ok (.Ok value,after)) :
      SkipSemantics (.field .Varint) tag count before (.Ok (),after)
  | varintError {tag count before after error} (hc : count ≠ 0#u32)
      (hd : encoding.varint.decode_varint sliceBuf before = .ok (.Err error,after)) :
      SkipSemantics (.field .Varint) tag count before (.Err error,after)
  | length {tag count before after value} (hc : count ≠ 0#u32)
      (hd : encoding.varint.decode_varint sliceBuf before = .ok (.Ok value,after)) :
      SkipSemantics (.field .LengthDelimited) tag count before (fixedResult after value.val)
  | lengthError {tag count before after error} (hc : count ≠ 0#u32)
      (hd : encoding.varint.decode_varint sliceBuf before = .ok (.Err error,after)) :
      SkipSemantics (.field .LengthDelimited) tag count before (.Err error,after)
  | start {tag count before result} (hc : count ≠ 0#u32)
      (body : SkipSemantics .group tag count before result) :
      SkipSemantics (.field .StartGroup) tag count before result
  | keyError {tag count before after error}
      (hd : encoding.decode_key sliceBuf before = .ok (.Err error,after)) :
      SkipSemantics .group tag count before (.Err error,after)
  | close {tag inner count before after}
      (hd : encoding.decode_key sliceBuf before = .ok (.Ok (inner,.EndGroup),after)) :
      SkipSemantics .group tag count before (groupClose tag inner after)
  | childError {tag inner count child before middle after kind error}
      (hk : kind ≠ .EndGroup)
      (hd : encoding.decode_key sliceBuf before = .ok (.Ok (inner,kind),middle))
      (hc : count.val = child.val + 1)
      (body : SkipSemantics (.field kind) inner child middle (.Err error,after)) :
      SkipSemantics .group tag count before (.Err error,after)
  | childNext {tag inner count child before middle after kind result}
      (hk : kind ≠ .EndGroup)
      (hd : encoding.decode_key sliceBuf before = .ok (.Ok (inner,kind),middle))
      (hc : count.val = child.val + 1)
      (body : SkipSemantics (.field kind) inner child middle (.Ok (),after))
      (rest : SkipSemantics .group tag count after result) :
      SkipSemantics .group tag count before result

def runSkipMode (mode : SkipMode) (tag count : U32) (bytes : Slice U8) :=
  match mode with
  | .field kind => encoding.skip_field sliceBuf kind tag bytes ⟨count⟩
  | .group => encoding.skip_field_loop sliceBuf tag bytes ⟨count⟩

theorem enter_recursion_value (count child : U32) (hc : count.val = child.val + 1) :
    encoding.DecodeContext.enter_recursion ⟨count⟩ = .ok ⟨child⟩ := by
  unfold encoding.DecodeContext.enter_recursion
  have hs : (count - 1#u32 : Result U32) = .ok child := by
    obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists
      (UScalar.sub_spec (x := count) (y := 1#u32) (by scalar_tac))
    have he : z = child := by apply UScalar.eq_of_val_eq; scalar_tac
    simpa only [he] using hz
  simp [hs]

/-- Every finite grammar derivation agrees with the unchanged translated Rust skip.
This is a refinement theorem, not a totality theorem or a whole Signal parser proof. -/
theorem skip_semantics_reference {mode tag count before result}
    (derivation : SkipSemantics mode tag count before result) :
    runSkipMode mode tag count before = .ok result := by
  induction derivation with
  | limit kind tag bytes => exact recursion_limit_first sliceBuf kind tag bytes
  | endField hc => exact unexpected_end_group sliceBuf _ _ _ hc
  | fixed32 hc => exact fixed32_reference _ _ _ hc
  | fixed64 hc => exact fixed64_reference _ _ _ hc
  | varint hc hd => exact skip_varint_after _ _ _ _ _ hc hd
  | varintError hc hd => exact skip_varint_error _ _ _ _ _ hc hd
  | length hc hd => exact length_delimited_after _ _ _ _ _ hc hd
  | lengthError hc hd => exact length_delimited_error _ _ _ _ _ hc hd
  | start hc _ ih => exact (start_group _ _ _ hc).trans ih
  | keyError hd => exact group_loop_done _ _ _ _ (group_key_error _ _ _ _ _ hd)
  | close hd => exact group_loop_done _ _ _ _ (group_end_after _ _ _ _ _ hd)
  | childError hk hd hc _ ih =>
    exact group_loop_done _ _ _ _
      (group_child_after _ _ _ _ _ _ _ _ _ hk hd (enter_recursion_value _ _ hc) ih)
  | childNext hk hd hc _ _ ihChild ihRest =>
    exact (group_loop_cont _ _ _ _
      (group_child_after _ _ _ _ _ _ _ _ _ hk hd (enter_recursion_value _ _ hc) ihChild)).trans ihRest

end LibSignalReference.Candidate.ProstSkip
