import SkipTranslatorWork.Generated.skip.Funs
import SkipTranslatorWork.Replayed.Consumption

namespace LibSignalReference.Candidate.ProstSkip
open Aeneas Aeneas.Std LoopSupportSkip
open LibSignalReference.Candidate.ProstSkipBuf
set_option maxHeartbeats 300000

def decodeError (kind : error.DecodeErrorKind) : error.DecodeError :=
  ⟨⟨kind,alloc.vec.Vec.new (Str × Str)⟩⟩

theorem recursion_limit_first {T : Type} (inst : bytes.buf.buf_impl.Buf T)
    (kind : encoding.wire_type.WireType) (tag : U32) (buf : T) :
    encoding.skip_field inst kind tag buf ⟨0#u32⟩ =
      .ok (.Err (decodeError .RecursionLimitReached),buf) := by
  rw [encoding.skip_field.eq_def]
  simp [encoding.DecodeContext.limit_reached,decodeError,
    core.convert.IntoFrom.into,error.DecodeError.Insts.CoreConvertFromDecodeErrorKind.from,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame,core.convert.FromSame.from]

theorem unexpected_end_group {T : Type} (inst : bytes.buf.buf_impl.Buf T)
    (tag : U32) (buf : T) (count : U32) (hc : count ≠ 0#u32) :
    encoding.skip_field inst .EndGroup tag buf ⟨count⟩ =
      .ok (.Err (decodeError .UnexpectedEndGroupTag),buf) := by
  rw [encoding.skip_field.eq_def]
  simp [encoding.DecodeContext.limit_reached,hc,decodeError,
    core.convert.IntoFrom.into,error.DecodeError.Insts.CoreConvertFromDecodeErrorKind.from,
    core.result.Result.Insts.CoreOpsTry.branch]


theorem skip_varint_after (before after : Slice U8) (value : U64)
    (tag count : U32) (hc : count ≠ 0#u32)
    (hdecode : encoding.varint.decode_varint sliceBuf before = .ok (.Ok value,after)) :
    encoding.skip_field sliceBuf .Varint tag before ⟨count⟩ = .ok (.Ok (),after) := by
  rw [encoding.skip_field.eq_def]
  simp only [encoding.DecodeContext.limit_reached,hc,if_false,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch,hdecode,uncurry_apply_pair,
    core.result.Result.map,
    encoding.skip_field.closure.Insts.CoreOpsFunctionFnOnceTupleU64U64,
    encoding.skip_field.closure.Insts.CoreOpsFunctionFnOnceTupleU64U64.call_once,
    remaining_spec,lift]
  have hzero : ¬(0#u64 > UScalar.cast .U64 after.len) := by scalar_tac
  simp only [if_neg hzero]
  have hz : UScalar.cast .Usize 0#u64 = 0#usize := by
    apply UScalar.eq_of_val_eq
    simp [UScalar.cast_val_eq]
  rw [hz]
  change (do let next ← sliceBuf.advance after 0#usize; .ok ((core.result.Result.Ok () : core.result.Result Unit error.DecodeError),next)) = _
  rw [advance_spec after 0#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  rfl

theorem skip_varint_error (before after : Slice U8) (error : error.DecodeError)
    (tag count : U32) (hc : count ≠ 0#u32)
    (hdecode : encoding.varint.decode_varint sliceBuf before = .ok (.Err error,after)) :
    encoding.skip_field sliceBuf .Varint tag before ⟨count⟩ = .ok (.Err error,after) := by
  rw [encoding.skip_field.eq_def]
  simp [encoding.DecodeContext.limit_reached,hc,hdecode,
    core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.map,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]


def fixedResult (bytes : Slice U8) (width : Nat) :
    core.result.Result Unit error.DecodeError × Slice U8 :=
  if bytes.length < width then (.Err (decodeError .BufferUnderflow),bytes)
  else (.Ok (),drop bytes width)

theorem fixed32_reference (bytes : Slice U8) (tag count : U32) (hc : count ≠ 0#u32) :
    encoding.skip_field sliceBuf .ThirtyTwoBit tag bytes ⟨count⟩ =
      .ok (fixedResult bytes 4) := by
  rw [encoding.skip_field.eq_def]
  simp only [encoding.DecodeContext.limit_reached,hc,if_false,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch,remaining_spec,lift]
  have hlen : (UScalar.cast .U64 bytes.len).val = bytes.length := by
    rw [UScalar.cast_val_mod_pow_greater_numBits_eq .U64 bytes.len (by
      simp only [UScalarTy.Usize_numBits_eq,UScalarTy.U64_numBits_eq]
      cases System.Platform.numBits_eq <;> omega)]
    exact Slice.len_val bytes
  have hcond : (4#u64 > UScalar.cast .U64 bytes.len) ↔ bytes.length < 4 := by
    scalar_tac
  simp only [hcond,fixedResult]
  split
  · rfl
  · rename_i h
    have hz : UScalar.cast .Usize 4#u64 = 4#usize := by
      apply UScalar.eq_of_val_eq
      cases System.Platform.numBits_eq <;> simp_all [UScalar.cast_val_eq]
    rw [hz,advance_spec bytes 4#usize (by scalar_tac)]
    rfl

theorem fixed64_reference (bytes : Slice U8) (tag count : U32) (hc : count ≠ 0#u32) :
    encoding.skip_field sliceBuf .SixtyFourBit tag bytes ⟨count⟩ =
      .ok (fixedResult bytes 8) := by
  rw [encoding.skip_field.eq_def]
  simp only [encoding.DecodeContext.limit_reached,hc,if_false,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch,remaining_spec,lift]
  have hlen : (UScalar.cast .U64 bytes.len).val = bytes.length := by
    rw [UScalar.cast_val_mod_pow_greater_numBits_eq .U64 bytes.len (by
      simp only [UScalarTy.Usize_numBits_eq,UScalarTy.U64_numBits_eq]
      cases System.Platform.numBits_eq <;> omega)]
    exact Slice.len_val bytes
  have hcond : (8#u64 > UScalar.cast .U64 bytes.len) ↔ bytes.length < 8 := by
    scalar_tac
  simp only [hcond,fixedResult]
  split
  · rfl
  · rename_i h
    have hz : UScalar.cast .Usize 8#u64 = 8#usize := by
      apply UScalar.eq_of_val_eq
      cases System.Platform.numBits_eq <;> simp_all [UScalar.cast_val_eq]
    rw [hz,advance_spec bytes 8#usize (by scalar_tac)]
    rfl


theorem length_delimited_after (before after : Slice U8) (value : U64)
    (tag count : U32) (hc : count ≠ 0#u32)
    (hdecode : encoding.varint.decode_varint sliceBuf before = .ok (.Ok value,after)) :
    encoding.skip_field sliceBuf .LengthDelimited tag before ⟨count⟩ =
      .ok (fixedResult after value.val) := by
  rw [encoding.skip_field.eq_def]
  simp only [encoding.DecodeContext.limit_reached,hc,if_false,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch,hdecode,uncurry_apply_pair,remaining_spec,lift]
  have hlen : (UScalar.cast .U64 after.len).val = after.length := by
    rw [UScalar.cast_val_mod_pow_greater_numBits_eq .U64 after.len (by
      simp only [UScalarTy.Usize_numBits_eq,UScalarTy.U64_numBits_eq]
      cases System.Platform.numBits_eq <;> omega)]
    exact Slice.len_val after
  have hcond : (value > UScalar.cast .U64 after.len) ↔ after.length < value.val := by scalar_tac
  simp only [hcond,fixedResult]
  split
  · rfl
  · rename_i h
    have hbound := after.len.hBounds
    rw [Slice.len_val] at hbound
    have hv : (UScalar.cast .Usize value).val = value.val :=
      UScalar.cast_val_mod_pow_of_inBounds_eq .Usize value (by omega)
    rw [advance_spec after (UScalar.cast .Usize value) (by rw [hv]; omega)]
    simp only [bind_tc_ok,hv]

theorem length_delimited_error (before after : Slice U8) (error : error.DecodeError)
    (tag count : U32) (hc : count ≠ 0#u32)
    (hdecode : encoding.varint.decode_varint sliceBuf before = .ok (.Err error,after)) :
    encoding.skip_field sliceBuf .LengthDelimited tag before ⟨count⟩ = .ok (.Err error,after) := by
  rw [encoding.skip_field.eq_def]
  simp [encoding.DecodeContext.limit_reached,hc,hdecode,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

end LibSignalReference.Candidate.ProstSkip
