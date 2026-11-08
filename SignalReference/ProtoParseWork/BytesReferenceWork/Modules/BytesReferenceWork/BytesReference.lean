import BytesReferenceWork.Replayed.Consumption
import BytesReferenceWork.CopyModel

namespace LibSignalReference.Candidate.ProstBytes
open Aeneas Aeneas.Std ProstBytesCandidate
open LibSignalReference.Candidate.ProstBytesBuf
set_option maxHeartbeats 500000
deriving instance DecidableEq for encoding.wire_type.WireType

def decodeError (kind : error.DecodeErrorKind) : error.DecodeError :=
  ⟨⟨kind,alloc.vec.Vec.new (Str × Str)⟩⟩

theorem check_wire_reference (expected actual : encoding.wire_type.WireType) :
    encoding.wire_type.check_wire_type expected actual =
      .ok (if actual = expected then .Ok ()
        else .Err (decodeError (.UnexpectedWireType actual expected))) := by
  cases expected <;> cases actual <;> rfl

theorem bytes_wire_error {T B : Type} (adapter : encoding.BytesAdapter T)
    (bufInst : bytes.buf.buf_impl.Buf B) (kind : encoding.wire_type.WireType)
    (old : T) (buf : B) (ctx : encoding.DecodeContext) (hk : kind ≠ .LengthDelimited) :
    encoding.bytes.merge adapter bufInst kind old buf ctx =
      .ok (.Err (decodeError (.UnexpectedWireType kind .LengthDelimited)),old,buf) := by
  simp [encoding.bytes.merge,check_wire_reference,hk,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

theorem bytes_decode_error {T : Type} (adapter : encoding.BytesAdapter T)
    (before after : Slice U8) (old : T) (error : error.DecodeError) (ctx : encoding.DecodeContext)
    (hd : encoding.varint.decode_varint sliceBuf before = .ok (.Err error,after)) :
    encoding.bytes.merge adapter sliceBuf .LengthDelimited old before ctx = .ok (.Err error,old,after) := by
  simp [encoding.bytes.merge,check_wire_reference,hd,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

private theorem remaining_u64 (view : Slice U8) :
    (UScalar.cast .U64 view.len).val = view.length := by
  rw [UScalar.cast_val_mod_pow_greater_numBits_eq .U64 view.len (by
    simp only [UScalarTy.Usize_numBits_eq,UScalarTy.U64_numBits_eq]
    cases System.Platform.numBits_eq <;> omega)]
  exact Slice.len_val view

theorem bytes_underflow {T : Type} (adapter : encoding.BytesAdapter T)
    (before after : Slice U8) (old : T) (value : U64) (ctx : encoding.DecodeContext)
    (hd : encoding.varint.decode_varint sliceBuf before = .ok (.Ok value,after))
    (hn : after.length < value.val) :
    encoding.bytes.merge adapter sliceBuf .LengthDelimited old before ctx =
      .ok (.Err (decodeError .BufferUnderflow),old,after) := by
  simp only [encoding.bytes.merge,check_wire_reference,if_true,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch,hd,uncurry_apply_pair,remaining_spec,lift]
  have hl := remaining_u64 after
  have hc : value > UScalar.cast .U64 after.len := by scalar_tac
  rw [if_pos hc]
  rfl

/-- Exact bounded copy and replacement call. The actual adapter replacement is
an explicit premise, not silently assumed to be a particular Vec model. -/
theorem bytes_after_replace {T : Type} (adapter : encoding.BytesAdapter T)
    (before after : Slice U8) (old next : T) (value : U64) (ctx : encoding.DecodeContext)
    (hd : encoding.varint.decode_varint sliceBuf before = .ok (.Ok value,after))
    (hn : value.val ≤ after.length)
    (hr : adapter.sealedBytesAdapterInst.replace_with bytes.bytes.Bytes.Insts.BytesBufBuf_implBuf
      old ⟨ContentModel.take after value.val⟩ = .ok next) :
    encoding.bytes.merge adapter sliceBuf .LengthDelimited old before ctx =
      .ok (.Ok (),next,drop after value.val) := by
  simp only [encoding.bytes.merge,check_wire_reference,if_true,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch,hd,uncurry_apply_pair,remaining_spec,lift]
  have hl := remaining_u64 after
  have hc : ¬value > UScalar.cast .U64 after.len := by scalar_tac
  rw [if_neg hc]
  have hbound := after.len.hBounds
  rw [Slice.len_val] at hbound
  have hv : (UScalar.cast .Usize value).val = value.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq .Usize value (by omega)
  rw [copy_slice_spec after (UScalar.cast .Usize value) (by rw [hv]; exact hn)]
  simp only [bind_tc_ok,hv,uncurry_apply_pair,hr]

#print axioms check_wire_reference
#print axioms bytes_wire_error
#print axioms bytes_decode_error
#print axioms bytes_underflow
#print axioms bytes_after_replace
end LibSignalReference.Candidate.ProstBytes
