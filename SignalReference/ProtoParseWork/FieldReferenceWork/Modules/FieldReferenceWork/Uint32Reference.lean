import FieldReferenceWork.Replayed.Consumption

namespace LibSignalReference.Candidate.ProstField
open Aeneas Aeneas.Std ProstFieldCandidate
open LibSignalReference.Candidate.ProstFieldBuf
set_option maxHeartbeats 400000
deriving instance DecidableEq for encoding.wire_type.WireType

def decodeError (kind : error.DecodeErrorKind) : error.DecodeError :=
  ⟨⟨kind,alloc.vec.Vec.new (Str × Str)⟩⟩

theorem check_wire_reference (expected actual : encoding.wire_type.WireType) :
    encoding.wire_type.check_wire_type expected actual =
      .ok (if actual = expected then .Ok ()
        else .Err (decodeError (.UnexpectedWireType actual expected))) := by
  cases expected <;> cases actual <;> rfl

theorem uint32_wire_error {T : Type} (bufInst : bytes.buf.buf_impl.Buf T)
    (kind : encoding.wire_type.WireType) (old : U32) (buf : T) (ctx : encoding.DecodeContext)
    (hkind : kind ≠ .Varint) :
    encoding.uint32.merge bufInst kind old buf ctx =
      .ok (.Err (decodeError (.UnexpectedWireType kind .Varint)),old,buf) := by
  simp [encoding.uint32.merge,check_wire_reference,hkind,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

theorem uint32_after (before after : Slice U8) (old : U32) (value : U64)
    (ctx : encoding.DecodeContext)
    (hdecode : encoding.varint.decode_varint sliceBuf before = .ok (.Ok value,after)) :
    encoding.uint32.merge sliceBuf .Varint old before ctx =
      .ok (.Ok (),UScalar.cast .U32 value,after) := by
  simp [encoding.uint32.merge,check_wire_reference,hdecode,
    core.result.Result.Insts.CoreOpsTry.branch,lift]

theorem uint32_error (before after : Slice U8) (old : U32) (error : error.DecodeError)
    (ctx : encoding.DecodeContext)
    (hdecode : encoding.varint.decode_varint sliceBuf before = .ok (.Err error,after)) :
    encoding.uint32.merge sliceBuf .Varint old before ctx = .ok (.Err error,old,after) := by
  simp [encoding.uint32.merge,check_wire_reference,hdecode,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

/-- Prost intentionally truncates successfully decoded uint64 values to uint32. -/
theorem uint32_truncates (value : U64) :
    (UScalar.cast .U32 value).val = value.val % 2^32 := by
  simp only [UScalar.cast_val_eq,UScalarTy.U32_numBits_eq]

/-- A later successful duplicate replaces the prior scalar, even if the earlier
value or the caller's initial value differs. -/
theorem uint32_last_value (before middle after : Slice U8) (old : U32) (first last : U64)
    (ctx : encoding.DecodeContext)
    (hfirst : encoding.varint.decode_varint sliceBuf before = .ok (.Ok first,middle))
    (hlast : encoding.varint.decode_varint sliceBuf middle = .ok (.Ok last,after)) :
    (do
      let (_,next,rest) ← encoding.uint32.merge sliceBuf .Varint old before ctx
      encoding.uint32.merge sliceBuf .Varint next rest ctx) =
      .ok (.Ok (),UScalar.cast .U32 last,after) := by
  rw [uint32_after _ _ _ _ _ hfirst]
  simp only [bind_tc_ok]
  exact uint32_after _ _ _ _ _ hlast


def scalarResult (old : U32) (decoded : core.result.Result U64 error.DecodeError)
    (after : Slice U8) : core.result.Result Unit error.DecodeError × U32 × Slice U8 :=
  match decoded with
  | .Ok value => (.Ok (),UScalar.cast .U32 value,after)
  | .Err error => (.Err error,old,after)

theorem uint32_from_decode (before after : Slice U8) (old : U32)
    (decoded : core.result.Result U64 error.DecodeError) (ctx : encoding.DecodeContext)
    (hdecode : encoding.varint.decode_varint sliceBuf before = .ok (decoded,after)) :
    encoding.uint32.merge sliceBuf .Varint old before ctx = .ok (scalarResult old decoded after) := by
  cases decoded with
  | Ok value => exact uint32_after _ _ _ _ _ hdecode
  | Err error => exact uint32_error _ _ _ _ _ hdecode

/-- Total reference for every contiguous input slice, reusing the accepted exact
varint prefix/error-consumption characterization. No caller decoder premise. -/
theorem uint32_full_reference (bytes : Slice U8) (old : U32) (ctx : encoding.DecodeContext) :
    ∃ decoded after,
      PrefixPost bytes decoded after ∧ ErrorPost bytes decoded after ∧
      encoding.uint32.merge sliceBuf .Varint old bytes ctx = .ok (scalarResult old decoded after) := by
  obtain ⟨decoded,after,hd,hp,he⟩ := decode_full_reference bytes
  exact ⟨decoded,after,hp,he,uint32_from_decode _ _ _ _ _ hd⟩

#print axioms check_wire_reference
#print axioms uint32_wire_error
#print axioms uint32_after
#print axioms uint32_error
#print axioms uint32_truncates
#print axioms uint32_last_value
#print axioms uint32_from_decode
#print axioms uint32_full_reference
end LibSignalReference.Candidate.ProstField
