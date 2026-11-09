import ChatResponseReferenceWork.StreamingV1.VarintReference
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
open Std.Tactic.BVDecide
namespace ChatResponseReference.StreamingV1

def enumWord (value : I32) : BitVec 64 := value.bv.setWidth 64
def statusWord (value : U32) : BitVec 64 := value.bv.setWidth 64

private theorem low32_bits (bits : BitVec 64) :
    (bits.setWidth 32).setWidth 64 = bits &&& 4294967295 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth,BitVec.toNat_and,BitVec.toNat_ofNat]
  change (bits.toNat % 2^32) % 2^64 = bits.toNat &&& (2^32-1)
  rw [Nat.and_two_pow_sub_one_eq_mod]
  apply Nat.mod_eq_of_lt
  have bound := Nat.mod_lt bits.toNat (show 0 < 2^32 by decide)
  omega

theorem enum_cast_projection (value : U64) :
    enumWord (UScalar.hcast .I32 value) = value.bv &&& 4294967295 := by
  unfold enumWord I32.bv
  rw [UScalar.hcast_bv_eq]
  exact low32_bits _

theorem status_cast_projection (value : U64) :
    statusWord (UScalar.cast .U32 value) = value.bv &&& 4294967295 := by
  unfold statusWord U32.bv
  rw [UScalar.cast_bv_eq]
  exact low32_bits _

/-- Signed enum interpretation does not accidentally sign-extend into the Core
word. The native response enum comparison is preserved exactly. -/
theorem enum_two_exact (value : I32) : enumWord value = 2 ↔ value = 2#i32 := by
  rcases value with ⟨bits⟩
  change BitVec 32 at bits
  change bits.setWidth 64 = (2 : BitVec 64) ↔ (⟨bits⟩ : I32) = ⟨(2 : BitVec 32)⟩
  simp only [IScalar.mk.injEq]
  constructor
  · intro same
    have numeric := congrArg BitVec.toNat same
    simp only [BitVec.toNat_setWidth] at numeric
    change bits.toNat % 2^64 = 2 at numeric
    have bound : bits.toNat < 2^64 := by have small := bits.isLt; omega
    rw [Nat.mod_eq_of_lt bound] at numeric
    apply BitVec.eq_of_toNat_eq
    exact numeric
  · intro same
    subst bits
    rfl

def scalarObservation {T B E : Type} (word : T → BitVec 64)
    (result : core.result.Result Unit E × T × B) :=
  (result.1,word result.2.1,result.2.2)

theorem actual_enum_projection (old : I32) (before after : Slice U8)
    (ctx : ActualOuterEnvelopeV1.prost.encoding.DecodeContext)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError)
    (run : LoopSupportSkip.encoding.varint.decode_varint LibSignalReference.Candidate.ProstSkipBuf.sliceBuf before = .ok (decoded,after)) :
    (do let result ← ActualOuterEnvelopeV1.prost.encoding.int32.merge OuterEnvelopeV1.sliceBuf .Varint old before ctx
        .ok (scalarObservation enumWord result)) =
      .ok (match decoded with
        | .Ok value => (.Ok (),value.bv &&& 4294967295,after)
        | .Err error => (.Err (ActualResponseBytesV1.fromSkipError error),enumWord old,after)) := by
  rw [OuterEnvelopeV1.int32_from_decode old before after ctx decoded run]
  cases decoded with
  | Err error => rfl
  | Ok value => simp [OuterEnvelopeV1.scalarResult,scalarObservation,enum_cast_projection]

theorem actual_status_projection (old : U32) (before after : Slice U8)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext)
    (decoded : core.result.Result U64 LoopSupportSkip.error.DecodeError)
    (run : LoopSupportSkip.encoding.varint.decode_varint LibSignalReference.Candidate.ProstSkipBuf.sliceBuf before = .ok (decoded,after)) :
    (do let result ← ActualInnerResponseV1.prost.encoding.uint32.merge InnerResponseV1.sliceBuf .Varint old before ctx
        .ok (scalarObservation statusWord result)) =
      .ok (match decoded with
        | .Ok value => (.Ok (),value.bv &&& 4294967295,after)
        | .Err error => (.Err (ActualResponseBytesV1.fromSkipError error),statusWord old,after)) := by
  rw [InnerResponseV1.uint32_from_decode old before after ctx decoded run]
  cases decoded with
  | Err error => rfl
  | Ok value => simp [InnerResponseV1.scalarResult32,scalarObservation,status_cast_projection]
#print axioms enum_cast_projection
#print axioms status_cast_projection
#print axioms enum_two_exact
#print axioms actual_enum_projection
#print axioms actual_status_projection
end ChatResponseReference.StreamingV1
