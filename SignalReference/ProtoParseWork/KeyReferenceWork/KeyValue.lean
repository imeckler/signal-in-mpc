import ProtoParseWork.KeyReferenceWork.Generated.key_step.Funs

namespace LibSignalReference.Candidate.ProstKey
open Aeneas Aeneas.Std ProstKeyCandidate
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

abbrev WireType := encoding.wire_type.WireType

def makeError (kind : error.DecodeErrorKind) : error.DecodeError :=
  ⟨⟨kind,alloc.vec.Vec.new (Str × Str)⟩⟩

def wireResult (value : U64) : core.result.Result WireType error.DecodeError :=
  match value.val with
  | 0 => .Ok .Varint
  | 1 => .Ok .SixtyFourBit
  | 2 => .Ok .LengthDelimited
  | 3 => .Ok .StartGroup
  | 4 => .Ok .EndGroup
  | 5 => .Ok .ThirtyTwoBit
  | _ => .Err (makeError (.InvalidWireType value))

def wireNumber : WireType → Nat
  | .Varint => 0
  | .SixtyFourBit => 1
  | .LengthDelimited => 2
  | .StartGroup => 3
  | .EndGroup => 4
  | .ThirtyTwoBit => 5

theorem wire_reference (value : U64) :
    encoding.wire_type.WireType.Insts.CoreConvertTryFromU64DecodeError.try_from value =
      .ok (wireResult value) := by
  unfold encoding.wire_type.WireType.Insts.CoreConvertTryFromU64DecodeError.try_from wireResult
  split <;> try rfl
  rename_i _ h0 h1 h2 h3 h4 h5
  split <;> try rfl
  all_goals
    first
    | exact False.elim (h0 (UScalar.eq_of_val_eq (by assumption)))
    | exact False.elim (h1 (UScalar.eq_of_val_eq (by assumption)))
    | exact False.elim (h2 (UScalar.eq_of_val_eq (by assumption)))
    | exact False.elim (h3 (UScalar.eq_of_val_eq (by assumption)))
    | exact False.elim (h4 (UScalar.eq_of_val_eq (by assumption)))
    | exact False.elim (h5 (UScalar.eq_of_val_eq (by assumption)))

theorem wire_ok (value : U64) (kind : WireType) :
    wireResult value = .Ok kind ↔ value.val = wireNumber kind := by
  cases kind <;> unfold wireResult wireNumber <;> split <;> simp_all

theorem wire_error (value : U64) (h : 5 < value.val) :
    wireResult value = .Err (makeError (.InvalidWireType value)) := by
  unfold wireResult
  split <;> simp_all

def kindOf (value : U64) : U64 := value &&& 7#u64

def tagOf (value : U64) : U32 := ⟨(value.bv.setWidth 32) >>> 3⟩

def keyResult (value : U64) : core.result.Result (U32 × WireType) error.DecodeError :=
  if 4294967295 < value.val then .Err (makeError (.InvalidKey value)) else
    match wireResult (kindOf value) with
    | .Err error => .Err error
    | .Ok kind => if (tagOf value).val < 1 then .Err (makeError .InvalidTag) else .Ok (tagOf value,kind)

theorem tag_shift (value : U64) :
    (UScalar.cast .U32 value >>> 3#i32) = .ok (tagOf value) := by
  rfl

theorem kind_value (value : U64) : (kindOf value).val = value.val % 8 := by
  change value.bv.toNat &&& (2^3-1) = value.val % 8
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem tag_value (value : U64) (h : value.val ≤ 4294967295) :
    (tagOf value).val = value.val / 8 := by
  change ((value.bv.setWidth 32) >>> 3).toNat = value.val / 8
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_setWidth,UScalar.bv_toNat]
  rw [Nat.mod_eq_of_lt (by omega : value.val < 2^32)]
  exact Nat.shiftRight_eq_div_pow _ _

/-- Exact unchanged key-validation continuation after successful varint decoding. -/
theorem key_after_varint {T : Type} (bufInst : bytes.buf.buf_impl.Buf T)
    (before after : T) (value : U64)
    (h : encoding.varint.decode_varint bufInst before = .ok (.Ok value,after)) :
    encoding.decode_key bufInst before = .ok (keyResult value,after) := by
  rw [encoding.decode_key,h]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,lift]
  change (if value > core.convert.num.FromU64U32.from core.num.U32.MAX then _ else _) = _
  have hm : (value > core.convert.num.FromU64U32.from core.num.U32.MAX) ↔ 4294967295 < value.val := by rfl
  simp only [hm]
  unfold keyResult
  split
  · rfl
  · rw [wire_reference]
    simp only [bind_tc_ok]
    dsimp only [kindOf]
    cases hw : wireResult (value &&& 7#u64) with
    | Err error => rfl
    | Ok kind =>
      simp only [bind_tc_ok]
      rw [tag_shift]
      simp only [bind_tc_ok]
      rw [encoding.MIN_TAG]
      have ht : (tagOf value < 1#u32) ↔ (tagOf value).val < 1 := by rfl
      simp only [ht]
      split_ifs <;> rfl

theorem key_after_varint_error {T : Type} (bufInst : bytes.buf.buf_impl.Buf T)
    (before after : T) (error : error.DecodeError)
    (h : encoding.varint.decode_varint bufInst before = .ok (.Err error,after)) :
    encoding.decode_key bufInst before = .ok (.Err error,after) := by
  rw [encoding.decode_key,h]
  rfl

#print axioms wire_reference
#print axioms wire_ok
#print axioms key_after_varint
#print axioms key_after_varint_error
end LibSignalReference.Candidate.ProstKey
