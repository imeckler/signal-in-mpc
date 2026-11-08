import ProtoParseWork.FullParserV3Work.ObservedProofs
import ProtoParseWork.FullParserV3Work.KnownTotality
open Aeneas Aeneas.Std Result TlsMpc TlsMpc.Signal
namespace FullParserV3.Observed
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def wireNumber : ProstBytesCandidate.encoding.wire_type.WireType → Nat
  | .Varint => 0
  | .SixtyFourBit => 1
  | .LengthDelimited => 2
  | .StartGroup => 3
  | .EndGroup => 4
  | .ThirtyTwoBit => 5

/-- No constructor or payload is discarded for errors reachable by the bounded
Signal parser. Diagnostic stack text is the only erased error component. -/
def errorView : ProstBytesCandidate.error.DecodeErrorKind → Option (ErrorMeta (BitVec 64))
  | .InvalidVarint => some ⟨1,0⟩
  | .InvalidKey value => some ⟨2,value.bv⟩
  | .InvalidWireType value => some ⟨3,value.bv⟩
  | .InvalidTag => some ⟨4,0⟩
  | .UnexpectedWireType actual expected => some ⟨5,BitVec.ofNat 64 (wireNumber actual+8*wireNumber expected)⟩
  | .BufferUnderflow => some ⟨6,0⟩
  | .RecursionLimitReached => some ⟨7,0⟩
  | .UnexpectedEndGroupTag => some ⟨8,0⟩
  | _ => none

def statusView (status : Aeneas.Std.core.result.Result Unit prost.error.DecodeError) : Option (ErrorMeta (BitVec 64)) :=
  match status with | .Ok () => some ⟨0,0⟩ | .Err error => errorView error.inner.description

theorem diagnostics_only (error : prost.error.DecodeError) (stack : alloc.vec.Vec (Str × Str)) :
    statusView (.Err ⟨{error.inner with stack := stack}⟩) = statusView (.Err error) := rfl

theorem wire_number_injective {left right : ProstBytesCandidate.encoding.wire_type.WireType}
    (h : wireNumber left = wireNumber right) : left = right := by
  cases left <;> cases right <;> simp_all [wireNumber]

theorem wire_pair_injective {a b c d : ProstBytesCandidate.encoding.wire_type.WireType}
    (h : BitVec.ofNat 64 (wireNumber a+8*wireNumber b) = BitVec.ofNat 64 (wireNumber c+8*wireNumber d)) :
    a = c ∧ b = d := by
  have ha : wireNumber a < 8 := by cases a <;> decide
  have hb : wireNumber b < 8 := by cases b <;> decide
  have hc : wireNumber c < 8 := by cases c <;> decide
  have hd : wireNumber d < 8 := by cases d <;> decide
  have hn := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : wireNumber a+8*wireNumber b < 2^64),
    Nat.mod_eq_of_lt (by omega : wireNumber c+8*wireNumber d < 2^64)] at hn
  exact ⟨wire_number_injective (by omega),wire_number_injective (by omega)⟩

/-- Every represented error constructor and payload is recoverable. -/
theorem error_view_injective {left right : ProstBytesCandidate.error.DecodeErrorKind}
    {encoded : ErrorMeta (BitVec 64)} (hl : errorView left = some encoded) (hr : errorView right = some encoded) : left = right := by
  have h : errorView left = errorView right := hl.trans hr.symm
  cases left <;> cases right
  all_goals try { cases hl }
  all_goals try { cases hr }
  all_goals try rfl
  all_goals simp only [errorView,Option.some.injEq] at h
  all_goals have hc := congrArg ErrorMeta.code h
  all_goals have hp := congrArg ErrorMeta.parameter h
  all_goals dsimp only at hc hp
  all_goals first
    | (exfalso; revert hc; decide)
    | (rename_i a b; congr 1; apply UScalar.eq_of_val_eq; exact congrArg BitVec.toNat hp)
    | (obtain ⟨rfl,rfl⟩ := wire_pair_injective hp; rfl)

theorem key_varint_error (key payload : ProtoParse.Decoded (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (hk : key.ok = 0) :
    classify Word64.concrete ByteAuth.concrete key payload state = ⟨1,0⟩ := by
  dsimp only [classify]
  rw [hk]
  simp only [Word64.select_reject]
  rfl

#print axioms error_view_injective
#print axioms diagnostics_only
#print axioms key_varint_error
end FullParserV3.Observed
