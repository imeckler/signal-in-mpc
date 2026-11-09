import ChatResponseReferenceWork.StreamingV1.WireGuard
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
local instance : DecidableEq WireType := fun x y => by
  cases x <;> cases y <;> first | exact .isTrue rfl | exact .isFalse (by intro same; cases same)

/-- Every source scalar field rejects every non-varint wire kind in the actual
Core key guard, at both outer enum and inner ID/status dispatch sites. -/
theorem scalar_wrong_wire_mask (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (inside : Bool) (number : Nat) (wire : WireType)
    (known : if inside then number = 1 ∨ number = 2 else number = 1) (wrong : wire ≠ .Varint)
    (depth : state.depth = 0) (inner : state.inner = if inside then 255 else 0)
    (tag : Word64.concrete.shift (coreDecoded state byte) 3 = Word64.concrete.const number)
    (kind : Word64.concrete.band (coreDecoded state byte) 7 = Word64.concrete.const (wireNumber wire)) :
    schemaWireMask state byte = 0 := by
  unfold schemaWireMask scalarKeyMask bytesKeyMask
  rw [depth,inner,tag,kind]
  cases inside with
  | false =>
    change number = 1 at known
    subst number
    cases wire <;> first | contradiction | rfl
  | true =>
    change number = 1 ∨ number = 2 at known
    rcases known with h|h <;> subst number <;> cases wire <;> first | contradiction | rfl

/-- Every source response byte/string/header or outer submessage field rejects
all non-length-delimited wire kinds in the actual Core key guard. -/
theorem bytes_wrong_wire_mask (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (inside : Bool) (number : Nat) (wire : WireType)
    (known : if inside then number = 3 ∨ number = 4 ∨ number = 5 else number = 2 ∨ number = 3)
    (wrong : wire ≠ .LengthDelimited)
    (depth : state.depth = 0) (inner : state.inner = if inside then 255 else 0)
    (tag : Word64.concrete.shift (coreDecoded state byte) 3 = Word64.concrete.const number)
    (kind : Word64.concrete.band (coreDecoded state byte) 7 = Word64.concrete.const (wireNumber wire)) :
    schemaWireMask state byte = 0 := by
  unfold schemaWireMask scalarKeyMask bytesKeyMask
  rw [depth,inner,tag,kind]
  cases inside with
  | false =>
    change number = 2 ∨ number = 3 at known
    rcases known with h|h <;> subst number <;> cases wire <;> first | contradiction | rfl
  | true =>
    change number = 3 ∨ number = 4 ∨ number = 5 at known
    rcases known with h|h|h <;> subst number <;> cases wire <;> first | contradiction | rfl

/-- Exact accepted/rejected guard for all six wire kinds at source scalar sites. -/
theorem scalar_wire_mask (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (inside : Bool) (number : Nat) (wire : WireType)
    (known : if inside then number = 1 ∨ number = 2 else number = 1)
    (depth : state.depth = 0) (inner : state.inner = if inside then 255 else 0)
    (tag : Word64.concrete.shift (coreDecoded state byte) 3 = Word64.concrete.const number)
    (kind : Word64.concrete.band (coreDecoded state byte) 7 = Word64.concrete.const (wireNumber wire)) :
    schemaWireMask state byte = if wire = .Varint then 255 else 0 := by
  by_cases wrong : wire ≠ .Varint
  · rw [if_neg wrong]
    exact scalar_wrong_wire_mask state byte inside number wire known wrong depth inner tag kind
  · have same : wire = .Varint := by simpa only [ne_eq,not_not] using wrong
    subst wire
    unfold schemaWireMask scalarKeyMask bytesKeyMask
    rw [depth,inner,tag,kind]
    cases inside with
    | false => change number = 1 at known; subst number; rfl
    | true =>
      change number = 1 ∨ number = 2 at known
      rcases known with h|h <;> subst number <;> rfl

theorem bytes_wire_mask (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (inside : Bool) (number : Nat) (wire : WireType)
    (known : if inside then number = 3 ∨ number = 4 ∨ number = 5 else number = 2 ∨ number = 3)
    (depth : state.depth = 0) (inner : state.inner = if inside then 255 else 0)
    (tag : Word64.concrete.shift (coreDecoded state byte) 3 = Word64.concrete.const number)
    (kind : Word64.concrete.band (coreDecoded state byte) 7 = Word64.concrete.const (wireNumber wire)) :
    schemaWireMask state byte = if wire = .LengthDelimited then 255 else 0 := by
  by_cases wrong : wire ≠ .LengthDelimited
  · rw [if_neg wrong]
    exact bytes_wrong_wire_mask state byte inside number wire known wrong depth inner tag kind
  · have same : wire = .LengthDelimited := by simpa only [ne_eq,not_not] using wrong
    subst wire
    unfold schemaWireMask scalarKeyMask bytesKeyMask
    rw [depth,inner,tag,kind]
    cases inside with
    | false =>
      change number = 2 ∨ number = 3 at known
      rcases known with h|h <;> subst number <;> rfl
    | true =>
      change number = 3 ∨ number = 4 ∨ number = 5 at known
      rcases known with h|h|h <;> subst number <;> rfl

/-- Nested unknown groups never reinterpret their fields as response fields. -/
theorem nested_schema_unknown (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte : BitVec 8) (depth : state.depth ≠ 0) :
    scalarKeyMask state byte = 0 ∧ bytesKeyMask state byte = 0 ∧ schemaWireMask state byte = 255 := by
  have top : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0 = 0 := by
    unfold TlsChatResponse.weq
    rw [word_eq_value]
    exact if_neg depth
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  have scalar : scalarKeyMask state byte = 0 := by unfold scalarKeyMask; rw [top,zeroAnd]
  have bytes : bytesKeyMask state byte = 0 := by unfold bytesKeyMask; rw [top,zeroAnd]
  refine ⟨scalar,bytes,?_⟩
  unfold schemaWireMask
  rw [scalar,bytes,zeroAnd,zeroAnd]
  rfl

#print axioms scalar_wrong_wire_mask
#print axioms bytes_wrong_wire_mask
#print axioms scalar_wire_mask
#print axioms bytes_wire_mask
#print axioms nested_schema_unknown
end ChatResponseReference.StreamingV1
