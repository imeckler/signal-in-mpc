import ChatResponseReferenceWork.StreamingUnknownV1.GroupKeyGuard
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey

/-- At depth 99 inside a response, the real source child recursion budget is
zero. Every further non-end key fails the Core depth guard; a matching EndGroup
is governed separately and remains allowed to close at this depth. -/
theorem inner_group_limit_key_guard (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (native : U64) (tag : U32) (wire : WireType)
    (depth : state.depth = BitVec.ofNat 64 99) (inner : state.inner = 255)
    (notEnd : wire ≠ .EndGroup)
    (decoded : coreDecoded state byte = native.bv) (accepted : keyResult native = .Ok (tag,wire)) :
    actualKeyGood state byte = 0 := by
  have nativeKind : Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7) = Word64.concrete.const (wireNumber wire) := by
    rw [decoded]; exact native_key_kind native tag wire accepted
  have notGroup : TlsChatResponse.weq Word64.concrete ByteAuth.concrete
      (Word64.concrete.band (coreDecoded state byte) (Word64.concrete.const 7)) 4 = 0 := by
    rw [nativeKind]
    cases wire <;> first | contradiction | rfl
  have limit : Word64.concrete.ule state.depth (Word64.concrete.select state.inner 98 99) = 0 := by rw [depth,inner]; rfl
  have andZero (x : BitVec 8) : ByteAuth.concrete.and x 0 = 0 := BitVec.and_zero
  dsimp only [actualKeyGood]
  rw [notGroup,TlsInner.select_reject,limit]
  simp only [andZero]

/-- Exact arithmetic correspondence used by actual group child context descent;
no wraparound or blanket lifetime/primitive assumption is involved. -/
theorem inner_group_child_budget (depth : Nat) (bound : depth ≤ 98) :
    99-depth = (98-depth)+1 := by omega

#print axioms inner_group_limit_key_guard
#print axioms inner_group_child_budget
end ChatResponseReference.StreamingUnknownV1
