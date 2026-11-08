import ProtoParseWork.FullParserV3Work.KeyRejectionStep
open TlsMpc TlsMpc.Signal
namespace FullParserV3
open ParserErrorStateV2 LibSignalReference.Candidate.ProstSkipPlan
set_option maxHeartbeats 2000000

/-- Full internal rejected state for any valid/invalid plan. Active failures
retain their actual cursor, recursion frames and all existing field values;
only a top-level selected Option is initialized before decoding. -/
theorem apply_reject_any (position : Nat) (p : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hs : state.ok = 255) (hn : state.next = BitVec.ofNat 64 position) (hp : p.ok = 0) :
    let result := ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state
    result.ok = 0 ∧ result.next = p.stop ∧ result.depth = state.depth ∧ result.stack = state.stack ∧
      result.fields = if state.depth = 0 then ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 p.tag state.fields else state.fields := by
  have hf : (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state).fields =
      if state.depth = 0 then ProtoParse.initializeFields Word64.concrete ByteAuth.concrete 255 p.tag state.fields else state.fields := by
    by_cases hd : state.depth = 0
    · rw [if_pos hd]
      exact (apply_reject state position p hs hn hd hp).2.2
    · rw [if_neg hd]
      exact nested_fields_unchanged position p state hd
  have hh : Word64.eq Word64.concrete ByteAuth.concrete state.next (Word64.concrete.const position) = 255 := by
    rw [hn]; exact word_eq_self _
  have hz (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  refine ⟨?_,?_,?_,?_,hf⟩
  all_goals simp only [ProtoParse.applyPlan,hs,hh,hp,show ByteAuth.concrete.and 255 255 = 255 from rfl,
    show ByteAuth.concrete.and 255 0 = 0 from rfl,hz]
  · rfl
  · exact Word64.select_accept _ _
  · exact Word64.select_reject _ _
  · exact ParserErrorStateV2.stack_zero state.depth p.tag state.stack

namespace Observed

theorem finish_failed (state : State (BitVec 8) (BitVec 64)) (hs : state.parser.ok = 0) :
    finish Word64.concrete ByteAuth.concrete state = state := by
  have hz (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  simp only [finish,hs,hz,Word64.select_reject]

#print axioms finish_failed
end Observed
#print axioms apply_reject_any
end FullParserV3
