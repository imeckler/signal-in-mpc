import ProtoParseWork.FullParserV3Work.Numeric.Group
open TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipKey LibSignalReference.Candidate.ProstSkipPlan
open ParserErrorStateV2
set_option maxHeartbeats 2000000

theorem apply_nested_leaf (position : Nat) (p : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hs : state.ok = 255) (hp : p.ok = 255) (hn : state.next = BitVec.ofNat 64 position)
    (hd : state.depth ≠ 0) (h3 : p.kind ≠ 3) (h4 : p.kind ≠ 4) :
    let result := ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state
    result.ok = 255 ∧ result.next = p.stop ∧ result.depth = state.depth ∧ result.fields = state.fields := by
  have hh : Word64.eq Word64.concrete ByteAuth.concrete state.next (Word64.concrete.const position) = 255 := by
    rw [hn]; exact word_eq_self _
  have hstart : Word64.eq Word64.concrete ByteAuth.concrete p.kind (Word64.concrete.const 3) = 0 := by
    rw [word_eq_value]; exact if_neg h3
  have hstop : Word64.eq Word64.concrete ByteAuth.concrete p.kind (Word64.concrete.const 4) = 0 := by
    rw [word_eq_value]; exact if_neg h4
  refine ⟨?_,apply_next position p state hs hp hn,?_,nested_fields_unchanged position p state hd⟩
  · simp only [ProtoParse.applyPlan,hs,hp,hh]
    rfl
  · simp only [ProtoParse.applyPlan,hs,hp,hh,hstart,hstop,Word64.select_reject]
    exact Word64.select_accept _ _

#print axioms apply_nested_leaf
end FullParserV3
