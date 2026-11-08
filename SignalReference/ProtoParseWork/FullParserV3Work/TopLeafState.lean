import ProtoParseWork.FullParserV3Work.ScanState
open TlsMpc TlsMpc.Signal
namespace FullParserV3
open LibSignalReference.Candidate.ProstSkipKey LibSignalReference.Candidate.ProstSkipPlan
open ParserErrorStateV2
set_option maxHeartbeats 2000000

theorem apply_leaf_depth (position : Nat) (p : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (state : ProtoParse.State (BitVec 8) (BitVec 64))
    (hs : state.ok = 255) (hp : p.ok = 255) (hn : state.next = BitVec.ofNat 64 position)
    (h3 : p.kind ≠ 3) (h4 : p.kind ≠ 4) :
    (ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state).depth = state.depth := by
  have hh : Word64.eq Word64.concrete ByteAuth.concrete state.next (Word64.concrete.const position) = 255 := by
    rw [hn]; exact word_eq_self _
  have hstart : Word64.eq Word64.concrete ByteAuth.concrete p.kind (Word64.concrete.const 3) = 0 := by
    rw [word_eq_value]; exact if_neg h3
  have hstop : Word64.eq Word64.concrete ByteAuth.concrete p.kind (Word64.concrete.const 4) = 0 := by
    rw [word_eq_value]; exact if_neg h4
  simp only [ProtoParse.applyPlan,hs,hp,hh,hstart,hstop,Word64.select_reject]
  exact Word64.select_accept _ _

theorem package_top_step (bytes : Aeneas.Std.Slice Aeneas.Std.U8) (position finish : Nat)
    (state : ProtoParse.State (BitVec 8) (BitVec 64)) (p : ProtoParse.Plan (BitVec 8) (BitVec 64))
    (hat : StateAt bytes position state []) (hp : p.ok = 255)
    (h3 : p.kind ≠ 3) (h4 : p.kind ≠ 4) (hs : p.stop = BitVec.ofNat 64 finish)
    (hstep : stepOf bytes state position = ProtoParse.applyPlan Word64.concrete ByteAuth.concrete position p state)
    (hpos : position < finish) (hbound : finish ≤ bytes.length) (hcap : bytes.length ≤ 512) :
    StateAt bytes finish (stepOf bytes state position) [] ∧ scanOf bytes position finish state = stepOf bytes state position := by
  have hok : (stepOf bytes state position).ok = 255 := by rw [hstep]; exact apply_success_ok _ _ _ hat.ok hp hat.cursor
  have hnext : (stepOf bytes state position).next = BitVec.ofNat 64 finish := by
    rw [hstep,apply_next position p state hat.ok hp hat.cursor,hs]
  have hdepth : (stepOf bytes state position).depth = state.depth := by rw [hstep]; exact apply_leaf_depth _ _ _ hat.ok hp hat.cursor h3 h4
  have hstack : (stepOf bytes state position).stack = state.stack := by rw [hstep]; exact apply_nonstart_stack _ _ _ h3
  have hfields : (stepOf bytes state position).fields.length = 6 := by rw [hstep,apply_fields_length,hat.fields_size]
  have hm := (apply_masks state position p (Or.inr hat.ok) (Or.inr hp) hat.fields_mask).2
  refine ⟨{ok := hok,cursor := hnext,frames := ?_,frames_before := by simp,stack_size := ?_,fields_size := hfields,fields_mask := ?_},?_⟩
  · simpa only [hdepth,hstack] using hat.frames
  · rw [hstack]; exact hat.stack_size
  · simpa only [hstep] using hm
  · exact scan_step_interval bytes.length position finish (rowsOf bytes) state _ rfl hnext hpos hbound hcap

#print axioms package_top_step
end FullParserV3
