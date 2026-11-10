import ChatResponseReferenceWork.StreamingUnknownV1.GroupErrorEvents
import ChatResponseReferenceWork.StreamingUnknownV1.GroupDepthStep
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- At actual non-top depth, no key may install schema field kinds. This
holds even for malformed keys, invalid states and schema-looking inner tags. -/
theorem active_group_kinds_step (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (active : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0 = 0)
    (kinds : state.kinds = [0,0,0,0]) :
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state.kinds = [0,0,0,0] := by
  have zeroAnd (x : BitVec 8) : ByteAuth.concrete.and 0 x = 0 := BitVec.zero_and
  change TlsWebSocketUpgrade.choose ByteAuth.concrete _
    [ByteAuth.concrete.and (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0) _,
     ByteAuth.concrete.and (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0) _,
     ByteAuth.concrete.and (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0) _,
     ByteAuth.concrete.and (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0) _] state.kinds = _
  rw [active,kinds]
  simp only [zeroAnd]
  simp [TlsWebSocketUpgrade.choose,List.zipWith,TlsInner.select,ByteAuth.concrete]


/-- Explicit numeric trajectory boundary for silent group bytes. It permits
arbitrary rejected tails, but every live proper-beforeBytes state must still be
inside a group. Source-to-trajectory grounding remains a separate theorem. -/
def GroupSilentTrajectory (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (bytes : List (BitVec 8)) : Prop :=
  ∀ beforeBytes suffix, bytes = beforeBytes++suffix → suffix ≠ [] →
    TlsChatResponse.weq Word64.concrete ByteAuth.concrete (feed state beforeBytes).depth 0 = 0 ∨ (feed state beforeBytes).valid = 0

theorem active_group_trace_zero (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (bytes : List (BitVec 8)) (initial : state.kinds = [0,0,0,0] ∨ state.valid = 0)
    (trajectory : GroupSilentTrajectory state bytes) :
    bodyTrace state bytes = bytes.map (fun byte => (0,0,0,byte)) := by
  induction bytes generalizing state with
  | nil => rfl
  | cons byte rest ih =>
    let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state
    have atStart : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.depth 0 = 0 ∨ state.valid = 0 :=
      trajectory [] (byte::rest) rfl (by simp)
    have events :
        (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).bodyData = 0 ∧
        (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).bodyReset = 0 ∧
        (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).headerData = 0 := by
      rcases initial with kinds|invalid
      · exact zero_kinds_events_zero state byte kinds
      · exact rejected_events_zero state byte invalid
    have nextInitial : next.kinds = [0,0,0,0] ∨ next.valid = 0 := by
      rcases atStart with active|invalid
      · rcases initial with kinds|invalid
        · exact .inl (active_group_kinds_step state byte active kinds)
        · exact .inr (step_invalid_sticky state byte invalid)
      · exact .inr (step_invalid_sticky state byte invalid)
    have nextTrajectory : GroupSilentTrajectory next rest := by
      intro beforeBytes suffix span nonempty
      have current := trajectory (byte::beforeBytes) suffix (by simp only [List.cons_append,span]) nonempty
      simpa only [feed,List.foldl_cons] using current
    change (_,_,_,byte)::bodyTrace next rest = (0,0,0,byte)::rest.map _
    rw [events.1,events.2.1,events.2.2,ih next nextInitial nextTrajectory]

#print axioms active_group_kinds_step
#print axioms active_group_trace_zero
end ChatResponseReference.StreamingUnknownV1
