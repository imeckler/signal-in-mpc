import ChatResponseReferenceWork.ParserCircuitCandidateV1.TrimStack
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 100000

def processTail (started : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (event : TlsChatResponse.Event (BitVec 8) (BitVec 64)) (active ending canonical : BitVec 8) :
    TlsChatResponse.Event (BitVec 8) (BitVec 64) :=
  let selected := TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete active event.state started
  let selected := {selected with valid := ByteAuth.concrete.and selected.valid canonical}
  let ended := TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete ending
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete selected) selected
  let visible := ByteAuth.concrete.and ended.valid active
  ⟨ended,ByteAuth.concrete.and visible event.bodyData,ByteAuth.concrete.and visible event.bodyReset,
    ByteAuth.concrete.and visible event.headerData⟩

theorem trim_guard (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (mask : BitVec 8) :
    trimStack {state with valid := ByteAuth.concrete.and state.valid mask} =
    {trimStack state with valid := ByteAuth.concrete.and (trimStack state).valid mask} := rfl

theorem trim_process_tail (started : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (event : TlsChatResponse.Event (BitVec 8) (BitVec 64)) (active ending canonical : BitVec 8) :
    trimEvent (processTail (trimStack started) (trimEvent event) active ending canonical) =
    trimEvent (processTail started event active ending canonical) := by
  let selected := TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete active event.state started
  let guarded := {selected with valid := ByteAuth.concrete.and selected.valid canonical}
  let ended := TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete ending
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete guarded) guarded
  have selectedEq := trim_state_select active event.state started
  have guardedEq := trim_guard selected canonical
  have endedEq := trim_state_select ending (TlsChatResponse.finish Word64.concrete ByteAuth.concrete guarded) guarded
  rw [trim_finish] at endedEq
  have validEq : (trimStack ended).valid = ended.valid := rfl
  dsimp [selected,guarded,ended] at guardedEq endedEq validEq
  change trimEvent ⟨_,_,_,_⟩ = trimEvent ⟨ended,_,_,_⟩
  simp only [trimEvent]
  simp only [←selectedEq,←guardedEq,←endedEq,validEq,trim_stack_idempotent]
  rfl

theorem trim_step_tail (started : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (byte active ending canonical : BitVec 8) (safe : SafeStack started) :
    trimEvent (processTail (trimStack started)
      (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (trimStack started) byte)
      active ending canonical) =
    trimEvent (processTail started
      (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete started byte)
      active ending canonical) := by
  rw [←trim_process_tail]
  rw [trim_stack_idempotent,trim_step started byte safe]
  exact trim_process_tail _ _ _ _ _

theorem trim_process (capacity : Nat) (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (active beginning ending byte : BitVec 8) (safe : SafeStack state) :
    trimEvent (TlsChatResponse.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      capacity (trimStack state) active beginning ending byte) =
    trimEvent (TlsChatResponse.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      capacity state active beginning ending byte) := by
  let fresh := {TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity state.expected with
    valid := ByteAuth.concrete.and state.valid (ByteAuth.concrete.not state.seen),seen := 255}
  let started := TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete
    (TlsWebSocketUpgrade.eq ByteAuth.concrete beginning 255) fresh state
  have freshNarrow : NarrowStack fresh.stack := initial_narrow_stack capacity state.expected
  have freshTrim : trimStack fresh = fresh := trim_stack_identity fresh freshNarrow
  have startedTrim := trim_state_select (TlsWebSocketUpgrade.eq ByteAuth.concrete beginning 255) fresh state
  rw [freshTrim] at startedTrim
  have startedSafe : SafeStack started := select_safe_stack _ _ _
    (canonical_byte_eq beginning 255) (.inr freshNarrow) safe
  change trimEvent (processTail _ _ _ _ _) = trimEvent (processTail started _ _ _ _)
  change trimEvent (processTail
    (TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete
      (TlsWebSocketUpgrade.eq ByteAuth.concrete beginning 255) fresh (trimStack state))
    (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      (TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete
        (TlsWebSocketUpgrade.eq ByteAuth.concrete beginning 255) fresh (trimStack state)) byte) _ _ _) = _
  rw [←startedTrim]
  exact trim_step_tail started byte _ _ _ startedSafe

/-- The original stateful endpoint, observed after each byte through the stack
projection. All control, status, cursor counters and event masks are retained. -/
def projectedTrace (capacity : Nat) (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) :
    List (BitVec 8 × BitVec 8 × BitVec 8 × BitVec 8) → List (TlsChatResponse.Event (BitVec 8) (BitVec 64))
  | [] => []
  | input::rest =>
    let event := TlsChatResponse.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      capacity state input.1 input.2.1 input.2.2.1 input.2.2.2
    trimEvent event :: projectedTrace capacity event.state rest

/-- Candidate semantic recurrence: erase the high stack half between bytes. -/
def trimmedTrace (capacity : Nat) (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) :
    List (BitVec 8 × BitVec 8 × BitVec 8 × BitVec 8) → List (TlsChatResponse.Event (BitVec 8) (BitVec 64))
  | [] => []
  | input::rest =>
    let event := trimEvent (TlsChatResponse.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      capacity state input.1 input.2.1 input.2.2.1 input.2.2.2)
    event :: trimmedTrace capacity event.state rest

theorem trimmed_trace_eq (capacity : Nat) (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (inputs : List (BitVec 8 × BitVec 8 × BitVec 8 × BitVec 8)) (reachable : ReachableStack state) :
    trimmedTrace capacity (trimStack state) inputs = projectedTrace capacity state inputs := by
  induction inputs generalizing state with
  | nil => rfl
  | cons input rest ih =>
    simp only [trimmedTrace,projectedTrace]
    rw [trim_process capacity state _ _ _ _ reachable.2]
    congr 1
    exact ih _ (process_reachable_stack capacity state _ _ _ _ reachable)

theorem fresh_trimmed_trace_eq (capacity : Nat) (expected : BitVec 64)
    (inputs : List (BitVec 8 × BitVec 8 × BitVec 8 × BitVec 8)) :
    trimmedTrace capacity (TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity expected) inputs =
    projectedTrace capacity (TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity expected) inputs := by
  have eq := trimmed_trace_eq capacity (TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity expected) inputs
    ⟨initial_control_masks capacity expected,.inr (initial_narrow_stack capacity expected)⟩
  rw [trim_stack_identity _ (initial_narrow_stack capacity expected)] at eq
  exact eq

#print axioms trimmed_trace_eq
#print axioms fresh_trimmed_trace_eq
#print axioms trim_step_tail
#print axioms trim_process
#print axioms trim_process_tail
end ChatResponseReference.ParserCircuitCandidateV1
