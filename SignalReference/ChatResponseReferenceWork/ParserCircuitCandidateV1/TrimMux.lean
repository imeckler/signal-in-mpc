import ChatResponseReferenceWork.ParserCircuitCandidateV1.TrimProcess
open TlsMpc TlsMpc.Signal
open TlsWebSocketUpgrade (get eq either any)
namespace ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 100000

def trimMuxState (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64)) :=
  {state with parser := trimStack state.parser}

def trimMuxEvent (event : TlsChatResponseMux.Event (BitVec 8) (BitVec 64)) :=
  {event with state := trimMuxState event.state}

open TlsChatResponseMux in
def muxTail (capacity : Nat) (s : State (BitVec 8) (BitVec 64)) (beginning ending : BitVec 8)
    (parsed : TlsChatResponse.Event (BitVec 8) (BitVec 64)) : Event (BitVec 8) (BitVec 64) :=
  let o := Word64.concrete
  let a := ByteAuth.concrete
  let finished := TlsChatResponse.finish o a (selfExpected parsed.state)
  let slots := s.slots.map (prepareSlot a beginning)
  let masks := slots.map (matchSlot o a parsed.state.id)
  let eligible := any a (slots.map (fun slot => a.and (eq a slot.active 255)
    (a.and (eq a slot.eligible 255) (a.not (eq a slot.consumed 255)))))
  let beginReady := either a (a.not (eq a beginning 255)) eligible
  let done := eq a ending 255
  let canonical := either a (eq a ending 0) done
  let room := TlsWebSocketUpgrade.member a s.queued [0,1,2,3]
  -- Current application policy closes the connection on a non2xx response.
  let accepted := a.and finished.valid (a.and finished.successful (a.and (exactlyOne a masks) room))
  let valid := a.and s.valid (a.and parsed.state.valid
    (a.and canonical (a.and beginReady (either a (a.not done) accepted))))
  let enqueue := a.and done valid
  let reset := validCore (TlsChatResponse.initial o a capacity (o.const 0)) valid
  let parser := validCore (TlsChatResponse.stateSelect o a done reset parsed.state) valid
  let next : State (BitVec 8) (BitVec 64) := {
    valid := valid,parser := parser,
    slots := List.zipWith (fun slot mask => consumeSlot o a done (a.and valid mask) slot) slots masks,
    queued := TlsInner.select a enqueue (TlsWebSocketControl.inc a s.queued) s.queued,
    rows := (List.range 4).map (fun i => TlsInner.select a (a.and enqueue (eq a s.queued i))
      (slotCode a masks) (get a s.rows i))}
  ⟨next,a.and valid parsed.bodyData,a.and valid parsed.bodyReset,a.and valid parsed.headerData⟩

theorem mux_process_as_tail (capacity : Nat) (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (active beginning ending byte : BitVec 8) :
    TlsChatResponseMux.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      capacity state active beginning ending byte =
    muxTail capacity state beginning ending
      (TlsChatResponse.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
        capacity state.parser active beginning 0 byte) := rfl

theorem trim_correlated_parser (capacity : Nat) (parsed : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (valid done : BitVec 8) :
    trimStack (TlsChatResponseMux.validCore
      (TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete done
        (TlsChatResponseMux.validCore (TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity (Word64.concrete.const 0)) valid) parsed) valid) =
    TlsChatResponseMux.validCore
      (TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete done
        (TlsChatResponseMux.validCore (TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity (Word64.concrete.const 0)) valid)
        (trimStack parsed)) valid := by
  have fresh : trimStack (TlsChatResponseMux.validCore
      (TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity (Word64.concrete.const 0)) valid) =
      TlsChatResponseMux.validCore (TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity (Word64.concrete.const 0)) valid :=
    trim_stack_identity _ (initial_narrow_stack capacity (Word64.concrete.const 0))
  have selected := trim_state_select done
    (TlsChatResponseMux.validCore (TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity (Word64.concrete.const 0)) valid) parsed
  rw [fresh] at selected
  change {trimStack _ with valid := valid} = _
  rw [selected]
  rfl

theorem trim_valid (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) :
    (trimStack state).valid = state.valid := rfl

theorem trim_id (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) :
    (trimStack state).id = state.id := rfl

theorem trim_self_finish_valid (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete
      (TlsChatResponseMux.selfExpected (trimStack state))).valid =
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete
      (TlsChatResponseMux.selfExpected state)).valid := rfl

theorem trim_self_finish_successful (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete
      (TlsChatResponseMux.selfExpected (trimStack state))).successful =
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete
      (TlsChatResponseMux.selfExpected state)).successful := rfl

theorem trim_mux_tail (capacity : Nat) (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (beginning ending : BitVec 8) (parsed : TlsChatResponse.Event (BitVec 8) (BitVec 64)) :
    trimMuxEvent (muxTail capacity (trimMuxState state) beginning ending (trimEvent parsed)) =
    trimMuxEvent (muxTail capacity state beginning ending parsed) := by
  simp only [muxTail,trimMuxState,trimMuxEvent,trimEvent]
  simp only [trim_valid,trim_id,trim_self_finish_valid,trim_self_finish_successful,
    trim_correlated_parser,trim_stack_idempotent]

theorem trim_mux_idempotent (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64)) :
    trimMuxState (trimMuxState state) = trimMuxState state := by
  simp only [trimMuxState,trim_stack_idempotent]

theorem trim_mux_process (capacity : Nat) (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (active beginning ending byte : BitVec 8) (safe : SafeStack state.parser) :
    trimMuxEvent (TlsChatResponseMux.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      capacity (trimMuxState state) active beginning ending byte) =
    trimMuxEvent (TlsChatResponseMux.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      capacity state active beginning ending byte) := by
  rw [mux_process_as_tail,mux_process_as_tail]
  change trimMuxEvent (muxTail capacity (trimMuxState state) beginning ending
    (TlsChatResponse.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      capacity (trimStack state.parser) active beginning 0 byte)) = _
  rw [←trim_mux_tail,trim_mux_idempotent]
  rw [trim_process capacity state.parser _ _ _ _ safe]
  exact trim_mux_tail _ _ _ _ _

theorem trim_mux_admit (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (index : BitVec 8) (id : BitVec 64) (valid : BitVec 8) :
    trimMuxState (TlsChatResponseMux.admit Word64.concrete ByteAuth.concrete (trimMuxState state) index id valid) =
    trimMuxState (TlsChatResponseMux.admit Word64.concrete ByteAuth.concrete state index id valid) := by
  simp only [TlsChatResponseMux.admit,trimMuxState,trim_stack_idempotent]

def muxInputEvent (capacity : Nat) (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64)) :
    MuxInput → TlsChatResponseMux.Event (BitVec 8) (BitVec 64)
  | .byte active beginning ending value =>
    TlsChatResponseMux.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete
      capacity state active beginning ending value
  | .admit index id valid =>
    ⟨TlsChatResponseMux.admit Word64.concrete ByteAuth.concrete state index id valid,0,0,0⟩

theorem trim_mux_input (capacity : Nat) (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (input : MuxInput) (safe : SafeStack state.parser) :
    trimMuxEvent (muxInputEvent capacity (trimMuxState state) input) =
    trimMuxEvent (muxInputEvent capacity state input) := by
  cases input with
  | byte active beginning ending value => exact trim_mux_process _ _ _ _ _ _ safe
  | admit index id valid =>
    change (⟨_,0,0,0⟩ : TlsChatResponseMux.Event (BitVec 8) (BitVec 64)) = ⟨_,0,0,0⟩
    simp only [muxInputEvent]
    rw [trim_mux_admit]

def muxProjectedTrace (capacity : Nat) (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64)) :
    List MuxInput → List (TlsChatResponseMux.Event (BitVec 8) (BitVec 64))
  | [] => []
  | input::rest =>
    let event := muxInputEvent capacity state input
    trimMuxEvent event :: muxProjectedTrace capacity event.state rest

def muxTrimmedTrace (capacity : Nat) (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64)) :
    List MuxInput → List (TlsChatResponseMux.Event (BitVec 8) (BitVec 64))
  | [] => []
  | input::rest =>
    let event := trimMuxEvent (muxInputEvent capacity state input)
    event :: muxTrimmedTrace capacity event.state rest

theorem mux_trimmed_trace_eq (capacity : Nat) (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (inputs : List MuxInput) (reachable : ReachableStack state.parser) :
    muxTrimmedTrace capacity (trimMuxState state) inputs = muxProjectedTrace capacity state inputs := by
  induction inputs generalizing state with
  | nil => rfl
  | cons input rest ih =>
    simp only [muxTrimmedTrace,muxProjectedTrace]
    rw [trim_mux_input capacity state input reachable.2]
    congr 1
    apply ih
    cases input with
    | byte active beginning ending value => exact mux_process_reachable _ _ _ _ _ _ reachable
    | admit index id valid => exact mux_admit_reachable _ _ _ _ reachable

theorem fresh_mux_trimmed_trace_eq (capacity : Nat) (inputs : List MuxInput) :
    muxTrimmedTrace capacity (TlsChatResponseMux.initial Word64.concrete ByteAuth.concrete capacity) inputs =
    muxProjectedTrace capacity (TlsChatResponseMux.initial Word64.concrete ByteAuth.concrete capacity) inputs := by
  have narrow := initial_narrow_stack capacity (Word64.concrete.const 0)
  have start : trimMuxState (TlsChatResponseMux.initial Word64.concrete ByteAuth.concrete capacity) =
      TlsChatResponseMux.initial Word64.concrete ByteAuth.concrete capacity := by
    simp only [trimMuxState,TlsChatResponseMux.initial,trim_stack_identity _ narrow]
  have eq := mux_trimmed_trace_eq capacity (TlsChatResponseMux.initial Word64.concrete ByteAuth.concrete capacity) inputs
    ⟨initial_control_masks capacity (Word64.concrete.const 0),.inr narrow⟩
  rw [start] at eq
  exact eq

#print axioms trim_mux_tail
#print axioms trim_mux_process
#print axioms trim_mux_admit
#print axioms mux_trimmed_trace_eq
#print axioms fresh_mux_trimmed_trace_eq
#print axioms mux_process_as_tail
#print axioms trim_correlated_parser
end ChatResponseReference.ParserCircuitCandidateV1
