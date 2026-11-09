import ChatResponseReferenceWork.ParserCircuitCandidateV1.ProcessStackSafe
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1
open TlsChatResponseMux
open TlsWebSocketUpgrade (get eq either any)
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem guard2_zero (first second rest : BitVec 8) (zero : second = 0) :
    ByteAuth.concrete.and first (ByteAuth.concrete.and second rest) = 0 := by
  rw [zero]
  have zeroAnd (mask : BitVec 8) : ByteAuth.concrete.and 0 mask = 0 := BitVec.zero_and
  have andZero (mask : BitVec 8) : ByteAuth.concrete.and mask 0 = 0 := BitVec.and_zero
  rw [zeroAnd,andZero]

private theorem mux_selected_safe (valid done : BitVec 8) (reset parsed : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (parsedSafe : SafeStack parsed) (resetNarrow : NarrowStack reset.stack) (doneCanonical : Canonical done)
    (zeroGlobal : parsed.valid = 0 → valid = 0) :
    SafeStack (validCore (TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete done reset parsed) valid) := by
  by_cases rejected : valid = 0
  · exact .inl rejected
  · have parsedNonzero : parsed.valid ≠ 0 := fun zero => rejected (zeroGlobal zero)
    have parsedNarrow : NarrowStack parsed.stack := parsedSafe.resolve_left parsedNonzero
    apply Or.inr
    change NarrowStack (List.zipWith (Word64.concrete.select done) reset.stack parsed.stack)
    rcases doneCanonical with inactive|active
    · rw [inactive]; exact narrow_zip_right _ _ parsedNarrow
    · rw [active]; exact narrow_zip_left _ _ resetNarrow

private theorem after_correlation_reachable (capacity : Nat)
    (parsed : TlsChatResponse.State (BitVec 8) (BitVec 64)) (outer rest done : BitVec 8)
    (old : ReachableStack parsed) (doneCanonical : Canonical done) :
    let valid := ByteAuth.concrete.and outer (ByteAuth.concrete.and parsed.valid rest)
    let reset := validCore (TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity (Word64.concrete.const 0)) valid
    ReachableStack (validCore (TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete done reset parsed) valid) := by
  intro valid reset
  have initialMasks := initial_control_masks capacity (Word64.concrete.const 0)
  have resetMasks : ControlMasks reset := ⟨initialMasks.modes,initialMasks.kinds,initialMasks.inner⟩
  have selectedMasks := select_control_masks done reset parsed doneCanonical resetMasks old.1
  refine ⟨⟨selectedMasks.modes,selectedMasks.kinds,selectedMasks.inner⟩,?_⟩
  exact mux_selected_safe valid done reset parsed old.2 (initial_narrow_stack capacity (Word64.concrete.const 0)) doneCanonical
    (fun zero => guard2_zero outer parsed.valid rest zero)

/-- Actual Mux reset/validation preserves conditional stack reachability for all
private controls, ID/status/correlation outcomes and malformed byte strings. -/
theorem mux_process_reachable (capacity : Nat) (s : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (active beginning ending x : BitVec 8) (old : ReachableStack s.parser) :
    ReachableStack (TlsChatResponseMux.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete capacity s active beginning ending x).state.parser := by
  let parsed := TlsChatResponse.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete capacity s.parser active beginning (ByteAuth.concrete.const 0) x
  let finished := TlsChatResponse.finish Word64.concrete ByteAuth.concrete (selfExpected parsed.state)
  let slots := s.slots.map (prepareSlot ByteAuth.concrete beginning)
  let masks := slots.map (matchSlot Word64.concrete ByteAuth.concrete parsed.state.id)
  let eligible := any ByteAuth.concrete (slots.map (fun slot => ByteAuth.concrete.and (eq ByteAuth.concrete slot.active 255)
    (ByteAuth.concrete.and (eq ByteAuth.concrete slot.eligible 255) (ByteAuth.concrete.not (eq ByteAuth.concrete slot.consumed 255)))))
  let beginReady := either ByteAuth.concrete (ByteAuth.concrete.not (eq ByteAuth.concrete beginning 255)) eligible
  let done := eq ByteAuth.concrete ending 255
  let canonical := either ByteAuth.concrete (eq ByteAuth.concrete ending 0) done
  let room := TlsWebSocketUpgrade.member ByteAuth.concrete s.queued [0,1,2,3]
  -- Current application policy closes the connection on ByteAuth.concrete non2xx response.
  let accepted := ByteAuth.concrete.and finished.valid (ByteAuth.concrete.and finished.successful (ByteAuth.concrete.and (exactlyOne ByteAuth.concrete masks) room))
  let valid := ByteAuth.concrete.and s.valid (ByteAuth.concrete.and parsed.state.valid
    (ByteAuth.concrete.and canonical (ByteAuth.concrete.and beginReady (either ByteAuth.concrete (ByteAuth.concrete.not done) accepted))))
  let enqueue := ByteAuth.concrete.and done valid
  let reset := validCore (TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity (Word64.concrete.const 0)) valid
  let parser := validCore (TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete done reset parsed.state) valid
  change ReachableStack parser
  exact after_correlation_reachable capacity parsed.state s.valid
    (ByteAuth.concrete.and canonical (ByteAuth.concrete.and beginReady (either ByteAuth.concrete (ByteAuth.concrete.not done) accepted))) done
    (process_reachable_stack capacity s.parser active beginning (ByteAuth.concrete.const 0) x old) (canonical_byte_eq ending 255)

theorem mux_admit_reachable (s : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (index : BitVec 8) (id : BitVec 64) (validity : BitVec 8) (old : ReachableStack s.parser) :
    ReachableStack (TlsChatResponseMux.admit Word64.concrete ByteAuth.concrete s index id validity).parser := old

inductive MuxInput where
  | byte (active beginning ending value : BitVec 8)
  | admit (index : BitVec 8) (id : BitVec 64) (validity : BitVec 8)

def muxAdvance (capacity : Nat) (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64)) : MuxInput → TlsChatResponseMux.State (BitVec 8) (BitVec 64)
  | .byte active beginning ending value => (TlsChatResponseMux.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete capacity state active beginning ending value).state
  | .admit index id validity => TlsChatResponseMux.admit Word64.concrete ByteAuth.concrete state index id validity

def muxRun (capacity : Nat) (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64)) (inputs : List MuxInput) :=
  inputs.foldl (muxAdvance capacity) state

theorem muxRun_reachable (capacity : Nat) (state : TlsChatResponseMux.State (BitVec 8) (BitVec 64))
    (inputs : List MuxInput) (old : ReachableStack state.parser) : ReachableStack (muxRun capacity state inputs).parser := by
  induction inputs generalizing state with
  | nil => exact old
  | cons input rest ih =>
    cases input with
    | byte active beginning ending value => exact ih _ (mux_process_reachable capacity state active beginning ending value old)
    | admit index id validity => exact ih _ (mux_admit_reachable state index id validity old)

theorem fresh_muxRun_reachable (capacity : Nat) (inputs : List MuxInput) :
    ReachableStack (muxRun capacity (TlsChatResponseMux.initial Word64.concrete ByteAuth.concrete capacity) inputs).parser :=
  muxRun_reachable capacity _ inputs ⟨initial_control_masks capacity 0,.inr (initial_narrow_stack capacity (Word64.concrete.const 0))⟩

#print axioms mux_process_reachable
#print axioms mux_admit_reachable
#print axioms muxRun_reachable
#print axioms fresh_muxRun_reachable
end ChatResponseReference.ParserCircuitCandidateV1
