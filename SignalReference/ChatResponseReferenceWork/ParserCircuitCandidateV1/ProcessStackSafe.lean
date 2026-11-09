import ChatResponseReferenceWork.ParserCircuitCandidateV1.SelectStackSafe
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem process_safe_stack (capacity : Nat) (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (active beginning ending byte : BitVec 8) (old : SafeStack state) (controls : ControlMasks state) :
    SafeStack (TlsChatResponse.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete capacity state active beginning ending byte).state := by
  let fresh := {TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity state.expected with
    valid := ByteAuth.concrete.and state.valid (ByteAuth.concrete.not state.seen),seen := 255}
  let started := TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete (TlsWebSocketUpgrade.eq ByteAuth.concrete beginning 255) fresh state
  let event := TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete started byte
  let selected0 := TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete (TlsWebSocketUpgrade.eq ByteAuth.concrete active 255) event.state started
  let canonical := ([active,beginning,ending]).foldl (fun valid mask =>
    ByteAuth.concrete.and valid (TlsWebSocketUpgrade.either ByteAuth.concrete
      (TlsWebSocketUpgrade.eq ByteAuth.concrete mask 0) (TlsWebSocketUpgrade.eq ByteAuth.concrete mask 255))) 255
  let selected := {selected0 with valid := ByteAuth.concrete.and selected0.valid canonical}
  have initialMasks := initial_control_masks capacity state.expected
  have freshMasks : ControlMasks fresh := ⟨initialMasks.modes,initialMasks.kinds,initialMasks.inner⟩
  have freshSafe : SafeStack fresh := .inr (initial_narrow_stack capacity state.expected)
  have startedMasks : ControlMasks started := select_control_masks _ _ _ (canonical_byte_eq beginning 255) freshMasks controls
  have startedSafe : SafeStack started := select_safe_stack _ _ _ (canonical_byte_eq beginning 255) freshSafe old
  have eventSafe : SafeStack event.state := step_safe_stack started byte startedSafe startedMasks
  have selectedSafe : SafeStack selected := guard_safe_stack selected0 canonical
    (select_safe_stack _ _ _ (canonical_byte_eq active 255) eventSafe startedSafe)
  exact select_safe_stack _ _ _ (canonical_byte_eq ending 255) (finish_safe_stack selected selectedSafe) selectedSafe

def ReachableStack (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) : Prop := ControlMasks state ∧ SafeStack state

theorem process_reachable_stack (capacity : Nat) (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (active beginning ending byte : BitVec 8) (old : ReachableStack state) :
    ReachableStack (TlsChatResponse.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete capacity state active beginning ending byte).state :=
  ⟨process_control_masks capacity state active beginning ending byte old.1,process_safe_stack capacity state active beginning ending byte old.2 old.1⟩

def coreRun (capacity : Nat) (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (inputs : List (BitVec 8 × BitVec 8 × BitVec 8 × BitVec 8)) : TlsChatResponse.State (BitVec 8) (BitVec 64) :=
  inputs.foldl (fun state input => (TlsChatResponse.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete capacity
    state input.1 input.2.1 input.2.2.1 input.2.2.2).state) state

theorem coreRun_reachable (capacity : Nat) (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (inputs : List (BitVec 8 × BitVec 8 × BitVec 8 × BitVec 8)) (old : ReachableStack state) : ReachableStack (coreRun capacity state inputs) := by
  induction inputs generalizing state with
  | nil => exact old
  | cons input rest ih => exact ih _ (process_reachable_stack capacity state input.1 input.2.1 input.2.2.1 input.2.2.2 old)

theorem fresh_coreRun_reachable (capacity : Nat) (expected : BitVec 64)
    (inputs : List (BitVec 8 × BitVec 8 × BitVec 8 × BitVec 8)) :
    ReachableStack (coreRun capacity (TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity expected) inputs) :=
  coreRun_reachable capacity _ inputs ⟨initial_control_masks capacity expected,.inr (initial_narrow_stack capacity expected)⟩

#print axioms process_safe_stack
#print axioms process_reachable_stack
#print axioms coreRun_reachable
#print axioms fresh_coreRun_reachable
end ChatResponseReference.ParserCircuitCandidateV1
