import ChatResponseReferenceWork.ParserCircuitCandidateV1.StepStackSafe
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem valid_update_masks (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (value : BitVec 8)
    (previous : ControlMasks state) : ControlMasks {state with valid := value} :=
  ⟨previous.modes,previous.kinds,previous.inner⟩

theorem process_control_masks (capacity : Nat) (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (active beginning ending byte : BitVec 8) (previous : ControlMasks state) :
    ControlMasks (TlsChatResponse.process VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete capacity state active beginning ending byte).state := by
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
  have startedMasks : ControlMasks started := select_control_masks _ _ _ (canonical_byte_eq beginning 255) freshMasks previous
  have eventMasks : ControlMasks event.state := step_control_masks started byte startedMasks
  have selectedMasks : ControlMasks selected := valid_update_masks selected0 _
    (select_control_masks _ _ _ (canonical_byte_eq active 255) eventMasks startedMasks)
  exact select_control_masks _ _ _ (canonical_byte_eq ending 255) (finish_control_masks selected selectedMasks) selectedMasks

#print axioms process_control_masks
end ChatResponseReference.ParserCircuitCandidateV1
