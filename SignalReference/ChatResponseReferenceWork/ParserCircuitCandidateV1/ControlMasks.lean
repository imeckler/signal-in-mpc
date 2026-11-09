import ChatResponseReferenceWork.ParserCircuitCandidateV1.CanonicalMasks
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

structure ControlMasks (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) : Prop where
  modes : CanonicalList state.modes
  kinds : CanonicalList state.kinds
  inner : Canonical state.inner

theorem step_control_masks (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (byte : BitVec 8)
    (previous : ControlMasks state) :
    ControlMasks (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state := by
  have modeMask (i : Nat) := canonical_get state.modes i previous.modes
  have kindMask (i : Nat) := canonical_get state.kinds i previous.kinds
  have terminal := canonical_terminal byte
  constructor
  · intro mask member
    change mask ∈ [_,_,_,_] at member
    simp only [List.mem_cons,List.not_mem_nil,false_or,or_false] at member
    rcases member with rfl|rfl|rfl|rfl
    all_goals repeat' first
      | with_reducible exact terminal
      | with_reducible exact canonical_weq _ _
      | with_reducible exact modeMask _
      | with_reducible exact kindMask _
      | with_reducible apply canonical_either
      | with_reducible apply canonical_and
      | with_reducible apply canonical_not
  · change CanonicalList (TlsWebSocketUpgrade.choose ByteAuth.concrete _ [_,_,_,_] state.kinds)
    apply canonical_choose
    · exact canonical_and _ _ (modeMask 0) terminal
    · intro mask member
      simp only [List.mem_cons,List.not_mem_nil,false_or,or_false] at member
      rcases member with rfl|rfl|rfl|rfl
      all_goals repeat' first
        | with_reducible exact previous.inner
        | with_reducible exact canonical_weq _ _
        | with_reducible apply canonical_and
        | with_reducible apply canonical_not
    · exact previous.kinds
  · change Canonical (TlsInner.select ByteAuth.concrete _ _ (TlsInner.select ByteAuth.concrete _ 0 state.inner))
    repeat' first
      | with_reducible exact previous.inner
      | with_reducible exact canonical_zero
      | with_reducible exact terminal
      | with_reducible exact canonical_weq _ _
      | with_reducible exact modeMask _
      | with_reducible exact kindMask _
      | with_reducible apply canonical_select
      | with_reducible apply canonical_and
      | with_reducible apply canonical_not

theorem initial_control_masks (capacity : Nat) (expected : BitVec 64) :
    ControlMasks (TlsChatResponse.initial Word64.concrete ByteAuth.concrete capacity expected) := by
  constructor
  · change CanonicalList [255,0,0,0]
    intro mask member
    simp only [List.mem_cons,List.not_mem_nil,false_or,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> first | exact canonical_zero | exact canonical_hot
  · change CanonicalList [0,0,0,0]
    intro mask member
    simp only [List.mem_cons,List.not_mem_nil,false_or,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> exact canonical_zero
  · exact canonical_zero

theorem select_control_masks (mask : BitVec 8) (yes no : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (hm : Canonical mask) (hy : ControlMasks yes) (hn : ControlMasks no) :
    ControlMasks (TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete mask yes no) :=
  ⟨canonical_choose _ _ _ hm hy.modes hn.modes,canonical_choose _ _ _ hm hy.kinds hn.kinds,
    canonical_select _ _ _ hm hy.inner hn.inner⟩

theorem finish_control_masks (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (previous : ControlMasks state) :
    ControlMasks (TlsChatResponse.finish Word64.concrete ByteAuth.concrete state) :=
  ⟨previous.modes,previous.kinds,previous.inner⟩

#print axioms step_control_masks
#print axioms initial_control_masks
#print axioms select_control_masks
#print axioms finish_control_masks
end ChatResponseReference.ParserCircuitCandidateV1
