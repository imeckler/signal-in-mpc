import ChatResponseReferenceWork.StreamingUnknownV1.GroupDepthProjection
import ChatResponseReferenceWork.StreamingUnknownV1.GroupStackLookup
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Full scalar/length varint byte-span depth projection from explicit strict
private remaining-input bounds. Control/closing guards are derived at every byte;
no per-step validity, lookup or successful-parse assumption is supplied. -/
theorem group_varint_depth_projection (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (leading : List (BitVec 8)) (terminal : BitVec 8) (role remaining : Nat)
    (roleClass : role = 1 ∨ role = 2) (modes : state.modes = lane role)
    (kindShape : state.kinds.length = 4) (inner : state.inner = 255)
    (remainingBound : remaining ≤ 4096) (inside : leading.length+1 < remaining)
    (counter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (continues : ∀ byte ∈ leading, VarintDecode.Spqr.terminates byte = false) :
    feed (eraseGroupDepth state) (leading++[terminal]) = eraseGroupDepth (feed state (leading++[terminal])) := by
  induction leading generalizing state remaining with
  | nil =>
    have notLast : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1 = 0 := by
      rw [counter,stack_index_eq remaining 1 (by omega) (by decide)]
      exact if_neg (by simp only [List.length_nil] at inside; omega)
    have result := congrArg TlsChatResponse.Event.state
      (nonkey_depth_projection state terminal role (roleClass.elim Or.inl (fun h => Or.inr (Or.inl h))) modes kindShape notLast)
    simpa only [feed,List.nil_append,List.foldl_cons,List.foldl_nil] using result
  | cons byte rest ih =>
    let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state
    have nonterminal := continues byte (by simp)
    have roleBound : role < 3 := by rcases roleClass with h|h <;> omega
    have notLast : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1 = 0 := by
      rw [counter,stack_index_eq remaining 1 (by omega) (by decide)]
      exact if_neg (by simp only [List.length_cons] at inside; omega)
    have notClosing : ByteAuth.concrete.and state.inner
        (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1) = 0 := by rw [inner,notLast]; rfl
    have nextInner : next.inner = 255 := (nonterminal_inner state byte nonterminal notClosing).trans inner
    have nextCounter : next.responseRemaining = BitVec.ofNat 64 (remaining-1) := by
      rw [nonterminal_remaining state byte nonterminal inner,counter]
      exact BitVec.ofNat_sub_ofNat_of_le remaining 1 (by decide) (by simp only [List.length_cons] at inside; omega)
    have stateStep := congrArg TlsChatResponse.Event.state
      (nonkey_depth_projection state byte role (roleClass.elim Or.inl (fun h => Or.inr (Or.inl h))) modes kindShape notLast)
    have result := ih next (remaining-1) (core_modes_continue state role roleBound byte modes nonterminal)
      (key_kinds_shape state byte kindShape) nextInner (by omega) (by simp only [List.length_cons] at inside; omega) nextCounter
      (by intro x member; exact continues x (by simp [member]))
    change feed (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete (eraseGroupDepth state) byte).state (rest++[terminal]) =
      eraseGroupDepth (feed next (rest++[terminal]))
    rw [stateStep]
    exact result

#print axioms group_varint_depth_projection
end ChatResponseReference.StreamingUnknownV1
