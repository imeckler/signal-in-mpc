import ChatResponseReferenceWork.StreamingUnknownV1.GroupOpaqueStack
import ChatResponseReferenceWork.StreamingUnknownV1.OpaqueResume
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Complete arbitrary opaque payload at real group depth, exact source drop,
cache/control/private counters and unchanged depth/full stack. Strict count fits
leave private bytes for the mandatory group end. -/
theorem group_opaque_value_complete (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before : Slice U8) (count budget remaining : Nat)
    (ready : ChildReady (eraseGroupDepth state) before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < count) (strictFit : count < remaining)
    (modes : state.modes = lane 3) (kinds : state.kinds = [0,0,0,0]) (skip : state.skip = BitVec.ofNat 64 count) :
    ∃ consumed,
      consumed = (contents before).take count ∧ contents before = consumed ++ contents (drop before count) ∧
      CacheAgrees outer source (feed state consumed) ∧
      (feed state consumed).modes = lane 0 ∧ (feed state consumed).positions = oneHot 0 ∧
      (feed state consumed).value = 0 ∧ (feed state consumed).valid = 255 ∧
      (feed state consumed).depth = state.depth ∧ (feed state consumed).stack = state.stack ∧
      (feed state consumed).responseRemaining = BitVec.ofNat 64 (remaining-count) ∧
      (feed state consumed).inner = 255 := by
  obtain ⟨consumed,payload,span,flatCache,flatBoundary⟩ := unknown_opaque_resumes outer source (eraseGroupDepth state) before count budget remaining
    ready cache positive (by omega) modes kinds skip
  have contentLength : (contents before).length = before.length := by simp only [contents,List.length_map]
  have length : consumed.length = count := by
    rw [payload,List.length_take,contentLength,Nat.min_eq_left (by have := ready.physical; omega)]
  have projection := group_opaque_depth_projection state consumed count remaining ready.remainingBound (by rw [length]) strictFit
    modes ready.shape.kinds ready.inner skip ready.childCounter
  rw [projection] at flatCache flatBoundary
  have countBound : count < 2^64 := by have := ready.remainingBound; omega
  have scopeResult := opaque_scope_prefix state consumed count remaining ready.remainingBound ready.positive (by rw [length]) (by omega)
    modes skip ready.inner ready.childCounter
  have stack := group_opaque_prefix_stack state consumed count countBound (by rw [length]) modes skip
  have inner : (feed state consumed).inner = 255 := by
    have result := flatBoundary.inner
    rw [if_neg (by omega : remaining-count ≠ 0)] at result
    exact result
  exact ⟨consumed,payload,span,flatCache,flatBoundary.modes,flatBoundary.positions,flatBoundary.value,flatBoundary.valid,
    scopeResult.2.2,stack,by simpa only [length] using scopeResult.1,inner⟩

#print axioms group_opaque_value_complete
end ChatResponseReference.StreamingUnknownV1
