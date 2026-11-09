import ChatResponseReferenceWork.StreamingUnknownV1.OpaquePrefixValidity
import ChatResponseReferenceWork.StreamingV1.OpaqueScope
import ChatResponseReferenceWork.StreamingV1.OpaqueControls
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Complete nonempty unknown opaque payload: every byte is ignored by the
schema, source cache is unchanged, and exact child/public counters resume. -/
theorem unknown_opaque_resumes (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before : Slice U8) (count budget remaining : Nat)
    (ready : ChildReady state before budget remaining) (cache : CacheAgrees outer source state)
    (positive : 0 < count) (fits : count ≤ remaining)
    (modes : state.modes = lane 3) (kinds : state.kinds = [0,0,0,0]) (skip : state.skip = BitVec.ofNat 64 count) :
    ∃ consumed,
      consumed = (contents before).take count ∧
      contents before = consumed ++ contents (drop before count) ∧
      CacheAgrees outer source (feed state consumed) ∧
      ChildAtKey (feed state consumed) (drop before count) (budget-count) (remaining-count) := by
  let consumed := (contents before).take count
  have contentLength : (contents before).length = before.length := by simp only [contents,List.length_map]
  have length : consumed.length = count := by
    simp only [consumed,List.length_take,contentLength]
    exact Nat.min_eq_left (by have := ready.physical; omega)
  have bound : count < 2^64 := by have := ready.remainingBound; omega
  have span : contents before = consumed ++ contents (drop before count) := by
    have dropped : contents (drop before count) = (contents before).drop count := List.map_drop
    rw [dropped]
    exact (List.take_append_drop count (contents before)).symm
  have nonempty : consumed ≠ [] := by
    intro empty
    have nilLength := congrArg List.length empty
    simp only [length,List.length_nil] at nilLength
    omega
  have data := opaque_prefix_data state consumed count bound (by rw [length]) modes skip
  have valid := unknown_opaque_payload_prefix_valid state consumed count budget remaining ready.budgetBound ready.remainingBound
    (by rw [length]; have := ready.budgetEnough; have := ready.physical; omega) (by rw [length]) fits modes kinds
    ready.valid ready.seen ready.finished ready.inner ready.depth skip ready.budgetCounter ready.childCounter
  have control := opaque_prefix_controls state consumed count bound (by rw [length]) modes skip ready.shape.positions
  have completed := opaque_payload_complete state consumed nonempty (by rw [length]; exact bound) modes (by rw [length]; exact skip)
  have scopeResult := opaque_scope_prefix state consumed count remaining ready.remainingBound ready.positive (by rw [length]) fits
    modes skip ready.inner ready.childCounter
  have boundary := child_boundary_after state before (drop before count) budget remaining ready consumed span (by rw [length]; exact fits)
    (control.1.trans ready.positions) (control.2.trans ready.value) valid completed.1 scopeResult.2.2 scopeResult.1 scopeResult.2.1
  refine ⟨consumed,rfl,span,data.trans cache,?_⟩
  simpa only [length] using boundary

#print axioms unknown_opaque_resumes
end ChatResponseReference.StreamingUnknownV1
