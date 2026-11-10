import ChatResponseReferenceWork.StreamingUnknownV1.GroupSourceProgress
import ChatResponseReferenceWork.StreamingUnknownV1.GroupOutcomePrefix
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
open LibSignalReference.Candidate.ProstSkip
open LoopSupportSkip
set_option maxHeartbeats 1000000

/-- Join a real source body continuation and exact numeric prefix, retaining
both the actual recursive result and its complete all-outcome observation. -/
theorem group_continue_outcome (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8)
    (parent count : U32) (older : List U32) (budget remaining : Nat)
    (result : core.result.Result Unit error.DecodeError × Slice U8) (consumed : List (BitVec 8))
    (body : encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before = .ok (.cont middle))
    (rest : encoding.skip_field_loop sliceBuf parent middle ⟨count⟩ = .ok result)
    (span : contents before = consumed++contents middle) (fits : consumed.length ≤ remaining)
    (post : GroupOutcome outer source (feed state consumed) middle (budget-consumed.length) (remaining-consumed.length) older count result) :
    encoding.skip_field_loop sliceBuf parent before ⟨count⟩ = .ok result ∧
      GroupOutcome outer source state before budget remaining older count result := by
  constructor
  · rw [group_loop_cont before middle parent ⟨count⟩ body]
    exact rest
  · exact group_outcome_prefix outer source state before middle budget remaining older count result consumed span fits post

/-- If a real body continuation has exhausted its private child, derive the
remaining source run and exact suffix from totality. Every source success must
consume another group key and therefore lies strictly beyond that child. -/
theorem group_exhausted_continue_outcome (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8)
    (parent count : U32) (older : List U32) (budget remaining : Nat)
    (positive : count ≠ 0#u32)
    (body : encoding.skip_field_loop.body sliceBuf parent ⟨count⟩ before = .ok (.cont middle))
    (exhausted : middle.length ≤ before.length-remaining)
    (rejected : (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0) :
    ∃ result, encoding.skip_field_loop sliceBuf parent before ⟨count⟩ = .ok result ∧
      GroupOutcome outer source state before budget remaining older count result := by
  obtain ⟨result,derivation,run,bound⟩ := FullParserV3.skip_group_total parent count middle positive
  refine ⟨result,?_,?_⟩
  · rw [group_loop_cont before middle parent ⟨count⟩ body]
    exact run
  · apply group_outcome_of_rejected outer source state before budget remaining older count result rejected
    intro success
    have strict := group_grammar_success_decreases derivation positive success
    omega

/-- An already-exhausted non-end key cannot yield a compatible native group
success. This keeps the exact source run/error/suffix even when the circuit
rejects before executing the physical continuation. -/
theorem group_exhausted_nonend_outcome (outer : ResponseData) (source : InnerResponseV1.Message)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before middle : Slice U8)
    (parent tag count : U32) (wire : encoding.wire_type.WireType) (older : List U32) (budget remaining : Nat)
    (positive : count ≠ 0#u32) (notEnd : wire ≠ .EndGroup)
    (keyRun : encoding.decode_key sliceBuf before = .ok (.Ok (tag,wire),middle))
    (exhausted : middle.length ≤ before.length-remaining)
    (rejected : (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0) :
    ∃ result, encoding.skip_field_loop sliceBuf parent before ⟨count⟩ = .ok result ∧
      GroupOutcome outer source state before budget remaining older count result := by
  obtain ⟨result,derivation,run,bound⟩ := FullParserV3.skip_group_total parent count before positive
  refine ⟨result,run,?_⟩
  apply group_outcome_of_rejected outer source state before budget remaining older count result rejected
  intro success
  have strict := group_success_after_nonend_key derivation positive success tag wire middle notEnd keyRun
  omega

#print axioms group_continue_outcome
#print axioms group_exhausted_continue_outcome
#print axioms group_exhausted_nonend_outcome
end ChatResponseReference.StreamingUnknownV1
