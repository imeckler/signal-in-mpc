import ChatResponseReferenceWork.StreamingUnknownV1.FixedSource
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem actual_unknown_fixed_resumes (outer : ResponseData) (source : InnerResponseV1.Message) (tag : U32)
    (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (before : Slice U8)
    (ctx : ActualInnerResponseV1.prost.encoding.DecodeContext) (budget remaining : Nat) (wide : Bool)
    (unknownTag : 5 < tag.val) (count : ctx.recurse_count ≠ 0#u32)
    (ready : ChildReady state before budget remaining) (cache : CacheAgrees outer source state)
    (fits : (if wide then 8 else 4) ≤ remaining)
    (modes : state.modes = lane 3) (kinds : state.kinds = [0,0,0,0])
    (skip : state.skip = BitVec.ofNat 64 (if wide then 8 else 4)) :
    ActualInnerResponseV1.merge_response InnerResponseV1.sliceBuf source tag
      (if wide then .SixtyFourBit else .ThirtyTwoBit) before ctx =
      .ok (.Ok (),source,drop before (if wide then 8 else 4)) ∧
    ∃ consumed,
      consumed = (contents before).take (if wide then 8 else 4) ∧
      contents before = consumed ++ contents (drop before (if wide then 8 else 4)) ∧
      CacheAgrees outer source (feed state consumed) ∧
      ChildAtKey (feed state consumed) (drop before (if wide then 8 else 4))
        (budget-(if wide then 8 else 4)) (remaining-(if wide then 8 else 4)) := by
  have sourceRun := unknown_fixed_source_all source tag before ctx wide unknownTag count
  have physical : ¬before.length < (if wide then 8 else 4) := by have := ready.physical; omega
  simp only [LibSignalReference.Candidate.ProstSkip.fixedResult,if_neg physical,
    unchangedSkipResult,InnerResponseV1.skipResult] at sourceRun
  refine ⟨sourceRun,?_⟩
  exact unknown_opaque_resumes outer source state before (if wide then 8 else 4) budget remaining ready cache
    (by cases wide <;> decide) fits modes kinds skip

#print axioms actual_unknown_fixed_resumes
end ChatResponseReference.StreamingUnknownV1
