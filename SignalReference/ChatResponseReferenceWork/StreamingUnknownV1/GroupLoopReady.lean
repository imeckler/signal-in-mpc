import ChatResponseReferenceWork.StreamingUnknownV1.GroupDepthProjection
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingUnknownV1
open ChatResponseReference.StreamingV1

/-- Explicit recursive inner-group relation. The real state retains its depth;
the proof-local erased common state shares every cache, counter and byte control.
Only active slots are related; stale inactive slots remain observable storage. -/
structure GroupLoopReady (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (view : Slice U8) (budget remaining : Nat) (parents : List U32) (count : U32) : Prop where
  common : ChildReady (eraseGroupDepth state) view budget remaining
  modes : state.modes = lane 0
  positive : 0 < parents.length
  bounded : parents.length ≤ 99
  depth : state.depth = BitVec.ofNat 64 parents.length
  slots : ∀ (index : Nat) (inside : index < parents.length),
    state.stack[index]'(by have size : state.stack.length = 100 := common.shape.stack; omega) = BitVec.ofNat 64 (parents[index]).val
  context : count.val + parents.length = 100

end ChatResponseReference.StreamingUnknownV1
