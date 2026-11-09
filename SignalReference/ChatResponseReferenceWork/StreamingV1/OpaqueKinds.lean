import ChatResponseReferenceWork.StreamingV1.StringUtfRejection
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
theorem opaque_prefix_kinds (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (bytes : List (BitVec 8)) (count : Nat) (bounded : count < 2^64)
    (inside : bytes.length ≤ count) (modes : state.modes = lane 3)
    (counter : state.skip = BitVec.ofNat 64 count) (shape : state.kinds.length = 4) :
    (feed state bytes).kinds = state.kinds := by
  induction bytes generalizing state count with
  | nil => rfl
  | cons byte rest ih =>
    cases rest with
    | nil => exact opaque_kinds_step state byte modes shape
    | cons next tail =>
      let after := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state
      have first := opaque_prefix_inside state [byte] count bounded (by simp only [List.length_cons,List.length_nil] at *; omega) modes counter
      have nextModes : after.modes = lane 3 := first.1
      have nextCounter : after.skip = BitVec.ofNat 64 (count-1) := first.2
      have result := ih after (count-1) (by omega) (by simp only [List.length_cons] at *; omega) nextModes nextCounter (by rw [opaque_kinds_step state byte modes shape]; exact shape)
      exact result.trans (opaque_kinds_step state byte modes shape)

#print axioms opaque_prefix_kinds
end ChatResponseReference.StreamingV1
