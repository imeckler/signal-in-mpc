import ChatResponseReferenceWork.StreamingV1.ResponseData
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

/-- No cached response data changes during a continuing varint prefix. -/
theorem nonterminal_prefix_data (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (leading : List (BitVec 8)) (continues : ∀ byte ∈ leading, VarintDecode.Spqr.terminates byte = false) :
    responseData (feed state leading) = responseData state := by
  induction leading generalizing state with
  | nil => rfl
  | cons byte rest ih =>
    have result := ih
      (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state
      (by intro x member; exact continues x (by simp [member]))
    exact result.trans (nonterminal_response_data state byte (continues byte (by simp)))

/-- Proper and exact opaque payload prefixes preserve every cached response data
field, independently of payload values or the current validity mask. -/
theorem opaque_prefix_data (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (bytes : List (BitVec 8)) (count : Nat) (bounded : count < 2^64)
    (inside : bytes.length ≤ count) (modes : state.modes = lane 3)
    (counter : state.skip = BitVec.ofNat 64 count) :
    responseData (feed state bytes) = responseData state := by
  induction bytes generalizing state count with
  | nil => rfl
  | cons byte rest ih =>
    cases rest with
    | nil => exact opaque_response_data state byte modes
    | cons next tail =>
      let after := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state
      have first := opaque_prefix_inside state [byte] count bounded (by simp only [List.length_cons,List.length_nil] at *; omega) modes counter
      have nextModes : after.modes = lane 3 := first.1
      have nextCounter : after.skip = BitVec.ofNat 64 (count-1) := first.2
      have result := ih after (count-1) (by omega) (by simp only [List.length_cons] at *; omega) nextModes nextCounter
      exact result.trans (opaque_response_data state byte modes)

#print axioms nonterminal_prefix_data
#print axioms opaque_prefix_data
end ChatResponseReference.StreamingV1
