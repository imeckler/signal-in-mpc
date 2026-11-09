import ChatResponseReferenceWork.StreamingV1.OpaqueBody
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

/-- Every proper opaque prefix consumes exactly its own bytes and remains
opaque, independently of payload values or any parser-validity premise. -/
theorem opaque_prefix_inside (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (bytes : List (BitVec 8)) (count : Nat) (bounded : count < 2^64)
    (inside : bytes.length < count) (modes : state.modes = lane 3)
    (counter : state.skip = BitVec.ofNat 64 count) :
    (feed state bytes).modes = lane 3 ∧
    (feed state bytes).skip = BitVec.ofNat 64 (count-bytes.length) := by
  induction bytes generalizing state count with
  | nil => exact ⟨modes,counter⟩
  | cons byte rest ih =>
    let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state
    have notLast : state.skip ≠ BitVec.ofNat 64 1 := by
      intro equal
      rw [counter] at equal
      have numeric := congrArg BitVec.toNat equal
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt bounded] at numeric
      change count = 1 at numeric
      simp only [List.length_cons] at inside
      omega
    have nextModes : next.modes = lane 3 := by rw [opaque_mode_step state byte modes,if_neg notLast]
    have nextCounter : next.skip = BitVec.ofNat 64 (count-1) := by
      rw [opaque_skip_step state byte modes,counter]
      exact BitVec.ofNat_sub_ofNat_of_le count 1 (by decide) (by simp only [List.length_cons] at inside; omega)
    have result := ih next (count-1) (by omega) (by simp only [List.length_cons] at inside; omega) nextModes nextCounter
    refine ⟨result.1,?_⟩
    change (feed next rest).skip = _
    rw [result.2]
    congr 1
    simp only [List.length_cons]
    omega

/-- An undersized actual input cannot finish an opaque field by reading padding. -/
theorem opaque_truncated_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (bytes : List (BitVec 8)) (count : Nat) (bounded : count < 2^64)
    (inside : bytes.length < count) (modes : state.modes = lane 3)
    (counter : state.skip = BitVec.ofNat 64 count) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state bytes)).valid = 0 := by
  apply finish_nonkey
  rw [(opaque_prefix_inside state bytes count bounded inside modes counter).1]
  rfl

/-- Exact opaque payload completion returns to key mode with zero skip count. -/
theorem opaque_payload_complete (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (bytes : List (BitVec 8)) (nonempty : bytes ≠ []) (bounded : bytes.length < 2^64)
    (modes : state.modes = lane 3) (counter : state.skip = BitVec.ofNat 64 bytes.length) :
    (feed state bytes).modes = lane 0 ∧ (feed state bytes).skip = 0 := by
  have split := List.dropLast_concat_getLast nonempty
  have positive : 0 < bytes.length := List.length_pos_iff.mpr nonempty
  have leadingLength : bytes.dropLast.length = bytes.length-1 := List.length_dropLast
  have before := opaque_prefix_inside state bytes.dropLast bytes.length bounded (by omega) modes counter
  have remaining : (feed state bytes.dropLast).skip = BitVec.ofNat 64 1 := by
    rw [before.2]
    congr 1
    omega
  have nextModes := opaque_mode_step (feed state bytes.dropLast) (bytes.getLast nonempty) before.1
  rw [remaining,if_pos rfl] at nextModes
  have nextCounter := opaque_skip_step (feed state bytes.dropLast) (bytes.getLast nonempty) before.1
  rw [remaining] at nextCounter
  rw [←split]
  simp only [feed,List.foldl_append,List.foldl_cons,List.foldl_nil]
  exact ⟨nextModes,nextCounter⟩

#print axioms opaque_prefix_inside
#print axioms opaque_truncated_reject
#print axioms opaque_payload_complete
end ChatResponseReference.StreamingV1
