import ChatResponseReferenceWork.ParserCircuitCandidateV1.ProcessMasks
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.ParserCircuitCandidateV1

theorem narrow_zip_left (yes no : List (BitVec 64)) (old : NarrowStack yes) :
    NarrowStack (List.zipWith (Word64.concrete.select 255) yes no) := by
  induction yes generalizing no with
  | nil => intro value member; cases member
  | cons value rest ih =>
    cases no with
    | nil => intro value member; cases member
    | cons other tail =>
      intro result member
      change result ∈ Word64.concrete.select 255 value other :: List.zipWith (Word64.concrete.select 255) rest tail at member
      rw [Word64.select_accept] at member
      rcases List.mem_cons.mp member with rfl|later
      · exact old result (by simp)
      · exact ih tail (by intro x member; exact old x (by simp [member])) result later

theorem narrow_zip_right (yes no : List (BitVec 64)) (old : NarrowStack no) :
    NarrowStack (List.zipWith (Word64.concrete.select 0) yes no) := by
  induction yes generalizing no with
  | nil => intro value member; cases member
  | cons value rest ih =>
    cases no with
    | nil => intro value member; cases member
    | cons other tail =>
      intro result member
      change result ∈ Word64.concrete.select 0 value other :: List.zipWith (Word64.concrete.select 0) rest tail at member
      rw [Word64.select_reject] at member
      rcases List.mem_cons.mp member with rfl|later
      · exact old result (by simp)
      · exact ih tail (by intro x member; exact old x (by simp [member])) result later

theorem select_safe_stack (mask : BitVec 8) (yes no : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (hm : Canonical mask) (hy : SafeStack yes) (hn : SafeStack no) :
    SafeStack (TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete mask yes no) := by
  rcases hm with rfl|rfl
  · rcases hn with rejected|narrow
    · apply Or.inl
      change TlsInner.select ByteAuth.concrete 0 yes.valid no.valid = 0
      rw [TlsInner.select_reject,rejected]
    · exact .inr (narrow_zip_right yes.stack no.stack narrow)
  · rcases hy with rejected|narrow
    · apply Or.inl
      change TlsInner.select ByteAuth.concrete 255 yes.valid no.valid = 0
      rw [TlsInner.select_accept,rejected]
    · exact .inr (narrow_zip_left yes.stack no.stack narrow)

theorem guard_safe_stack (state : TlsChatResponse.State (BitVec 8) (BitVec 64)) (mask : BitVec 8)
    (old : SafeStack state) : SafeStack {state with valid := ByteAuth.concrete.and state.valid mask} := by
  rcases old with rejected|narrow
  · apply Or.inl
    change ByteAuth.concrete.and state.valid mask = 0
    rw [rejected]
    exact BitVec.zero_and
  · exact .inr narrow

#print axioms narrow_zip_left
#print axioms narrow_zip_right
#print axioms select_safe_stack
#print axioms guard_safe_stack
end ChatResponseReference.ParserCircuitCandidateV1
