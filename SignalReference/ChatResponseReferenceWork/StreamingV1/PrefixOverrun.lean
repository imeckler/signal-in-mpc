import ChatResponseReferenceWork.StreamingV1.LengthRejection
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1
open LibSignalReference.Candidate.ProstSkipKey

/-- Every key/scalar/length continuing prefix that reaches a declared child end
rejects, even if later parent-buffer bytes would terminate the native varint.
No source decoder outcome, prefix value or position premise is needed. -/
theorem varint_child_prefix_overrun (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (leading tail : List (BitVec 8)) (remaining role : Nat) (roleBound : role < 3)
    (capacity : remaining ≤ 4096) (positive : 0 < remaining) (crosses : remaining ≤ leading.length)
    (modes : state.modes = lane role) (inner : state.inner = 255)
    (counter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (continues : ∀ byte ∈ leading, VarintDecode.Spqr.terminates byte = false) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (leading ++ tail))).valid = 0 := by
  induction leading generalizing state remaining with
  | nil => simp only [List.length_nil] at crosses; omega
  | cons byte rest ih =>
    have nonterminal := continues byte (by simp)
    let next := (TlsChatResponse.step VarintDecode.Spqr.concrete Word64.concrete ByteAuth.concrete state byte).state
    by_cases last : remaining = 1
    · have boundary : state.responseRemaining = BitVec.ofNat 64 1 := by rw [counter,last]
      have invalid : next.valid = 0 := core_close_nonterminal_reject state byte role roleBound modes inner boundary nonterminal
      apply finish_invalid_sticky
      change (feed next (rest ++ tail)).valid = 0
      exact feed_invalid_sticky next (rest ++ tail) invalid
    · have notLast : TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1 = 0 := by
        rw [counter]
        unfold TlsChatResponse.weq
        rw [word_eq_value]
        apply if_neg
        intro equal
        have numeric := congrArg BitVec.toNat equal
        have small : remaining < 2^64 := by omega
        simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at numeric
        change remaining = 1 at numeric
        exact last numeric
      have notClosing : ByteAuth.concrete.and state.inner
          (TlsChatResponse.weq Word64.concrete ByteAuth.concrete state.responseRemaining 1) = 0 := by rw [inner,notLast]; rfl
      have nextInner : next.inner = 255 := (nonterminal_inner state byte nonterminal notClosing).trans inner
      have nextCounter : next.responseRemaining = BitVec.ofNat 64 (remaining-1) := by
        rw [nonterminal_remaining state byte nonterminal inner,counter]
        exact BitVec.ofNat_sub_ofNat_of_le remaining 1 (by decide) (by omega)
      have nextModes : next.modes = lane role := core_modes_continue state role roleBound byte modes nonterminal
      exact ih next (remaining-1) (by omega) (by omega) (by simp only [List.length_cons] at crosses; omega)
        nextModes nextInner nextCounter (by intro x member; exact continues x (by simp [member]))

open Aeneas Aeneas.Std
open LibSignalReference.Candidate.ProstSkipBuf LibSignalReference.Candidate.ProstSkipSlice
/-- Any actual successful native key/scalar/length varint that consumed past its
child end still makes the complete Core input reject, with no prefix premise. -/
theorem native_varint_child_overrun_reject (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (before after : Slice U8) (native : U64) (remaining role : Nat) (roleBound : role < 3)
    (capacity : remaining ≤ 4096) (positive : 0 < remaining) (physical : remaining ≤ before.length)
    (overrun : after.length < before.length-remaining)
    (modes : state.modes = lane role) (inner : state.inner = 255)
    (counter : state.responseRemaining = BitVec.ofNat 64 remaining)
    (sourceSuccess : LoopSupportSkip.encoding.varint.decode_varint sliceBuf before = .ok (.Ok native,after)) :
    (TlsChatResponse.finish Word64.concrete ByteAuth.concrete (feed state (contents before))).valid = 0 := by
  obtain ⟨leading,byte,tail,span,suffix,bound,continues,terminal,tenth,nativeValue⟩ := native_success_span before after native sourceSuccess
  have tailLength : tail.length = after.length := by
    have result := congrArg List.length suffix
    simpa only [contents,List.length_map] using result.symm
  have inputLength : before.length = leading.length+1+after.length := by
    have result := congrArg List.length span
    simpa only [contents,List.length_map,List.length_append,List.length_cons,tailLength,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result
  have crosses : remaining ≤ leading.length := by omega
  rw [span]
  exact varint_child_prefix_overrun state leading (byte::tail) remaining role roleBound capacity positive crosses modes inner counter continues

#print axioms varint_child_prefix_overrun
#print axioms native_varint_child_overrun_reject
end ChatResponseReference.StreamingV1
