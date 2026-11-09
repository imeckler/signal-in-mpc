import ChatResponseReferenceWork.StreamingV1.NativePrefix
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

theorem spec_run_done (wire : List (BitVec 8)) (fuel index : Nat) (value : BitVec 64) :
    VarintDecode.Spqr.run wire fuel index value true = ⟨value,index,true⟩ := by
  cases fuel <;> rfl

theorem spec_run_add (wire : List (BitVec 8)) (first second index : Nat)
    (value : BitVec 64) (done : Bool) :
    VarintDecode.Spqr.run wire (first+second) index value done =
      let middle := VarintDecode.Spqr.run wire first index value done
      VarintDecode.Spqr.run wire second middle.index middle.value middle.done := by
  induction first generalizing index value done with
  | zero => simp only [Nat.zero_add,VarintDecode.Spqr.run]
  | succ first ih =>
    cases done with
    | false =>
      simpa only [Nat.succ_add,VarintDecode.Spqr.run,Bool.false_eq_true,if_false] using
        ih (index+1) (value ||| VarintDecode.Spqr.payload (wire[index]?.getD 0) index)
          (VarintDecode.Spqr.terminates (wire[index]?.getD 0))
    | true =>
      simp only [Nat.succ_add,VarintDecode.Spqr.run,if_true]
      exact (spec_run_done wire second index value).symm

/-- Full nonterminating prefix, with explicit lookup/remaining-span evidence.
Each actual lookup is inside the supplied input; missing bytes cannot stand in
for padding or a zero terminator. -/
theorem spec_run_prefix (wire bytes tail : List (BitVec 8)) (index : Nat) (value : BitVec 64)
    (span : wire.drop index = bytes ++ tail)
    (continues : ∀ byte ∈ bytes, VarintDecode.Spqr.terminates byte = false) :
    VarintDecode.Spqr.run wire bytes.length index value false =
      ⟨accumulated bytes index value,index+bytes.length,false⟩ := by
  induction bytes generalizing index value with
  | nil => rfl
  | cons byte rest ih =>
    have first : wire[index]? = some byte := by
      simpa only [List.head?_drop,List.cons_append,List.head?_cons] using
        congrArg (fun bytes : List (BitVec 8) => bytes.head?) span
    have nextSpan : wire.drop (index+1) = rest ++ tail := by
      simpa [List.drop_drop,Nat.add_comm] using congrArg (fun bytes : List (BitVec 8) => bytes.drop 1) span
    have nonterminal := continues byte (by simp)
    simp only [List.length_cons,VarintDecode.Spqr.run,Bool.false_eq_true,if_false,first,Option.getD_some,nonterminal]
    have result := ih (index+1) (value ||| VarintDecode.Spqr.payload byte index) nextSpan
      (by intro byte member; exact continues byte (by simp [member]))
    simpa only [accumulated,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result

/-- The actual Core's complete prefix accumulation agrees with the executable
reader used by the accepted native Prost primitive reference. -/
theorem core_prefix_reader_value (state : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (wire bytes tail : List (BitVec 8)) (role group : Nat) (roleBound : role < 3)
    (bound : group+bytes.length ≤ 9) (modes : state.modes = lane role)
    (positions : state.positions = oneHot group) (span : wire.drop group = bytes ++ tail)
    (continues : ∀ byte ∈ bytes, VarintDecode.Spqr.terminates byte = false) :
    (feed state bytes).value = (VarintDecode.Spqr.run wire bytes.length group state.value false).value := by
  rw [(core_prefix_invariant state bytes role group roleBound bound modes positions continues).2.2,
    spec_run_prefix wire bytes tail group state.value span continues]
#print axioms spec_run_add
#print axioms spec_run_prefix
#print axioms core_prefix_reader_value
end ChatResponseReference.StreamingV1
