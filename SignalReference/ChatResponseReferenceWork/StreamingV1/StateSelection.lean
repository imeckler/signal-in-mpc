import ChatResponseReferenceWork.StreamingV1.StateShape
open TlsMpc TlsMpc.Signal
namespace ChatResponseReference.StreamingV1

private theorem word_list_reject (yes no : List (BitVec 64)) (length : yes.length = no.length) :
    List.zipWith (Word64.concrete.select 0) yes no = no := by
  induction yes generalizing no with
  | nil => cases no <;> simp_all
  | cons y ys ih =>
    cases no with
    | nil => simp at length
    | cons n ns =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at length
      simp only [List.zipWith_cons_cons,Word64.select_reject]
      exact congrArg (List.cons n) (ih ns length)

private theorem word_list_accept (yes no : List (BitVec 64)) (length : yes.length = no.length) :
    List.zipWith (Word64.concrete.select 255) yes no = yes := by
  induction yes generalizing no with
  | nil => cases no <;> simp_all
  | cons y ys ih =>
    cases no with
    | nil => simp at length
    | cons n ns =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at length
      simp only [List.zipWith_cons_cons,Word64.select_accept]
      exact congrArg (List.cons y) (ih ns length)

theorem state_select_reject (yes no : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (yesShape : StateShape yes) (noShape : StateShape no) :
    TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete 0 yes no = no := by
  simp only [TlsChatResponse.stateSelect,TlsChatResponse.headerSelect,TlsInner.select_reject,Word64.select_reject,
    choose_reject_exact yes.modes no.modes (yesShape.modes.trans noShape.modes.symm),
    choose_reject_exact yes.positions no.positions (yesShape.positions.trans noShape.positions.symm),
    choose_reject_exact yes.kinds no.kinds (yesShape.kinds.trans noShape.kinds.symm),
    choose_reject_exact yes.utf no.utf (yesShape.utf.trans noShape.utf.symm),
    word_list_reject yes.stack no.stack (yesShape.stack.trans noShape.stack.symm)]

theorem state_select_accept (yes no : TlsChatResponse.State (BitVec 8) (BitVec 64))
    (yesShape : StateShape yes) (noShape : StateShape no) :
    TlsChatResponse.stateSelect Word64.concrete ByteAuth.concrete 255 yes no = yes := by
  simp only [TlsChatResponse.stateSelect,TlsChatResponse.headerSelect,TlsInner.select_accept,Word64.select_accept,
    choose_accept_exact yes.modes no.modes (yesShape.modes.trans noShape.modes.symm),
    choose_accept_exact yes.positions no.positions (yesShape.positions.trans noShape.positions.symm),
    choose_accept_exact yes.kinds no.kinds (yesShape.kinds.trans noShape.kinds.symm),
    choose_accept_exact yes.utf no.utf (yesShape.utf.trans noShape.utf.symm),
    word_list_accept yes.stack no.stack (yesShape.stack.trans noShape.stack.symm)]

#print axioms state_select_reject
#print axioms state_select_accept
end ChatResponseReference.StreamingV1
