import ChatResponseReferenceWork.FnMutBorrowV1.Replayed.Funs
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.FnMutBorrowV1
theorem actual_reference (left right : U32) :
    _root_.FnMutBorrowV1.actual left right = .ok (42#u32,7#u32,9#u32) := rfl
#print axioms actual_reference
end ChatResponseReference.FnMutBorrowV1
namespace ChatResponseReference.FnMutBorrowV1
/-- Arbitrary functions acquire no implicit return permutation. -/
example {S L R C O : Type}
    (raw : S → (L × R × C) → Result (O × L × R × S)) : True := by
  fail_if_success have converted : S → (L × R × C) → Result (O × S × L × R) := raw
  trivial
end ChatResponseReference.FnMutBorrowV1
