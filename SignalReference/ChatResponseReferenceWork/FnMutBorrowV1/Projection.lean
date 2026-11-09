import Aeneas
open Aeneas Aeneas.Std Result
namespace ChatResponseReference.FnMutBorrowV1
/-- Precisely typed borrowed-triple ABI. It is not a coercion for arbitrary
functions or arbitrary Rust FnMut arguments. -/
structure BorrowFnOnce (S L R C O : Type) where
  call_once : S → (L × R × C) → Result (O × L × R)
structure BorrowFnMut (S L R C O : Type) where
  FnOnceInst : BorrowFnOnce S L R C O
  call_mut : S → (L × R × C) → Result (O × S × L × R)

def toTrait {S L R O : Type} (raw : Result (O × L × R × S)) :
    Result (O × S × L × R) := do
  let (output,left,right,closure) ← raw
  .ok (output,closure,left,right)
def toRaw {S L R O : Type} (observed : Result (O × S × L × R)) :
    Result (O × L × R × S) := do
  let (output,closure,left,right) ← observed
  .ok (output,left,right,closure)
theorem raw_roundtrip {S L R O : Type} (raw : Result (O × L × R × S)) :
    toRaw (toTrait raw) = raw := by
  cases raw with
  | fail error => rfl
  | div => rfl
  | ok value => rcases value with ⟨output,left,right,closure⟩; rfl
theorem trait_roundtrip {S L R O : Type} (observed : Result (O × S × L × R)) :
    toTrait (toRaw observed) = observed := by
  cases observed with
  | fail error => rfl
  | div => rfl
  | ok value => rcases value with ⟨output,closure,left,right⟩; rfl
structure LoanOp (S L R C O : Type) where
  raw : S → (L × R × C) → Result (O × L × R × S)
instance {S L R C O : Type} : CoeFun (LoanOp S L R C O)
    (fun _ => S → (L × R × C) → Result (O × L × R × S)) := ⟨LoanOp.raw⟩
instance {S L R C O : Type} : Coe (LoanOp S L R C O)
    (S → (L × R × C) → Result (O × S × L × R)) :=
  ⟨fun operation closure args => toTrait (operation.raw closure args)⟩
theorem field_exact {S L R C O : Type} (operation : LoanOp S L R C O) (closure : S) (args : L × R × C) :
    toRaw ((operation : S → (L × R × C) → Result (O × S × L × R)) closure args) = operation.raw closure args :=
  raw_roundtrip _
#print axioms raw_roundtrip
#print axioms trait_roundtrip
#print axioms field_exact
end ChatResponseReference.FnMutBorrowV1
