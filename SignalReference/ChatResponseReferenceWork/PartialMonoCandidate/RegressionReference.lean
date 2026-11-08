import ChatResponseReferenceWork.PartialMonoCandidate.Generated.Funs
open Aeneas Aeneas.Std Result
namespace PartialMonoRegression
/-- Actual generated closed-dictionary specialization preserves both the
remaining operation's result/failure and the exact borrowed buffer. -/
theorem entry_reference {B : Type} (inst : Buf B) (input : B) :
    entry inst input = (do let n ← inst.remaining input; .ok (n,input)) := by
  unfold entry merge.partial_Fun_5
    Value.Insts.Borrow_clause_regressionAdapter.replace_with
    Buf.partial_TraitDecl_4.Blanket Buf.partial_TraitDecl_3.Blanket
    Buf.partial_TraitDecl_4.Blanket.remaining Buf.partial_TraitDecl_3.Blanket.remaining
  dsimp only
  cases h : inst.remaining input <;> rfl
#print axioms entry_reference
end PartialMonoRegression
