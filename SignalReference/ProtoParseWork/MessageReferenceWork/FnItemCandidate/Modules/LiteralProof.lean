import ProtoParseWork.MessageReferenceWork.FnItemCandidate.Generated.candidate_literal.Funs
open Aeneas Aeneas.Std
namespace FnItemLiteralProof

theorem actual_literal_item : FnItemRegression.literal_item = .ok 7#u32 := rfl

theorem actual_seven : FnItemRegression.seven = .ok 7#u32 := rfl

#print axioms actual_literal_item
#print axioms actual_seven
end FnItemLiteralProof
