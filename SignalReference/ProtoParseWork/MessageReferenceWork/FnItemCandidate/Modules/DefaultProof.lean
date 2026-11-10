import ProtoParseWork.MessageReferenceWork.FnItemCandidate.Generated.candidate_default.Funs
open Aeneas Aeneas.Std
namespace FnItemLiftProof

def liftPure (value : U32) : Result U32 := .ok value

theorem call_lift (value : U32) :
    FnItemRegression.P.Insts.CoreOpsFunctionFnOnceTupleU32.call_once (liftPure value) () = .ok value := rfl

theorem actual_default_item : FnItemRegression.default_item = .ok 0#u32 := rfl

theorem call_result (result : Result U32) :
    FnItemRegression.apply FnItemRegression.P.Insts.CoreOpsFunctionFnOnceTupleU32 result = result := rfl

#print axioms call_lift
#print axioms actual_default_item
#print axioms call_result
end FnItemLiftProof
