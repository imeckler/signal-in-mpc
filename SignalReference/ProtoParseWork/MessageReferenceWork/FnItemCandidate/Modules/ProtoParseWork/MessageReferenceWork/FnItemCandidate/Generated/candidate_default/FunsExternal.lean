import ProtoParseWork.MessageReferenceWork.FnItemCandidate.Generated.candidate_default.Types
open Aeneas Aeneas.Std
namespace FnItemRegression
/-- A zero-input function item is represented by its result. Calling the Rust
FnOnce shim observes that same result. Scoped to this default-u32 item. -/
def P.Insts.CoreOpsFunctionFnOnceTupleU32.call_once (value : Result U32) (_ : Unit) : Result U32 := value
end FnItemRegression
