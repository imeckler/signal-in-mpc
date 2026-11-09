import ChatResponseReferenceWork.InnerResponseV1.ScalarSource
import ChatResponseReferenceWork.InnerResponseV1.StringBridge
import ChatResponseReferenceWork.InnerResponseV1.BytesBridge
import ChatResponseReferenceWork.InnerResponseV1.SkipBridge
import ChatResponseReferenceWork.InnerResponseV1.Callbacks
open Aeneas Aeneas.Std Result
namespace ActualInnerResponseV1
abbrev P.Insts.CoreOpsFunctionFnOnceTupleU64.call_once (value : Result U64) (_ : Unit) := value
abbrev P.Insts.CoreOpsFunctionFnOnceTupleU32.call_once (value : Result U32) (_ : Unit) := value
abbrev P.Insts.CoreOpsFunctionFnOnceTupleString.call_once (value : Result String) (_ : Unit) := value
abbrev P.Insts.CoreOpsFunctionFnOnceTupleBytes.call_once (value : Result bytes.bytes.Bytes) (_ : Unit) := value
def alloc.string.String.Insts.CoreDefaultDefault.default : Result String := .ok (alloc.vec.Vec.new U8)
def core.option.Option.get_or_insert_with {T F : Type} (inst : core.ops.function.FnOnce F Unit T)
    (old : Option T) (make : F) : Result (T × (T → Option T)) :=
  match old with
  | some value => .ok (value,some)
  | none => do let value ← inst.call_once make (); .ok (value,some)
def core.result.Result.map_err {T E F C : Type} (inst : core.ops.function.FnOnce C E F)
    (value : core.result.Result T E) (closure : C) : Result (core.result.Result T F) :=
  match value with
  | .Ok value => .ok (.Ok value)
  | .Err error => do let mapped ← inst.call_once closure error; .ok (.Err mapped)

end ActualInnerResponseV1
