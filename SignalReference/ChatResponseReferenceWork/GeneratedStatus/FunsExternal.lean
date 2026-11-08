import ChatResponseReferenceWork.GeneratedStatus.Types
namespace ActualChatResponseStatus
open Aeneas Aeneas.Std

def U16.Insts.CoreConvertTryFromU32TryFromIntError.try_from (value : U32) :
    Result (core.result.Result U16 core.num.error.TryFromIntError) :=
  Aeneas.Std.core.num.tryFromUScalar .U16 value

def core.num.niche_types.NonZeroU16Inner.Insts.CoreCloneClone.clone
    (value : _root_.core.num.niche_types.NonZeroU16Inner) : Result _root_.core.num.niche_types.NonZeroU16Inner := .ok value

/-- Only the extracted U16 instantiation is modeled. Other instantiations fail
at the model boundary instead of asserting arbitrary primitive correctness. -/
noncomputable def core.num.nonzero.NonZero.new
    {T Inner : Type} (_ : core.num.nonzero.ZeroablePrimitive T Inner) (value : T) :
    Result (Option (_root_.core.num.nonzero.NonZero T Inner)) := by
  classical
  exact if h : T = U16 then
    if h.mp value = 0#u16 then .ok none else .ok (some value)
  else .fail .panic

def core.num.nonzero.NonZero.get {T Inner : Type}
    (_ : core.num.nonzero.ZeroablePrimitive T Inner)
    (value : _root_.core.num.nonzero.NonZero T Inner) : Result T := .ok value

def core.ops.range.Range.contains {Idx U : Type}
    (_ : core.cmp.PartialOrd Idx Idx)
    (left : core.cmp.PartialOrd Idx U) (right : core.cmp.PartialOrd U Idx)
    (range : core.ops.range.Range Idx) (value : U) : Result Bool := do
  let lower ← left.le range.start value
  if lower then right.lt value range.end else .ok false

def core.result.Result.map_err {T E F O : Type}
    (f : core.ops.function.FnOnce O E F) (value : core.result.Result T E) (closure : O) :
    Result (core.result.Result T F) := do
  match value with
  | .Ok result => .ok (.Ok result)
  | .Err error => let converted ← f.call_once closure error; .ok (.Err converted)
end ActualChatResponseStatus
