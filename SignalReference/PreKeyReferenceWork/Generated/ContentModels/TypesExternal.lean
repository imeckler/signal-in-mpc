import Aeneas
open Aeneas Aeneas.Std
/-! Explicit external models, not Aeneas translations. NonZero is represented
by its inner value. DeviceId's additional <=127 source invariant is a caller
precondition. The error carrier projects only the InvalidArgument variant
reachable from this pure constructor; arbitrary protocol errors are out of scope. -/
@[rust_type "core::num::niche_types::NonZeroU8Inner"]
def core.num.niche_types.NonZeroU8Inner := { n : Std.U8 // n.val ≠ 0 }
@[rust_type "core::num::nonzero::NonZero"]
def core.num.nonzero.NonZero (_T : Type) (Inner : Type) := Inner
inductive error.SignalProtocolError where
  | InvalidArgument : String → SignalProtocolError
  deriving DecidableEq
