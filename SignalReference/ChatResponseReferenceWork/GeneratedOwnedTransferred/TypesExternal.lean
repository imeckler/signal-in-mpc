import Aeneas
open Aeneas Aeneas.Std
/-- Uninitialized bytes are unused encoding-only metadata in this profile. -/
def bytes.buf.uninit_slice.UninitSlice := List (Option U8)
/-- Actual recursion-budget content, independent of heap/layout. -/
structure prost.encoding.DecodeContext where
  recurse_count : U32
namespace ActualChatResponseOwned_transferred
/-- Scoped Rust String content model. Validity is an explicit successful-merge
invariant established by the executable UTF8 specification, not a type axiom.
Invalid temporary bytes may exist behind the native unsafe mutation guard. -/
abbrev String := Aeneas.Std.alloc.vec.Vec U8
end ActualChatResponseOwned_transferred
