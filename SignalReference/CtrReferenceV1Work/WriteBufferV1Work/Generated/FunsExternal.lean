import CtrReferenceV1Work.WriteBufferV1Work.Generated.Types
open Aeneas Aeneas.Std
-- Fixed ResetGuard owner-return binding. Rust forget skips Drop and ends the
-- guard's exclusive borrow; this returns the unchanged underlying content owner.
-- Not a generic extracted mem::forget/Drop/erasure theorem.
namespace ActualWriteBuffer16
def core.mem.forget (guard : ActualWriteBuffer16.ReadBuffer) :
 Result ActualWriteBuffer16.ReadBuffer := .ok guard
end ActualWriteBuffer16

namespace ActualWriteBuffer16
-- Scoped function-trait borrow signatures: a mutable block argument returns
-- its updated owner, a shared slice argument does not. No callback value assumed.
class CallbackContent (Args : Type) where
  Return : Type → Type
instance {α : Type} {n : Aeneas.Std.Usize} : CallbackContent (Aeneas.Std.Array α n) :=
 ⟨fun Out => Out × Aeneas.Std.Array α n⟩
instance : CallbackContent (Aeneas.Std.Slice Aeneas.Std.U8) := ⟨fun Out => Out⟩
structure core.ops.function.FnOnce (Self Args Output : Type) [CallbackContent Args] where
 call_once : Self → Args → Result (CallbackContent.Return (Args:=Args) Output)
structure core.ops.drop.Drop (Self : Type) where
 drop : Self → Result (Self × (Self → Self))
end ActualWriteBuffer16
