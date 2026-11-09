-- TRUSTED narrow source-grounded getter model: original debug_assert!(false) graph fails translation.
-- Valid caller invariant is derived by actual setter/reset proofs, not supplied crypto validity.
import CtrReferenceV1Work.ReadBufferV1Work.GeneratedOpaqueAttr.Types
namespace ActualReadBuffer16
open Aeneas Aeneas.Std

def ReadBuffer.get_pos (self : ReadBuffer) : Result Usize := do
 let pos ← Array.index_usize self.buffer 0#usize
 massert (pos != 0#u8)
 massert (pos <= 16#u8)
 lift (UScalar.cast .Usize pos)
end ActualReadBuffer16
