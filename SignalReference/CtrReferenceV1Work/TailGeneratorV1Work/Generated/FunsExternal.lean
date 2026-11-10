import CtrReferenceV1Work.TailGeneratorV1Work.Generated.Types
import CtrReferenceV1Work.ApplyBlockV1Work.Reference
namespace ActualCtrTail16
open Aeneas Aeneas.Std
-- Pinned core slice IntoIterator body dispatches directly to iter_mut.
def MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter {T : Type} :
 Slice T → Result (core.slice.iter.IterMut T × (core.slice.iter.IterMut T → Slice T)) :=
 core.slice.Slice.iter_mut

def toActual (value : Backend) : ActualApplyBlock16.Backend :=
 ⟨value.counter,value.nonce,value.keys⟩
def fromActual (value : ActualApplyBlock16.Backend) : Backend :=
 ⟨value.counter,value.nonce,value.keys⟩
def Backend.gen_ks_block (self : Backend) (old : Array U8 16#usize) :
 Result (Backend × Array U8 16#usize) := do
 let (next,block) ← ActualApplyBlock16.Backend.gen_ks_block (toActual self) old
 .ok (fromActual next,block)
end ActualCtrTail16
