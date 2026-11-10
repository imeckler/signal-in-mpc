import CtrReferenceV1Work.BlocksCallbackV1Work.GeneratedGetSelected.Types
import CtrReferenceV1Work.ParallelCallbackV1Work.Reference
import CtrReferenceV1Work.TailGeneratorV1Work.Reference
namespace ActualBlocksCallbackGet4
open Aeneas Aeneas.Std

def MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter {T : Type} :
 Slice T → Result (core.slice.iter.IterMut T × (core.slice.iter.IterMut T → Slice T)) :=
 core.slice.Slice.iter_mut

def toParallel (value : Backend) : ActualParallelCallback4.Backend := ⟨value.counter,value.nonce,value.keys⟩
def fromParallel (value : ActualParallelCallback4.Backend) : Backend := ⟨value.counter,value.nonce,value.keys⟩
def toSingle (value : Backend) : ActualApplyBlock16.Backend := ⟨value.counter,value.nonce,value.keys⟩
def fromSingle (value : ActualApplyBlock16.Backend) : Backend := ⟨value.counter,value.nonce,value.keys⟩
def toTail (value : Backend) : ActualCtrTail16.Backend := ⟨value.counter,value.nonce,value.keys⟩
def fromTail (value : ActualCtrTail16.Backend) : Backend := ⟨value.counter,value.nonce,value.keys⟩

def Backend.gen_ks_block (self : Backend) (old : Array U8 16#usize) :
 Result (Backend × Array U8 16#usize) := do
 let (next,output) ← ActualApplyBlock16.Backend.gen_ks_block (toSingle self) old
 .ok (fromSingle next,output)

def Backend.gen_par_ks_blocks (self : Backend) (old : Array (Array U8 16#usize) 4#usize) :
 Result (Backend × Array (Array U8 16#usize) 4#usize) := do
 let (next,output) ← ActualParallelCallback4.Backend.gen_par_ks_blocks (toParallel self) old
 .ok (fromParallel next,output)

def Backend.gen_tail_blocks (self : Backend) (old : Slice (Array U8 16#usize)) :
 Result (Backend × Slice (Array U8 16#usize)) := do
 let (next,output) ← ActualCtrTail16.Backend.gen_tail_blocks (toTail self) old
 .ok (fromTail next,output)

def InOutArrayU816.xor_in2out (self : InOut (Array U8 16#usize)) (data : Array U8 16#usize) :
 Result (InOut (Array U8 16#usize)) := do
 let (next,back) ← ActualXorContent16.InOut.xor_in2out ⟨self.input,self.output⟩ data
 let owner := back next
 .ok ⟨owner.input,owner.output⟩

def InOutArrayArrayU8164.xor_in2out (self : InOut (Array (Array U8 16#usize) 4#usize))
 (data : Array (Array U8 16#usize) 4#usize) : Result (InOut (Array (Array U8 16#usize) 4#usize)) := do
 let (next,back) ← ActualParallelCallback4.InOut.xor_in2out ⟨self.input,self.output⟩ data
 let owner := back next
 .ok ⟨owner.input,owner.output⟩

-- Scoped tail indexing/owner-return content binding. Both source borrow
-- continuations are retained; bounds/error comes from official Slice index.
def Tail.get (self : Tail) (i : Usize) :
 Result (InOut (Array U8 16#usize) × (InOut (Array U8 16#usize) → Tail) × (Tail → Tail)) := do
 let (item,back) ← Slice.index_mut_usize self.elements i
 .ok (item,fun fresh=>⟨back fresh⟩,fun owner=>owner)
end ActualBlocksCallbackGet4
