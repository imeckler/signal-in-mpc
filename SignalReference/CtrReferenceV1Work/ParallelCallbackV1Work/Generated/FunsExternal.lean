import CtrReferenceV1Work.ParallelCallbackV1Work.Generated.Types
import CtrReferenceV1Work.ParallelGeneratorV1Work.Reference
import CtrReferenceV1Work.ParallelXorV1Work.Reference
namespace ActualParallelCallback4
open Aeneas Aeneas.Std

def toBackend (value : Backend) : ActualParallelCtr4.CtrBackend :=
 ⟨⟨value.counter,value.nonce⟩,⟨value.keys⟩⟩
def fromBackend (value : ActualParallelCtr4.CtrBackend) : Backend :=
 ⟨value.ctr_nonce.ctr,value.ctr_nonce.nonce,value.backend.keys⟩
def toInOut (value : InOut) : ActualParallelXor4.InOut := ⟨value.input,value.output⟩
def fromInOut (value : ActualParallelXor4.InOut) : InOut := ⟨value.input,value.output⟩

def Backend.gen_par_ks_blocks (self : Backend) (old : Array (Array U8 16#usize) 4#usize) :
 Result (Backend × Array (Array U8 16#usize) 4#usize) := do
 let (next,output) ← ActualParallelCtr4.CtrBackend.gen_par_ks_blocks (toBackend self) old
 .ok (fromBackend next,output)

def InOut.xor_in2out (self : InOut) (data : Array (Array U8 16#usize) 4#usize) :
 Result (InOut × (InOut → InOut)) := do
 let (updated,back) ← ActualParallelXor4.InOut.xor_in2out (toInOut self) data
 .ok (fromInOut updated,fun value=>fromInOut (back (toInOut value)))
end ActualParallelCallback4
