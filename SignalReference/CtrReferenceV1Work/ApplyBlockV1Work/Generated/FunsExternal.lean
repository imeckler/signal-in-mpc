-- AUTHORED dispatch/layout adapters. Both slots call proved actual-source implementations.
import CtrReferenceV1Work.ApplyBlockV1Work.Generated.Types
import CtrReferenceV1Work.FixedGeneratorV1Work.GeneratorReference
import CtrReferenceV1Work.XorContentV1Work.LoopReference
namespace ActualApplyBlock16
open Aeneas Aeneas.Std

def toBackend (state : Backend) : FixedCtrGenerator.CtrBackend :=
 ⟨⟨state.counter,state.nonce⟩,⟨state.keys⟩⟩
def fromBackend (state : FixedCtrGenerator.CtrBackend) : Backend :=
 ⟨state.ctr_nonce.ctr,state.ctr_nonce.nonce,state.backend.keys⟩
def toInOut (state : InOut) : ActualXorContent16.InOut := ⟨state.input,state.output⟩
def fromInOut (state : ActualXorContent16.InOut) : InOut := ⟨state.input,state.output⟩

def Backend.gen_ks_block (self : Backend) (block : Array U8 16#usize) :
 Result (Backend × Array U8 16#usize) := do
 let (updated,back,output) ← FixedCtrGenerator.CtrBackend.gen_ks_block (toBackend self) block
 .ok (fromBackend (back updated),output)

def InOut.xor_in2out (self : InOut) (data : Array U8 16#usize) : Result (InOut × (InOut → InOut)) := do
 let (updated,back) ← ActualXorContent16.InOut.xor_in2out (toInOut self) data
 .ok (fromInOut updated,fun value => fromInOut (back (toInOut value)))
end ActualApplyBlock16
