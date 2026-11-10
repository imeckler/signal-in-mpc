import CtrReferenceV1Work.ApplyBlockV1Work.Generated.Funs
import CtrReferenceV1Work.FixedGeneratorV1Work.Circuit
namespace LibSignalReference.Candidate.ApplyBlock16
open Aeneas Aeneas.Std TlsMpc
open LibSignalReference.Candidate
open LibSignalReference.Candidate.FixedDispatch
open LibSignalReference.Candidate.FixsliceCircuitV1
open TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def backend (keys : Nat → Words (BitVec 64)) (counter : U32) : ActualApplyBlock16.Backend :=
 ⟨counter,(FixedCtr.zeroNonce counter).nonce,AesKeyRanges.keyArray keys⟩

theorem backend_roundtrip (state : ActualApplyBlock16.Backend) :
 ActualApplyBlock16.fromBackend (ActualApplyBlock16.toBackend state) = state := rfl

theorem inout_roundtrip (state : ActualApplyBlock16.InOut) :
 ActualApplyBlock16.fromInOut (ActualApplyBlock16.toInOut state) = state := rfl

theorem actual_generator (keys : Nat → Words (BitVec 64)) (counter : U32)
 (old : Array U8 16#usize) :
 ActualApplyBlock16.Backend.gen_ks_block (backend keys counter) old =
 .ok (backend keys (FixedCtr.successor counter),FixedCtr.streamBlock keys counter) := by
 unfold ActualApplyBlock16.Backend.gen_ks_block
 change (do
   let (updated,back,output) ← FixedCtrGenerator.CtrBackend.gen_ks_block ⟨FixedCtr.zeroNonce counter,⟨AesKeyRanges.keyArray keys⟩⟩ old
   .ok (ActualApplyBlock16.fromBackend (back updated),output)) = _
 rw [FixedCtr.generator_actual]
 simp only [uncurry_apply_pair,bind_tc_ok]
 rfl

theorem actual_xor (input data : Nat → BitVec 8) (old : Array U8 16#usize) :
 ActualApplyBlock16.InOut.xor_in2out ⟨blockOf input,old⟩ (blockOf data) =
 .ok (⟨blockOf input,blockOf (fun i => input i ^^^ data i)⟩,
       fun value => ⟨blockOf input,value.output⟩) := by
 unfold ActualApplyBlock16.InOut.xor_in2out
 change (do
   let (updated,back) ← ActualXorContent16.InOut.xor_in2out ⟨blockOf input,old⟩ (blockOf data)
   .ok (ActualApplyBlock16.fromInOut updated, fun value => ActualApplyBlock16.fromInOut (back (ActualApplyBlock16.toInOut value)))) = _
 rw [XorContent16.source_xor]
 simp only [uncurry_apply_pair,bind_tc_ok]
 rfl

theorem actual_apply (keys : Nat → Words (BitVec 64)) (counter : U32)
 (input : Nat → BitVec 8) (old : Array U8 16#usize) :
 ActualApplyBlock16.ApplyBlockCtx.call ⟨⟨blockOf input,old⟩⟩ (backend keys counter) =
 .ok (⟨⟨blockOf input,
  blockOf (fun i => input i ^^^
   encrypted keys (embed (FixedCtr.blockBytes (CtrState.expected counter))) 0 i)⟩⟩,
  backend keys (FixedCtr.successor counter)) := by
 simp only [ActualApplyBlock16.ApplyBlockCtx.call,
  LibSignalReference.Candidate.XorContent16.default_block input input,bind_tc_ok]
 rw [actual_generator]
 simp only [uncurry_apply_pair,bind_tc_ok,FixedCtr.streamBlock]
 rw [actual_xor]
 simp only [uncurry_apply_pair,bind_tc_ok]

end LibSignalReference.Candidate.ApplyBlock16
