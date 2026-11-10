import CtrReferenceV1Work.BlocksCallbackV1Work.GeneratedGetSelected.Funs
namespace LibSignalReference.Candidate.BlocksCallback4
open Aeneas Aeneas.Std
open TlsMpc.Signal.AesLayout TlsMpc.Signal.AesLinear
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def backend (keys : Nat → Words (BitVec 64)) (counter : U32) : ActualBlocksCallbackGet4.Backend :=
 ⟨counter,(CtrState.zeroNonce counter).nonce,AesKeyRanges.keyArray keys⟩

theorem parallel_roundtrip (value : ActualBlocksCallbackGet4.Backend) :
 ActualBlocksCallbackGet4.fromParallel (ActualBlocksCallbackGet4.toParallel value) = value := rfl

theorem single_roundtrip (value : ActualBlocksCallbackGet4.Backend) :
 ActualBlocksCallbackGet4.fromSingle (ActualBlocksCallbackGet4.toSingle value) = value := rfl

theorem tail_roundtrip (value : ActualBlocksCallbackGet4.Backend) :
 ActualBlocksCallbackGet4.fromTail (ActualBlocksCallbackGet4.toTail value) = value := rfl
end LibSignalReference.Candidate.BlocksCallback4
