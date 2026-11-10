-- AUTHORED actual counter/AES links, no supplied primitive result.
import CtrReferenceV1Work.ParallelGeneratorV1Work.GeneratedValue.Types
import CtrReferenceV1Work.StateCircuitAgreement
import AesCtrBlockWork.EncryptBoundV1.Funs
namespace ActualParallelCtr4
open Aeneas Aeneas.Std

def aes256_encrypt : Array U64 120#usize → Array (Array U8 16#usize) 4#usize →
 Result (Array (Array U8 16#usize) 4#usize) :=
 RustCryptoAesCtrBlock.soft.fixslice.aes256_encrypt

def toActual (state : Nonce) : LibSignalReference.Candidate.CtrState.Nonce :=
 ⟨state.ctr,state.nonce⟩
def fromActual (state : LibSignalReference.Candidate.CtrState.Nonce) : Nonce :=
 ⟨state.ctr,state.nonce⟩
def next_block (state : Nonce) : Result (Array U8 16#usize × Nonce) := do
 let (block,next) ← CtrStateV1.next (toActual state)
 .ok (block,fromActual next)
end ActualParallelCtr4
