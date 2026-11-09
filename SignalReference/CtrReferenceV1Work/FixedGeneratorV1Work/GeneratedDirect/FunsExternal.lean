-- AUTHORED linkage to actual pinned counter/AES bodies, not assumed primitives.
import CtrReferenceV1Work.FixedGeneratorV1Work.GeneratedDirect.Types
import CtrReferenceV1Work.StateCircuitAgreement
import AesCtrBlockWork.EncryptBoundV1.Funs
namespace FixedCtrGenerator
open Aeneas Aeneas.Std
open LibSignalReference.Candidate.CtrState

def aes256_encrypt : Array U64 120#usize → Array (Array U8 16#usize) 4#usize →
 Result (Array (Array U8 16#usize) 4#usize) :=
 RustCryptoAesCtrBlock.soft.fixslice.aes256_encrypt

def toActual (state : Nonce) : LibSignalReference.Candidate.CtrState.Nonce :=
 {ctr:=state.ctr,nonce:=state.nonce}
def fromActual (state : LibSignalReference.Candidate.CtrState.Nonce) : Nonce :=
 {ctr:=state.ctr,nonce:=state.nonce}
def next_block (state : Nonce) : Result (Array U8 16#usize × Nonce) := do
 let (block,next) ← CtrStateV1.next (toActual state)
 .ok (block,fromActual next)
end FixedCtrGenerator
