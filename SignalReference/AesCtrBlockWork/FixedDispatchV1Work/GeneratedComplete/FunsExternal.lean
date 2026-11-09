-- AUTHORED actual AES entry linkage; no assumed cipher implementation.
import AesCtrBlockWork.FixedDispatchV1Work.GeneratedComplete.Types
import AesCtrBlockWork.EncryptBoundV1.Funs
namespace FixedAesDispatch
open Aeneas Aeneas.Std

def aes256_encrypt :
 Array U64 120#usize → Array (Array U8 16#usize) 4#usize →
 Result (Array (Array U8 16#usize) 4#usize) :=
 RustCryptoAesCtrBlock.soft.fixslice.aes256_encrypt
end FixedAesDispatch
