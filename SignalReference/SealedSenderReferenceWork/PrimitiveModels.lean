import SealedSenderReferenceWork.Generated.EncryptWrapper.Types
import TlsMpc.Signal.SealedSenderV1

/-! EXPLICIT TRUST BOUNDARY. These two executable slots interpret actual opaque
Rust primitive calls in the unchanged generated wrapper. Agreement of the
excluded AES-CTR/HMAC Rust bodies with these models is NOT established here.
The intended SSv1 domain is message<=8192, cipher key32, MAC key32; behavior
outside that source-refinement domain is not claimed. No validity flag is an
input to either model. Official Aeneas Slice/Vec/Array models remain in use. -/
namespace SealedSenderReference
open Aeneas Aeneas.Std
open TlsMpc

def bytes (source : Slice U8) : List (BitVec 8) := source.val.map UScalar.bv

def byteScalars (source : List (BitVec 8)) : List U8 := source.map (fun x => ⟨x⟩)

theorem ctrLoop_length (expanded : List (BitVec 8)) (he : expanded.length=16*(14+1))
    (count index : Nat) (plain : List (BitVec 8)) (hp : plain.length≤16*count) :
    (Signal.SealedSenderV1.ctrLoop Aes.concrete expanded count index plain).length=plain.length := by
  induction count generalizing index plain with
  | zero => simp only [Signal.SealedSenderV1.ctrLoop,List.length_nil];omega
  | succ count ih =>
    simp only [Signal.SealedSenderV1.ctrLoop,List.length_append,List.length_zipWith,List.length_take,List.length_drop,
      Aes.encryptExpanded_length Aes.concrete 14 expanded _ he,ih (index+1) (plain.drop 16) (by simp only [List.length_drop];omega)]
    omega

theorem ctr_length (key plain : List (BitVec 8)) (hk : key.length=32) :
    (Signal.SealedSenderV1.ctr Aes.concrete key plain).length=plain.length := by
  unfold Signal.SealedSenderV1.ctr
  apply ctrLoop_length _ (Aes.expandKey_length Aes.concrete 8 14 key hk (by decide))
  omega

def crypto.aes_256_ctr_encrypt (msg key : Slice U8) :
    Result (core.result.Result (alloc.vec.Vec U8) crypto.EncryptionError) :=
  if hkey : key.length=32 then
    let encrypted := byteScalars (Signal.SealedSenderV1.ctr Aes.concrete (bytes key) (bytes msg))
    .ok (.Ok ⟨encrypted,by
      have hkeyBytes : (bytes key).length=32 := by simpa only [bytes,List.length_map] using hkey
      have length : encrypted.length=msg.length := by
        simp only [encrypted,byteScalars,List.length_map]
        rw [ctr_length (bytes key) (bytes msg) hkeyBytes]
        simp only [bytes,List.length_map]
      rw [length]
      exact msg.property⟩)
  else .ok (.Err .BadKeyOrIv)

def crypto.hmac_sha256 (key msg : Slice U8) : Result (Array U8 32#usize) :=
  .ok (Array.make 32#usize (byteScalars (Sha256.hmac Sha256.concrete (bytes key) (bytes msg)))
    (by simp [byteScalars,Sha256.hmac_length]))

end SealedSenderReference
