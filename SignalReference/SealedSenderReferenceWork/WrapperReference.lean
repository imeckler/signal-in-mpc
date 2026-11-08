import SealedSenderReferenceWork.Generated.EncryptWrapper.Funs

namespace SealedSenderReference
open Aeneas Aeneas.Std
set_option maxHeartbeats 1000000

theorem clone_bytes (source : Slice U8) :
    Slice.clone core.clone.CloneU8.clone source = .ok source := by
  obtain ⟨after, ha, he⟩ := WP.spec_imp_exists
    (Slice.clone_spec (s := source) (clone := core.clone.CloneU8.clone) (by intros; rfl))
  simpa only [← he] using ha

theorem extend_bytes (buf : alloc.vec.Vec U8) (source : Slice U8)
    (h : buf.length + source.length ≤ Usize.max) :
    ∃ after, alloc.vec.Vec.extend_from_slice core.clone.CloneU8 buf source = .ok after ∧
      after.val = buf.val ++ source.val := by
  refine ⟨⟨buf.val ++ source.val, by simpa using h⟩, ?_, rfl⟩
  have hc : Slice.clone (liftFun1 core.clone.impls.CloneU8.clone) source = .ok source := clone_bytes source
  simp only [alloc.vec.Vec.extend_from_slice,dif_pos h]
  split
  · rename_i copied he
    have eq : copied=source := Result.ok.inj (he.symm.trans hc)
    subst copied; rfl
  · rename_i error he; cases he.symm.trans hc
  · rename_i he; cases he.symm.trans hc

theorem wrong_cipher_key (msg key mac : Slice U8) (hk : key.length≠32) :
    crypto.aes256_ctr_hmacsha256_encrypt msg key mac = .ok (.Err .BadKeyOrIv) := by
  simp [crypto.aes256_ctr_hmacsha256_encrypt,crypto.aes_256_ctr_encrypt,hk,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

/-- Actual unchanged Rust wrapper control flow, relative to its two explicit
primitive model slots. No primitive-body agreement is assumed by a validity bit. -/
theorem wrapper_composition (msg key mac : Slice U8) (encrypted : alloc.vec.Vec U8)
    (digest : Array U8 32#usize)
    (hc : crypto.aes_256_ctr_encrypt msg key = .ok (.Ok encrypted))
    (hm : crypto.hmac_sha256 mac (alloc.vec.Vec.deref encrypted) = .ok digest)
    (hsize : encrypted.length+10≤Usize.max) :
    ∃ after, crypto.aes256_ctr_hmacsha256_encrypt msg key mac = .ok (.Ok after) ∧
      after.val = encrypted.val ++ digest.val.take 10 := by
  have hindex : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice U8)) digest {«end» := 10#usize} =
      .ok (⟨digest.val.take 10, by have := digest.property; simp at this ⊢; omega⟩ : Slice U8) := by
    simp [core.slice.index.SliceIndexRangeToUsizeSlice.index,Array.to_slice,
      Slice.length,List.slice,digest.property]
  let macSlice : Slice U8 := ⟨digest.val.take 10, by have := digest.property; simp at this ⊢; omega⟩
  have hp : macSlice.length=10 := by simp [macSlice,Slice.length,digest.property]
  obtain ⟨after,ha,hval⟩ := extend_bytes encrypted macSlice (by simpa only [hp] using hsize)
  refine ⟨after,?_,hval⟩
  simp only [crypto.aes256_ctr_hmacsha256_encrypt,hc,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch,hm,hindex]
  change (do
    let v ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 encrypted macSlice
    pure (core.result.Result.Ok v)) = .ok (.Ok after)
  rw [ha]
  rfl

/-- The generated wrapper produces exactly the circuit symmetric-envelope model,
under the explicit executable primitive interpretation (not Rust primitive-body
agreement). Official allocation/panic bounds are discharged by the stated bound. -/
theorem wrapper_matches_symmetric_model (msg key mac : Slice U8)
    (hk : key.length=32) (hsize : msg.length+10≤Usize.max) :
    ∃ after, crypto.aes256_ctr_hmacsha256_encrypt msg key mac = .ok (.Ok after) ∧
      after.val.map UScalar.bv = TlsMpc.Signal.SealedSenderV1.encrypt
        TlsMpc.Aes.concrete TlsMpc.Sha256.concrete (bytes key) (bytes mac) (bytes msg) := by
  have hkBytes : (bytes key).length=32 := by simpa only [bytes,List.length_map] using hk
  let ciphertext := TlsMpc.Signal.SealedSenderV1.ctr TlsMpc.Aes.concrete (bytes key) (bytes msg)
  have hlen : (byteScalars ciphertext).length=msg.length := by
    simp only [byteScalars,List.length_map,ciphertext,ctr_length (bytes key) (bytes msg) hkBytes]
    simp only [bytes,List.length_map]
  let encrypted : alloc.vec.Vec U8 := ⟨byteScalars ciphertext,by rw [hlen];exact msg.property⟩
  let digest := Array.make 32#usize (byteScalars (TlsMpc.Sha256.hmac
    TlsMpc.Sha256.concrete (bytes mac) ciphertext)) (by simp [byteScalars,TlsMpc.Sha256.hmac_length])
  have hc : crypto.aes_256_ctr_encrypt msg key = .ok (.Ok encrypted) := by
    simp only [crypto.aes_256_ctr_encrypt,dif_pos hk];rfl
  have hm : crypto.hmac_sha256 mac (alloc.vec.Vec.deref encrypted) = .ok digest := by
    simp [crypto.hmac_sha256,digest,bytes,alloc.vec.Vec.deref,encrypted,byteScalars,List.map_map]
  obtain ⟨after,ha,hval⟩ := wrapper_composition msg key mac encrypted digest hc hm
    (by simpa only [encrypted,alloc.vec.Vec.length,hlen] using hsize)
  refine ⟨after,ha,?_⟩
  rw [hval]
  simp [encrypted,digest,byteScalars,Array.make,List.map_map,List.map_take,
    TlsMpc.Signal.SealedSenderV1.encrypt,ciphertext]

end SealedSenderReference
