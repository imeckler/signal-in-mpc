import AesInverseCircuitWork.PaddingBridge

namespace LibSignalReference.Proofs.OpenResult

open Aeneas Aeneas.Std
open LibSignalReference.Proofs.Unpad
open TlsMpc

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- Mathematical big-endian decoding, used only in the lossless encoding proof. -/
def readLength (bytes : List (BitVec 8)) : Nat :=
  bytes.foldl (fun accumulated byte => accumulated * 256 + byte.toNat) 0

theorem encodeLength_roundtrip (length : Nat) (hbound : length < 2 ^ 64) :
    readLength (Signal.OpenResult.encodeLength ByteAuth.concrete length) = length := by
  simp [readLength, Signal.OpenResult.encodeLength, List.range_succ, ByteAuth.concrete]
  omega

theorem encodeResult_length_prefix (leading tail : List U8) :
    ((encodeResult true leading (some tail)).drop 1).take 8 =
      Signal.OpenResult.encodeLength ByteAuth.concrete (leading.length + tail.length) := by
  simp [encodeResult, Signal.OpenResult.encodeLength_length]

theorem encodeResult_retained_length (leading tail : List U8)
    (hbound : leading.length + tail.length < 2 ^ 64) :
    readLength (((encodeResult true leading (some tail)).drop 1).take 8) =
      leading.length + tail.length := by
  rw [encodeResult_length_prefix, encodeLength_roundtrip _ hbound]

theorem actual_retained_length_bound (block tail : Slice U8) (hblock : block.length = 16)
    (accepted : RustCryptoUnpadding.Pkcs7.Insts.Block_paddingPadding.raw_unpad block =
      .ok (.Ok tail)) : tail.length < 16 := by
  obtain ⟨result, hr, hv⟩ := WP.spec_imp_exists (raw_unpad_spec16 block hblock)
  have he : result = .Ok tail := Result.ok.inj (hr.symm.trans accepted)
  subst result
  exact expected16_retained_length block.val true tail.val hv.symm

/-- Accepted receive output carries the actual retained length losslessly in
eight secret bytes. The public whole-candidate bound rules out UInt64 wrap. -/
theorem finish_retained_length (leading : List U8) (block tail : Slice U8)
    (hblock : block.length = 16) (hbound : leading.length + 16 < 2 ^ 64)
    (accepted : RustCryptoUnpadding.Pkcs7.Insts.Block_paddingPadding.raw_unpad block =
      .ok (.Ok tail)) :
    readLength ((Signal.OpenResult.finish ByteAuth.concrete 255
      (leading.map UScalar.bv ++ block.val.map UScalar.bv)).drop 1 |>.take 8) =
        leading.length + tail.length := by
  obtain ⟨result, hr, hv⟩ := finish_reference true leading block hblock
  have he : result = .Ok tail := Result.ok.inj (hr.symm.trans accepted)
  subst result
  have ht := actual_retained_length_bound block tail hblock accepted
  have hb : leading.length + tail.val.length < 2 ^ 64 := by
    change leading.length + tail.length < 2 ^ 64
    omega
  exact (congrArg (fun bytes : List (BitVec 8) => readLength ((bytes.drop 1).take 8)) hv).trans
    (encodeResult_retained_length leading tail.val hb)

end LibSignalReference.Proofs.OpenResult
