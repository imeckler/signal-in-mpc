import LibSignalReference.Proofs.Unpad
import TlsMpc.Signal.OpenResult

namespace LibSignalReference.Proofs.OpenResult

open Aeneas Aeneas.Std
open LibSignalReference.Proofs.Unpad
open TlsMpc
open _root_.Std.Tactic.BVDecide

set_option maxHeartbeats 2000000

/-- Mathematical shared-result encoding. The eight-byte length is big-endian;
padding positions remain zero, and every field is zero on either rejection. -/
def encodeResult (authenticated : Bool) (leading : List U8) : Option (List U8) → List (BitVec 8)
  | none => List.replicate (9 + leading.length + 16) 0
  | some tail => if authenticated then
      [255] ++ Signal.OpenResult.encodeLength ByteAuth.concrete (leading.length + tail.length) ++
        leading.map UScalar.bv ++ tail.map UScalar.bv ++ List.replicate (16 - tail.length) 0
    else List.replicate (9 + leading.length + 16) 0

theorem expected16_retained_length (block : List U8) (strict : Bool) (tail : List U8)
    (hs : expected16 block strict = some tail) : tail.length < 16 := by
  unfold expected16 at hs
  dsimp only at hs
  split at hs
  · cases hs
  · rename_i hvalid
    split at hs
    · cases hs
    · have he := congrArg List.length (Option.some.inj hs)
      simp only [List.length_take] at he
      omega

theorem finish_split (o : ByteAuth.Ops B) (authenticated : B) (leading tail : List B)
    (ht : tail.length = 16) :
    Signal.OpenResult.finish o authenticated (leading ++ tail) =
      (let decoded := Signal.Unpad.decode o tail
       let accepted := o.and authenticated (Signal.OpenResult.get o decoded 0)
       accepted :: ByteAuth.release o accepted (Signal.OpenResult.candidatePayload o leading decoded)) := by
  simp [Signal.OpenResult.finish, ht]

theorem encodeResult_reject_auth (leading : List U8) (tail : Option (List U8)) :
    encodeResult false leading tail = List.replicate (9 + leading.length + 16) 0 := by
  cases tail <;> rfl

theorem finish_expected (authenticated : Bool) (leading block : List U8)
    (hblock : block.length = 16) :
    Signal.OpenResult.finish ByteAuth.concrete (if authenticated then 255 else 0)
      (leading.map UScalar.bv ++ block.map UScalar.bv) =
        encodeResult authenticated leading (expected16 block true) := by
  have hsize : 16 ≤ (leading.map UScalar.bv ++ block.map UScalar.bv).length := by
    simp [hblock]
  cases authenticated with
  | false =>
    rw [encodeResult_reject_auth]
    simpa only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_map,
      hblock, Nat.add_assoc] using Signal.OpenResult.finish_reject_auth
        (leading.map UScalar.bv ++ block.map UScalar.bv) hsize
  | true =>
    simp only [↓reduceIte]
    cases hout : expected16 block true with
    | none =>
      change Signal.OpenResult.finish ByteAuth.concrete 255 _ =
        List.replicate (9 + leading.length + 16) 0
      have hbad : Signal.OpenResult.get ByteAuth.concrete
          (Signal.Unpad.decode ByteAuth.concrete
            ((leading.map UScalar.bv ++ block.map UScalar.bv).drop
              ((leading.map UScalar.bv ++ block.map UScalar.bv).length - 16))) 0 = 0 := by
        simp only [List.length_append, List.length_map, hblock, Nat.add_sub_cancel]
        simp [decode_reference block hblock, hout,
          encodeOption, Signal.OpenResult.get]
      simpa only [List.length_append, List.length_map, hblock, Nat.add_assoc] using
        Signal.OpenResult.finish_reject_padding 255 _ hsize hbad
    | some tail =>
      have htail := expected16_retained_length block true tail hout
      rw [finish_split ByteAuth.concrete 255 _ _ (by simpa using hblock),
        decode_reference block hblock, hout]
      simp [encodeOption, Signal.OpenResult.candidatePayload, Signal.OpenResult.get,
        Signal.OpenResult.lengthBytes_value _ _ htail, encodeResult, List.append_assoc]
      constructor
      · rfl
      · exact ByteAuth.release_accept _

/-- Composition with the unchanged actual strict Rust final-block operation.
The leading bytes are unrestricted; a prefix of full CBC blocks is included. -/
theorem finish_reference (authenticated : Bool) (leading : List U8)
    (block : Slice U8) (hblock : block.length = 16) :
    ∃ result, RustCryptoUnpadding.Pkcs7.Insts.Block_paddingPadding.raw_unpad block = .ok result ∧
      Signal.OpenResult.finish ByteAuth.concrete (if authenticated then 255 else 0)
        (leading.map UScalar.bv ++ block.val.map UScalar.bv) =
          encodeResult authenticated leading (forgetResult result) := by
  obtain ⟨result, hr, hv⟩ := WP.spec_imp_exists (raw_unpad_spec16 block hblock)
  refine ⟨result, hr, ?_⟩
  rw [hv]
  exact finish_expected authenticated leading block.val hblock

theorem finish_reference_length (authenticated : Bool) (leading : List U8)
    (block : Slice U8) (hblock : block.length = 16) :
    (Signal.OpenResult.finish ByteAuth.concrete (if authenticated then 255 else 0)
      (leading.map UScalar.bv ++ block.val.map UScalar.bv)).length = 9 + leading.length + 16 := by
  rw [Signal.OpenResult.finish_length _ _ _ (by simp [show block.val.length = 16 from hblock])]
  simp [show block.val.length = 16 from hblock, Nat.add_assoc]

/-- An actual strict-padding rejection zeros status, retained length, and every
candidate byte, for either authentication input. -/
theorem finish_reject_reference (authenticated : Bool) (leading : List U8)
    (block : Slice U8) (hblock : block.length = 16) (failure : RustCryptoUnpadding.Error)
    (rejected : RustCryptoUnpadding.Pkcs7.Insts.Block_paddingPadding.raw_unpad block =
      .ok (.Err failure)) :
    Signal.OpenResult.finish ByteAuth.concrete (if authenticated then 255 else 0)
      (leading.map UScalar.bv ++ block.val.map UScalar.bv) =
        List.replicate (9 + leading.length + 16) 0 := by
  obtain ⟨result, hr, hv⟩ := finish_reference authenticated leading block hblock
  have he : result = .Err failure := Result.ok.inj (hr.symm.trans rejected)
  subst result
  exact hv

/-- Numeric MPC output equals the receive encoding of the actual Rust unpad
result. The authentication mask, retained length and plaintext remain shared. -/
theorem finish_refines_artifact (authenticated : Bool) (leading : List U8)
    (block : Slice U8) (hblock : block.length = 16)
    (secretAuth : BVExpr 8) (secret : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (ha : secretAuth.eval assign = if authenticated then 255 else 0)
    (hs : secret.map (BVExpr.eval assign) = leading.map UScalar.bv ++ block.val.map UScalar.bv) :
    ∃ result, RustCryptoUnpadding.Pkcs7.Insts.Block_paddingPadding.raw_unpad block = .ok result ∧
      ∀ (index : Nat)
        (hi : index < 8 * (Signal.OpenResult.finish ByteAuth.symbolic secretAuth secret).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile
            (ByteCircuit.joinExpr (Signal.OpenResult.finish ByteAuth.symbolic secretAuth secret))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile
            (ByteCircuit.joinExpr (Signal.OpenResult.finish ByteAuth.symbolic secretAuth secret))).vec.get index hi)) =
          (ByteCircuit.joinValue (encodeResult authenticated leading (forgetResult result))).getLsbD index := by
  obtain ⟨result, hr, hv⟩ := finish_reference authenticated leading block hblock
  refine ⟨result, hr, ?_⟩
  intro index hi
  rw [Signal.OpenResult.compiled_finish_correct, ha, hs, hv]

end LibSignalReference.Proofs.OpenResult
