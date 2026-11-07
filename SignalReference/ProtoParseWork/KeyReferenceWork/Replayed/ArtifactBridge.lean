import ProtoParseWork.KeyReferenceWork.Replayed.WrapperReference

namespace LibSignalReference.Candidate.ProstKeyVarint
open Aeneas Aeneas.Std TlsMpc TlsMpc.Signal TlsMpc.Signal.VarintDecode
open LibSignalReference.Candidate.ProstKeySlice
open _root_.Std.Tactic.BVDecide
set_option maxHeartbeats 200000

/-- Normalized status255 || consumedBE8 || valueBE8. On any error all 17 bytes
are zero. Consumption on success is measured from the actual mutable Buf suffix. -/
def wrapperBytes (before after : Slice U8)
    (result : core.result.Result U64 ProstKeyCandidate.error.DecodeError) : List (BitVec 8) :=
  match result with
  | .Ok value => 255 :: (Word64.bytes Word64.concrete (BitVec.ofNat 64 (before.length-after.length)) ++
      Word64.bytes Word64.concrete value.bv)
  | .Err _ => List.replicate 17 0

theorem post_bytes (bytes remaining : Slice U8)
    (result : core.result.Result U64 ProstKeyCandidate.error.DecodeError)
    (h : PrefixPost bytes result remaining) :
    prefixBytes Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes) =
      wrapperBytes bytes remaining result := by
  cases result with
  | Ok value =>
      obtain ⟨count,hc,_,hp,hr⟩ := h
      have hcount : bytes.length-remaining.length = count := by rw [hr,drop_length]; omega
      unfold prefixBytes
      rw [hp]
      simp only [wrapperBytes,hcount]
      exact congrArg (List.cons 255) (ByteAuth.release_accept _)
  | Err error =>
      have hz := h.2
      simp only [prefixBytes,decodedBytes,hz,ByteAuth.release_reject,List.length_append,
        Word64.bytes_length,wrapperBytes]
      rfl

theorem decode_bytes_reference (bytes : Slice U8) :
    ∃ result remaining,
      ProstKeyCandidate.encoding.varint.decode_varint sliceBuf bytes = .ok (result,remaining) ∧
      PrefixPost bytes result remaining ∧
      prefixBytes Spqr.concrete Word64.concrete ByteAuth.concrete (contents bytes) =
        wrapperBytes bytes remaining result := by
  obtain ⟨result,remaining,hd,hp⟩ := decode_reference bytes
  exact ⟨result,remaining,hd,hp,post_bytes bytes remaining result hp⟩

/-- Kernel-checked bitwise refinement of the unchanged actual full Prost
wrapper instantiated with the explicitly modeled contiguous &[u8] Buf.
Unlike the leaf slice endpoint, this theorem needs no nonempty/last-byte promise. -/
theorem decode_refines_artifact (bytes : Slice U8)
    (secret : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (hinput : secret.map (BVExpr.eval assign) = contents bytes) :
    ∃ result remaining,
      ProstKeyCandidate.encoding.varint.decode_varint sliceBuf bytes = .ok (result,remaining) ∧
      PrefixPost bytes result remaining ∧
      ∀ (index : Nat) (hi : index < 8*(prefixBytes Spqr.symbolic Word64.symbolic ByteAuth.symbolic secret).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
            (prefixBytes Spqr.symbolic Word64.symbolic ByteAuth.symbolic secret))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
            (prefixBytes Spqr.symbolic Word64.symbolic ByteAuth.symbolic secret))).vec.get index hi)) =
          (ByteCircuit.joinValue (wrapperBytes bytes remaining result)).getLsbD index := by
  obtain ⟨result,remaining,hd,hp,hb⟩ := decode_bytes_reference bytes
  refine ⟨result,remaining,hd,hp,?_⟩
  intro index hi
  rw [ByteCircuit.compile_bytes_correct,prefixBytes_map (Spqr.evaluationHom assign)
    (Word64.evaluationHom assign) (ByteAuth.evaluationHom assign),hinput,hb]

#print axioms post_bytes
#print axioms decode_bytes_reference
#print axioms decode_refines_artifact
end LibSignalReference.Candidate.ProstKeyVarint
