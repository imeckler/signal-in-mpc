import VarintDecodeWork.OffsetReference
import TlsMpc.Signal.SpqrDecodeAt

namespace LibSignalReference.Candidate.VarintDecode
open Aeneas Aeneas.Std TlsMpc
open TlsMpc.Signal TlsMpc.Signal.VarintDecode
open _root_.Std.Tactic.BVDecide

/-- Status, absolute cursor (eight big-endian bytes), and decoded U64.
The failure encoding retains the actual returned cursor. -/
def resultBytesAt (result : core.result.Result U64 _root_.SpqrVarintDecode.Error)
    (cursor : Usize) : List (BitVec 8) :=
  match result with
  | .Ok value => 255 :: (OpenResult.encodeLength ByteAuth.concrete cursor.val ++ Spqr.valueBytes value.bv)
  | .Err _ => 0 :: (OpenResult.encodeLength ByteAuth.concrete cursor.val ++ List.replicate 8 0)

theorem matches_at_bytes (start : Usize) (state : Spqr.State)
    (result : core.result.Result U64 _root_.SpqrVarintDecode.Error) (cursor : Usize)
    (h : MatchesAt start state result cursor) :
    resultBytesAt result cursor = SpqrDecodeAt.resultSpec start.val state := by
  unfold MatchesAt at h
  unfold SpqrDecodeAt.resultSpec
  split at h <;> simp_all [resultBytesAt]

theorem contents_drop (bytes : Slice U8) (start : Usize) :
    contents (bytes.drop start) = (contents bytes).drop start.val := by
  simp [contents, Slice.drop, List.map_drop]

/-- Every actual decoder result, including an invalid initial offset, has the
same 17-byte result encoding as the shared-offset specification. -/
theorem decode_at_bytes_reference (bytes : Slice U8) (start : Usize) :
    ∃ result cursor,
      _root_.SpqrVarintDecode.decode_varint bytes start = .ok (result, cursor) ∧
      MatchesAt start (Spqr.decode (contents (bytes.drop start))) result cursor ∧
      resultBytesAt result cursor = SpqrDecodeAt.spec (contents bytes) start.val := by
  obtain ⟨result, cursor, hd, hm⟩ := decode_at_reference bytes start
  refine ⟨result, cursor, hd, hm, ?_⟩
  rw [matches_at_bytes start _ result cursor hm, contents_drop]
  unfold SpqrDecodeAt.spec
  split
  · rfl
  · rename_i hout
    have hempty : (contents bytes).drop start.val = [] :=
      List.drop_eq_nil_of_le (by omega)
    simp [hempty, Spqr.decode, Spqr.run, SpqrDecodeAt.resultSpec, SpqrDecodeAt.fallback, ByteAuth.concrete]

/-- Usize is at most 64 bits in the unchanged official scalar model. -/
theorem usize_max_lt_uint64 : Usize.max < 2 ^ 64 := by
  rcases Usize.bounds_eq with h | h <;> simp_all [U32.max_eq, U64.max_eq]

/-- Actual pinned SPQR decode_varint at every shared starting offset refines
every numeric AIG output bit. No success, canonicality, or input-byte bound
is assumed beyond the official Slice model. Offset bytes encode the Usize. -/
theorem decode_at_refines_artifact (bytes : Slice U8) (start : Usize)
    (secret offset : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (hinput : secret.map (BVExpr.eval assign) = contents bytes)
    (hoffset : offset.map (BVExpr.eval assign) = OpenResult.encodeLength ByteAuth.concrete start.val) :
    ∃ result cursor,
      _root_.SpqrVarintDecode.decode_varint bytes start = .ok (result, cursor) ∧
      MatchesAt start (Spqr.decode (contents (bytes.drop start))) result cursor ∧
      ∀ (index : Nat) (hi : index < 8 * (SpqrDecodeAt.decodeCore Spqr.symbolic ByteAuth.symbolic secret offset).length),
        AigExport.evalRef
          (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
            (SpqrDecodeAt.decodeCore Spqr.symbolic ByteAuth.symbolic secret offset))).aig)
          (fun varId bit => (assign.get varId).bv.getLsbD bit)
          (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
            (SpqrDecodeAt.decodeCore Spqr.symbolic ByteAuth.symbolic secret offset))).vec.get index hi)) =
          (ByteCircuit.joinValue (resultBytesAt result cursor)).getLsbD index := by
  obtain ⟨result, cursor, hd, hm, hb⟩ := decode_at_bytes_reference bytes start
  have hs : start.val < 2 ^ 64 := by have := usize_max_lt_uint64; scalar_tac
  have hlen : secret.length ≤ 2 ^ 64 := by
    have he := congrArg List.length hinput
    simp only [List.length_map, contents] at he
    have hslice := bytes.property
    have := usize_max_lt_uint64
    omega
  refine ⟨result, cursor, hd, hm, ?_⟩
  intro index hi
  rw [SpqrDecodeAt.compiled_decodeCore_spec secret offset start.val hs hlen assign hoffset,
    hinput, hb]

end LibSignalReference.Candidate.VarintDecode
