import TlsMpc.Signal.SpqrParse

/-! Pure public-index semantics for the shared-cursor SPQR parser. These
theorems remove the circuit's scans and cursor muxes from its specification;
the numerical cursor follows successful decodes/reads and stays on failure. -/
namespace TlsMpc.Signal.SpqrParse
open Std.Tactic.BVDecide
open VarintDecode

theorem cursor_prefix (tag : BitVec 8) (offset data : List (BitVec 8)) (hlen : offset.length = 8) :
    cursor ByteAuth.concrete (tag :: (offset ++ data)) = offset := by
  apply List.ext_getElem
  · simp [cursor, OffsetSelect.normalize_length, hlen]
  · intro i hi hj
    simp only [cursor, List.drop_succ_cons, List.drop_zero, OffsetSelect.normalize,
      List.getElem_map, List.getElem_range, OpenResult.get]
    rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj, Option.getD_some]

def decodeEnd (wire : List (BitVec 8)) (start : Nat) : Nat :=
  if start < wire.length then
    let decoded := Spqr.decode (wire.drop start)
    if decoded.done then start + decoded.index else start
  else start

def readEnd (width : Nat) (wire : List (BitVec 8)) (start : Nat) : Nat :=
  if start + width ≤ wire.length then start + width else start

theorem decodeEnd_bound (wire : List (BitVec 8)) (start : Nat) :
    decodeEnd wire start ≤ max wire.length start := by
  unfold decodeEnd
  split
  · dsimp only
    split
    · have hb := (Spqr.run_index_bounds (wire.drop start) (min 10 (wire.drop start).length) 0 0 false).2
      change start + (Spqr.run (wire.drop start) (min 10 (wire.drop start).length) 0 0 false).index ≤ _
      simp only [List.length_drop] at hb ⊢
      omega
    · omega
  · omega

theorem readEnd_bound (width : Nat) (wire : List (BitVec 8)) (start : Nat) :
    readEnd width wire start ≤ max wire.length start := by
  unfold readEnd
  split <;> omega

theorem cursor_decode_spec (wire : List (BitVec 8)) (start : Nat) :
    cursor ByteAuth.concrete (SpqrDecodeAt.spec wire start) =
      OpenResult.encodeLength ByteAuth.concrete (decodeEnd wire start) := by
  simp only [SpqrDecodeAt.spec, decodeEnd]
  split
  · simp only [SpqrDecodeAt.resultSpec]
    split <;> exact cursor_prefix _ _ _ (OpenResult.encodeLength_length _ _)
  · exact cursor_prefix _ _ _ (OpenResult.encodeLength_length _ _)

theorem cursor_read_spec (width : Nat) (wire : List (BitVec 8)) (start : Nat) :
    cursor ByteAuth.concrete (ReadAt.spec width wire start) =
      OpenResult.encodeLength ByteAuth.concrete (readEnd width wire start) := by
  simp only [ReadAt.spec, readEnd]
  split <;> exact cursor_prefix _ _ _ (OpenResult.encodeLength_length _ _)

def stagesSpec (wire : List (BitVec 8)) : Stages (BitVec 8) :=
  let afterEpoch := decodeEnd wire 1
  let afterIndex := decodeEnd wire afterEpoch
  let afterKind := readEnd 1 wire afterIndex
  let afterChunk := decodeEnd wire afterKind
  ⟨SpqrDecodeAt.spec wire 1, SpqrDecodeAt.spec wire afterEpoch,
    ReadAt.spec 1 wire afterIndex, SpqrDecodeAt.spec wire afterKind,
    ReadAt.spec 32 wire afterChunk⟩

theorem stages_spec (wire : List (BitVec 8)) (bound : wire.length < 2 ^ 64) :
    stages Spqr.concrete ByteAuth.concrete wire = stagesSpec wire := by
  have b1 : decodeEnd wire 1 < 2 ^ 64 := by
    have := decodeEnd_bound wire 1; omega
  have b2 : decodeEnd wire (decodeEnd wire 1) < 2 ^ 64 := by
    have := decodeEnd_bound wire (decodeEnd wire 1); omega
  have b3 : readEnd 1 wire (decodeEnd wire (decodeEnd wire 1)) < 2 ^ 64 := by
    have := readEnd_bound 1 wire (decodeEnd wire (decodeEnd wire 1)); omega
  have b4 : decodeEnd wire (readEnd 1 wire (decodeEnd wire (decodeEnd wire 1))) < 2 ^ 64 := by
    have := decodeEnd_bound wire (readEnd 1 wire (decodeEnd wire (decodeEnd wire 1))); omega
  dsimp only [stages, stagesSpec]
  rw [SpqrDecodeAt.decodeCore_spec wire 1 (by decide) (by omega), cursor_decode_spec,
    SpqrDecodeAt.decodeCore_spec wire _ b1 (by omega), cursor_decode_spec,
    ReadAt.readCore_spec 1 wire _ b2 bound, cursor_read_spec,
    SpqrDecodeAt.decodeCore_spec wire _ b3 (by omega), cursor_decode_spec,
    ReadAt.readCore_spec 32 wire _ b4 bound]

/-- Ordinary branch-based parser result, with Nat cursors and genuine suffix
lengths. It admits extra trailing bytes, and only requests a chunk for the
five chunk-bearing kinds; the other two kinds ignore chunk-stage rejection. -/
def parserSpec (wire : List (BitVec 8)) : List (BitVec 8) :=
  let state := stagesSpec wire
  if accepted wire state then 255 :: payload ByteAuth.concrete state else List.replicate 49 0

theorem parseCore_parserSpec (wire : List (BitVec 8)) (bound : wire.length < 2 ^ 64) :
    parseCore Spqr.concrete ByteAuth.concrete wire = parserSpec wire := by
  rw [parseCore_spec]
  simp only [spec, parserSpec, stages_spec wire bound]

theorem compiled_parseCore_parserSpec (wire : List (BVExpr 8)) (bound : wire.length < 2 ^ 64)
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (parseCore Spqr.symbolic ByteAuth.symbolic wire).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (parseCore Spqr.symbolic ByteAuth.symbolic wire))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (parseCore Spqr.symbolic ByteAuth.symbolic wire))).vec.get index hi)) =
      (ByteCircuit.joinValue (parserSpec (wire.map (BVExpr.eval assign)))).getLsbD index := by
  rw [compiled_parseCore_correct, parseCore_parserSpec _ (by simpa using bound)]

end TlsMpc.Signal.SpqrParse
