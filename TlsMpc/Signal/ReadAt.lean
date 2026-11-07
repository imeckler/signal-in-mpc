import TlsMpc.Signal.OffsetSelect

/-! Fixed-width reads at a shared cursor. Public width and buffer capacity are
the only host indices. The shared output is status || cursorBE8 || data; an
out-of-bounds read keeps the cursor and zeros the data. -/
namespace TlsMpc.Signal.ReadAt
open Std.Tactic.BVDecide

def fallback (a : ByteAuth.Ops B) (width : Nat) (offset : List B) : List B :=
  a.const 0 :: (offset ++ List.replicate width (a.const 0))

def row (a : ByteAuth.Ops B) (width start : Nat) (bytes : List B) : List B :=
  a.const 255 :: (OpenResult.encodeLength a (start + width) ++ (bytes.drop start).take width)

def rows (a : ByteAuth.Ops B) (width : Nat) (bytes : List B) : List (List B) :=
  (List.range (if width ≤ bytes.length then bytes.length - width + 1 else 0)).map
    (fun start => row a width start bytes)

def readCore (a : ByteAuth.Ops B) (width : Nat) (bytes offset : List B) : List B :=
  OffsetSelect.selectOr a offset (rows a width bytes) (fallback a width offset)

theorem fallback_length (a : ByteAuth.Ops B) (width : Nat) (offset : List B) :
    (fallback a width offset).length = 1 + offset.length + width := by simp [fallback]; omega

theorem readCore_length (a : ByteAuth.Ops B) (width : Nat) (bytes offset : List B) :
    (readCore a width bytes offset).length = 1 + offset.length + width := by
  simp [readCore, OffsetSelect.selectOr_length, fallback_length]

section Refinement
variable {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a a' f)
include ha

theorem fallback_map (width : Nat) (offset : List B) :
    (fallback a width offset).map f = fallback a' width (offset.map f) := by
  simp [fallback, ha.const]

theorem row_map (width start : Nat) (bytes : List B) :
    (row a width start bytes).map f = row a' width start (bytes.map f) := by
  simp [row, ha.const, OpenResult.encodeLength_map ha, List.map_take, List.map_drop]

theorem rows_map (width : Nat) (bytes : List B) :
    (rows a width bytes).map (List.map f) = rows a' width (bytes.map f) := by
  simp only [rows, List.length_map, List.map_map, Function.comp_def, row_map ha]

theorem readCore_map (width : Nat) (bytes offset : List B) :
    (readCore a width bytes offset).map f = readCore a' width (bytes.map f) (offset.map f) := by
  simp only [readCore, OffsetSelect.selectOr_map ha, rows_map ha, fallback_map ha]
end Refinement

def spec (width : Nat) (bytes : List (BitVec 8)) (start : Nat) : List (BitVec 8) :=
  if start + width ≤ bytes.length then row ByteAuth.concrete width start bytes
  else fallback ByteAuth.concrete width (OpenResult.encodeLength ByteAuth.concrete start)

theorem readCore_spec (width : Nat) (bytes : List (BitVec 8)) (start : Nat)
    (hs : start < 2 ^ 64) (hb : bytes.length < 2 ^ 64) :
    readCore ByteAuth.concrete width bytes (OpenResult.encodeLength ByteAuth.concrete start) =
      spec width bytes start := by
  have hr : (rows ByteAuth.concrete width bytes).length ≤ 2 ^ 64 := by
    simp only [rows, List.length_map, List.length_range]
    split <;> omega
  rw [readCore, OffsetSelect.selectOr_nat_spec start hs _ _ hr]
  simp only [rows, List.length_map, List.length_range]
  by_cases fits : start + width ≤ bytes.length
  · have hw : width ≤ bytes.length := by omega
    have hi : start < bytes.length - width + 1 := by omega
    simp only [if_pos hw, if_pos hi, OffsetSelect.rowAt, List.getElem?_map,
      List.getElem?_range hi, Option.map_some, Option.getD_some, fallback_length,
      OpenResult.encodeLength_length, spec, if_pos fits]
    have hl : (row ByteAuth.concrete width start bytes).length = 1 + 8 + width := by
      simp [row, OpenResult.encodeLength_length]; omega
    rw [← hl, OffsetSelect.normalize_self]
  · have hbad : ¬start < (if width ≤ bytes.length then bytes.length - width + 1 else 0) := by
      split <;> omega
    simp only [if_neg hbad, spec, if_neg fits]

theorem compiled_readCore_correct (width : Nat) (bytes offset : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (readCore ByteAuth.symbolic width bytes offset).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (readCore ByteAuth.symbolic width bytes offset))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (readCore ByteAuth.symbolic width bytes offset))).vec.get index hi)) =
      (ByteCircuit.joinValue (readCore ByteAuth.concrete width
        (bytes.map (BVExpr.eval assign)) (offset.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, readCore_map (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.ReadAt
