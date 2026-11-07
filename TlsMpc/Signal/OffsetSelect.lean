import TlsMpc.Signal.OpenResult

/-! Shared-offset selection for bounded parser composition. Each row may be
computed from the public suffix starting at its index, so its genuine remaining
length is available at circuit-construction time. Selecting an already decoded
row avoids treating zero padding as a valid varint terminator.

The input offset and selected result remain secret. Input/row counts and result
width are public. This is a linear scan of rows, not an ORAM or a parser by itself. -/

namespace TlsMpc.Signal.OffsetSelect
open Std.Tactic.BVDecide

def normalize (a : ByteAuth.Ops B) (width : Nat) (row : List B) : List B :=
  (List.range width).map (OpenResult.get a row)

def rowAt (rows : List (List B)) (index : Nat) : List B := rows[index]?.getD []

def selectCases (a : ByteAuth.Ops B) (offset : List B) (rows : List (List B)) (fallback : List B) : List Nat → List B
  | [] => fallback
  | index :: rest => Unpad.choose a (ByteAuth.equalMask a offset (OpenResult.encodeLength a index))
      (normalize a fallback.length (rowAt rows index)) (selectCases a offset rows fallback rest)

def selectOr (a : ByteAuth.Ops B) (offset : List B) (rows : List (List B)) (fallback : List B) : List B :=
  selectCases a offset rows fallback (List.range rows.length)

def selectChecked (a : ByteAuth.Ops B) (offset : List B) (rows : List (List B)) (fallback : List B) : Option (List B) :=
  if offset.length = 8 ∧ rows.length ≤ 1024 then some (selectOr a offset rows fallback) else none

theorem normalize_length (a : ByteAuth.Ops B) (width : Nat) (row : List B) :
    (normalize a width row).length = width := by simp [normalize]

theorem selectCases_length (a : ByteAuth.Ops B) (offset : List B) (rows : List (List B))
    (fallback : List B) (indices : List Nat) :
    (selectCases a offset rows fallback indices).length = fallback.length := by
  induction indices with
  | nil => rfl
  | cons index rest ih => simp [selectCases, Unpad.choose, normalize_length, ih]

theorem selectOr_length (a : ByteAuth.Ops B) (offset : List B) (rows : List (List B)) (fallback : List B) :
    (selectOr a offset rows fallback).length = fallback.length := selectCases_length _ _ _ _ _

section Refinement
variable {a : ByteAuth.Ops B} {b : ByteAuth.Ops B'} {f : B → B'} (h : ByteAuth.Hom a b f)
include h

theorem normalize_map (width : Nat) (row : List B) :
    (normalize a width row).map f = normalize b width (row.map f) := by
  simp only [normalize, List.map_map, Function.comp_def, OpenResult.get_map h]

omit h in
theorem rowAt_map (rows : List (List B)) (index : Nat) :
    (rowAt rows index).map f = rowAt (rows.map (List.map f)) index := by
  simp only [rowAt, List.getElem?_map]
  cases rows[index]? <;> rfl

theorem selectCases_map (offset : List B) (rows : List (List B)) (fallback : List B) (indices : List Nat) :
    (selectCases a offset rows fallback indices).map f =
      selectCases b (offset.map f) (rows.map (List.map f)) (fallback.map f) indices := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      simp only [selectCases, Unpad.choose_map h, ByteAuth.equalMask_map h,
        OpenResult.encodeLength_map h, normalize_map h, rowAt_map, ih, List.length_map]

theorem selectOr_map (offset : List B) (rows : List (List B)) (fallback : List B) :
    (selectOr a offset rows fallback).map f =
      selectOr b (offset.map f) (rows.map (List.map f)) (fallback.map f) := by
  simp only [selectOr, selectCases_map h, List.length_map]

theorem selectChecked_map (offset : List B) (rows : List (List B)) (fallback : List B) :
    (selectChecked a offset rows fallback).map (List.map f) =
      selectChecked b (offset.map f) (rows.map (List.map f)) (fallback.map f) := by
  simp only [selectChecked, List.length_map]
  split <;> simp [selectOr_map h]

end Refinement

/-- Pure decoding used only to prove exact public offset-label equality. -/
def readOffset (bytes : List (BitVec 8)) : Nat :=
  bytes.foldl (fun accumulated byte => accumulated * 256 + byte.toNat) 0

theorem encodeLength_roundtrip (index : Nat) (bound : index < 2 ^ 64) :
    readOffset (OpenResult.encodeLength ByteAuth.concrete index) = index := by
  simp [readOffset, OpenResult.encodeLength, List.range_succ, ByteAuth.concrete]
  omega

theorem encodeLength_eq_iff (i j : Nat) (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    OpenResult.encodeLength ByteAuth.concrete i = OpenResult.encodeLength ByteAuth.concrete j ↔ i = j := by
  constructor
  · intro equal
    have values := congrArg readOffset equal
    simpa only [encodeLength_roundtrip i hi, encodeLength_roundtrip j hj] using values
  · intro equal
    rw [equal]

theorem normalize_self (row : List (BitVec 8)) : normalize ByteAuth.concrete row.length row = row := by
  apply List.ext_getElem
  · simp [normalize]
  · intro i hi hj
    simp [normalize, OpenResult.get, hj]

theorem selectCases_nat_spec (start : Nat) (hs : start < 2 ^ 64)
    (rows : List (List (BitVec 8))) (fallback : List (BitVec 8)) (indices : List Nat)
    (bounds : ∀ i ∈ indices, i < 2 ^ 64) :
    selectCases ByteAuth.concrete (OpenResult.encodeLength ByteAuth.concrete start) rows fallback indices =
      if start ∈ indices then normalize ByteAuth.concrete fallback.length (rowAt rows start) else fallback := by
  induction indices with
  | nil => simp [selectCases]
  | cons i rest ih =>
      have hi := bounds i (by simp)
      have hr : ∀ j ∈ rest, j < 2 ^ 64 := by intro j hj; exact bounds j (by simp [hj])
      simp only [selectCases, ByteAuth.equalMask_value, encodeLength_eq_iff start i hs hi]
      by_cases equal : start = i
      · simp only [if_pos equal]
        rw [Unpad.choose_accept _ _ (by simp [normalize_length, selectCases_length])]
        simp [equal]
      · simp only [if_neg equal]
        rw [Unpad.choose_reject _ _ (by simp [normalize_length, selectCases_length]), ih hr]
        simp [equal]

theorem selectOr_nat_spec (start : Nat) (hs : start < 2 ^ 64)
    (rows : List (List (BitVec 8))) (fallback : List (BitVec 8)) (bound : rows.length ≤ 2 ^ 64) :
    selectOr ByteAuth.concrete (OpenResult.encodeLength ByteAuth.concrete start) rows fallback =
      if start < rows.length then normalize ByteAuth.concrete fallback.length (rowAt rows start) else fallback := by
  rw [selectOr, selectCases_nat_spec start hs rows fallback (List.range rows.length)
    (by intro i hi; exact Nat.lt_of_lt_of_le (List.mem_range.mp hi) bound)]
  simp only [List.mem_range]

theorem compiled_selectOr_correct (offset : List (BVExpr 8)) (rows : List (List (BVExpr 8)))
    (fallback : List (BVExpr 8)) (assign : BVExpr.Assignment) (bit : Nat)
    (hi : bit < 8 * (selectOr ByteAuth.symbolic offset rows fallback).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (selectOr ByteAuth.symbolic offset rows fallback))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (selectOr ByteAuth.symbolic offset rows fallback))).vec.get bit hi)) =
      (ByteCircuit.joinValue (selectOr ByteAuth.concrete (offset.map (BVExpr.eval assign))
        (rows.map (List.map (BVExpr.eval assign))) (fallback.map (BVExpr.eval assign)))).getLsbD bit := by
  rw [ByteCircuit.compile_bytes_correct, selectOr_map (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.OffsetSelect
