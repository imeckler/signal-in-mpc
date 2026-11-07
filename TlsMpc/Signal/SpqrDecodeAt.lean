import TlsMpc.Signal.OffsetSelect
import TlsMpc.Signal.VarintDecode.Spqr

/-! Shared-offset parser composition. A result is computed for each genuine
public suffix, then selected using the secret eight-byte offset. Offset update
uses the decoder's secret consumed count; errors retain the original offset.
All output bytes, including status and offset, remain shared.

This composes the separately proved prefix circuit. The actual-Rust bridge
preserving an arbitrary starting offset is tracked in SignalReference; this
module does not itself claim a full protobuf parser. -/

namespace TlsMpc.Signal.SpqrDecodeAt
open Std.Tactic.BVDecide
open VarintDecode

def resultRow (a : ByteAuth.Ops B) (start : Nat) (decoded : List B) : List B :=
  OpenResult.get a decoded 0 ::
    (OpenResult.lengthCases a start (OpenResult.get a decoded 1) (List.range 11) ++
      OffsetSelect.normalize a 8 (decoded.drop 2))

def fallback (a : ByteAuth.Ops B) (offset : List B) : List B :=
  a.const 0 :: (offset ++ List.replicate 8 (a.const 0))

def rows (a : ByteAuth.Ops B) (decode : List B → List B) (bytes : List B) : List (List B) :=
  (List.range bytes.length).map (fun start => resultRow a start (decode (bytes.drop start)))

def decodeWith (a : ByteAuth.Ops B) (decode : List B → List B) (bytes offset : List B) : List B :=
  OffsetSelect.selectOr a offset (rows a decode bytes) (fallback a offset)

theorem resultRow_length (a : ByteAuth.Ops B) (start : Nat) (decoded : List B) :
    (resultRow a start decoded).length = 17 := by
  simp [resultRow, OpenResult.lengthCases_length, OffsetSelect.normalize_length]

theorem fallback_length (a : ByteAuth.Ops B) (offset : List B) :
    (fallback a offset).length = 9 + offset.length := by simp [fallback]; omega

theorem decodeWith_length (a : ByteAuth.Ops B) (decode : List B → List B) (bytes offset : List B) :
    (decodeWith a decode bytes offset).length = 9 + offset.length := by
  simp [decodeWith, OffsetSelect.selectOr_length, fallback_length]

section Refinement
variable {a : ByteAuth.Ops B} {b : ByteAuth.Ops B'} {f : B → B'} (h : ByteAuth.Hom a b f)
include h

theorem resultRow_map (start : Nat) (decoded : List B) :
    (resultRow a start decoded).map f = resultRow b start (decoded.map f) := by
  simp only [resultRow, List.map_cons, List.map_append, OpenResult.get_map h,
    OpenResult.lengthCases_map h, OffsetSelect.normalize_map h, List.map_drop]

theorem fallback_map (offset : List B) :
    (fallback a offset).map f = fallback b (offset.map f) := by
  simp only [fallback, List.map_cons, List.map_append, List.map_replicate, h.const]

theorem rows_map (decode : List B → List B) (decode' : List B' → List B')
    (hd : ∀ bytes, (decode bytes).map f = decode' (bytes.map f)) (bytes : List B) :
    (rows a decode bytes).map (List.map f) = rows b decode' (bytes.map f) := by
  simp only [rows, List.map_map, Function.comp_def, resultRow_map h, hd, List.map_drop, List.length_map]

theorem decodeWith_map (decode : List B → List B) (decode' : List B' → List B')
    (hd : ∀ bytes, (decode bytes).map f = decode' (bytes.map f)) (bytes offset : List B) :
    (decodeWith a decode bytes offset).map f = decodeWith b decode' (bytes.map f) (offset.map f) := by
  simp only [decodeWith, OffsetSelect.selectOr_map h, rows_map h decode decode' hd, fallback_map h]

end Refinement

theorem byteLabel_eq_iff (i j : Nat) (hi : i < 256) (hj : j < 256) :
    (BitVec.ofNat 8 i = BitVec.ofNat 8 j) ↔ i = j := by
  constructor
  · intro equal
    have values := congrArg BitVec.toNat equal
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using values
  · intro equal
    rw [equal]

theorem lengthCases_nat_spec (start count : Nat) (hc : count < 256) (counts : List Nat)
    (bounds : ∀ n ∈ counts, n < 256) :
    OpenResult.lengthCases ByteAuth.concrete start (BitVec.ofNat 8 count) counts =
      if count ∈ counts then OpenResult.encodeLength ByteAuth.concrete (start + count) else List.replicate 8 0 := by
  induction counts with
  | nil => rfl
  | cons n rest ih =>
      have hn := bounds n (by simp)
      have hr : ∀ j ∈ rest, j < 256 := by intro j hj; exact bounds j (by simp [hj])
      simp only [OpenResult.lengthCases, ByteAuth.eqMask_value]
      change Unpad.choose ByteAuth.concrete (if BitVec.ofNat 8 count = BitVec.ofNat 8 n then 255 else 0) _ _ = _
      simp only [byteLabel_eq_iff count n hc hn]
      by_cases equal : count = n
      · simp only [if_pos equal]
        rw [Unpad.choose_accept _ _ (by simp [OpenResult.encodeLength_length, OpenResult.lengthCases_length])]
        simp [equal]
      · simp only [if_neg equal]
        rw [Unpad.choose_reject _ _ (by simp [OpenResult.encodeLength_length, OpenResult.lengthCases_length]), ih hr]
        simp [equal]

def resultSpec (start : Nat) (state : Spqr.State) : List (BitVec 8) :=
  if state.done then 255 :: (OpenResult.encodeLength ByteAuth.concrete (start + state.index) ++ Spqr.valueBytes state.value)
  else 0 :: (OpenResult.encodeLength ByteAuth.concrete start ++ List.replicate 8 0)

theorem resultRow_encoded (start : Nat) (state : Spqr.State) (bound : state.index ≤ 10) :
    resultRow ByteAuth.concrete start (Spqr.encodeResult state) = resultSpec start state := by
  have hc : state.index < 256 := by omega
  have counts : ∀ n ∈ List.range 11, n < 256 := by intro n hn; have := List.mem_range.mp hn; omega
  cases hd : state.done
  · simp only [Spqr.encodeResult, hd, Bool.false_eq_true, if_false, resultSpec]
    simp only [resultRow, OpenResult.get, List.getElem?_replicate, Nat.reduceLT, if_true,
      Option.getD_some, List.drop_replicate]
    change 0 :: (OpenResult.lengthCases ByteAuth.concrete start (BitVec.ofNat 8 0) (List.range 11) ++
      OffsetSelect.normalize ByteAuth.concrete 8 (List.replicate 8 0)) = _
    rw [lengthCases_nat_spec start 0 (by omega) (List.range 11) counts]
    simp only [List.mem_range, Nat.reduceLT, if_true, Nat.add_zero]
    rw [show OffsetSelect.normalize ByteAuth.concrete 8 (List.replicate 8 0) = List.replicate 8 0 from
      OffsetSelect.normalize_self _]
  · simp only [Spqr.encodeResult, hd, if_true, resultSpec, resultRow,
      OpenResult.get, List.getElem?_cons_zero, Option.getD_some, List.getElem?_cons_succ,
      List.drop_succ_cons, List.drop_zero]
    rw [lengthCases_nat_spec start state.index hc (List.range 11) counts]
    simp only [List.mem_range, show state.index < 11 by omega, if_true]
    have hl : (Spqr.valueBytes state.value).length = 8 := by simp [Spqr.valueBytes]
    have normalized : OffsetSelect.normalize ByteAuth.concrete 8 (Spqr.valueBytes state.value) = Spqr.valueBytes state.value := by
      simpa only [hl] using OffsetSelect.normalize_self (Spqr.valueBytes state.value)
    rw [normalized]

theorem decodeWith_nat_spec (decode : List (BitVec 8) → List (BitVec 8))
    (bytes : List (BitVec 8)) (start : Nat) (hs : start < 2 ^ 64) (bound : bytes.length ≤ 2 ^ 64) :
    decodeWith ByteAuth.concrete decode bytes (OpenResult.encodeLength ByteAuth.concrete start) =
      if start < bytes.length then resultRow ByteAuth.concrete start (decode (bytes.drop start))
      else fallback ByteAuth.concrete (OpenResult.encodeLength ByteAuth.concrete start) := by
  rw [decodeWith, OffsetSelect.selectOr_nat_spec start hs _ _ (by simpa [rows] using bound)]
  simp only [rows, List.length_map, List.length_range]
  split
  · rename_i good
    simp only [OffsetSelect.rowAt, List.getElem?_map, List.getElem?_range good,
      Option.map_some, Option.getD_some, fallback_length, OpenResult.encodeLength_length]
    have hl := resultRow_length ByteAuth.concrete start (decode (bytes.drop start))
    rw [show 9 + 8 = (resultRow ByteAuth.concrete start (decode (bytes.drop start))).length by omega,
      OffsetSelect.normalize_self]
  · rfl

def decodeCore (o : Spqr.Ops B W) (a : ByteAuth.Ops B) (bytes offset : List B) : List B :=
  decodeWith a (Spqr.decodeCore o a) bytes offset

def decodeChecked (o : Spqr.Ops B W) (a : ByteAuth.Ops B) (bytes offset : List B) : Option (List B) :=
  if bytes.length ≤ 1024 ∧ offset.length = 8 then some (decodeCore o a bytes offset) else none

theorem decodeCore_map {o : Spqr.Ops B W} {o' : Spqr.Ops B' W'}
    {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}
    (ho : Spqr.Hom o o' f fw) (ha : ByteAuth.Hom a a' f) (bytes offset : List B) :
    (decodeCore o a bytes offset).map f = decodeCore o' a' (bytes.map f) (offset.map f) := by
  exact decodeWith_map ha _ _ (Spqr.decodeCore_map ho ha) bytes offset

theorem decodeChecked_map {o : Spqr.Ops B W} {o' : Spqr.Ops B' W'}
    {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} {fw : W → W'}
    (ho : Spqr.Hom o o' f fw) (ha : ByteAuth.Hom a a' f) (bytes offset : List B) :
    (decodeChecked o a bytes offset).map (List.map f) = decodeChecked o' a' (bytes.map f) (offset.map f) := by
  simp only [decodeChecked, List.length_map]
  split <;> simp [decodeCore_map ho ha]

theorem decodeCore_length (o : Spqr.Ops B W) (a : ByteAuth.Ops B) (bytes offset : List B) :
    (decodeCore o a bytes offset).length = 9 + offset.length := decodeWith_length _ _ _ _

def spec (bytes : List (BitVec 8)) (start : Nat) : List (BitVec 8) :=
  if start < bytes.length then resultSpec start (Spqr.decode (bytes.drop start))
  else fallback ByteAuth.concrete (OpenResult.encodeLength ByteAuth.concrete start)

theorem decodeCore_spec (bytes : List (BitVec 8)) (start : Nat) (hs : start < 2 ^ 64)
    (bound : bytes.length ≤ 2 ^ 64) :
    decodeCore Spqr.concrete ByteAuth.concrete bytes (OpenResult.encodeLength ByteAuth.concrete start) = spec bytes start := by
  rw [decodeCore, decodeWith_nat_spec _ bytes start hs bound]
  unfold spec
  split
  · rw [Spqr.decodeCore_spec, resultRow_encoded]
    have hb := (Spqr.run_index_bounds (bytes.drop start) (min 10 (bytes.drop start).length) 0 0 false).2
    change (Spqr.run (bytes.drop start) (min 10 (bytes.drop start).length) 0 0 false).index ≤ 10
    omega
  · rfl

theorem compiled_decodeCore_correct (bytes offset : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (bit : Nat) (hi : bit < 8 * (decodeCore Spqr.symbolic ByteAuth.symbolic bytes offset).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (decodeCore Spqr.symbolic ByteAuth.symbolic bytes offset))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (decodeCore Spqr.symbolic ByteAuth.symbolic bytes offset))).vec.get bit hi)) =
      (ByteCircuit.joinValue (decodeCore Spqr.concrete ByteAuth.concrete
        (bytes.map (BVExpr.eval assign)) (offset.map (BVExpr.eval assign)))).getLsbD bit := by
  rw [ByteCircuit.compile_bytes_correct,
    decodeCore_map (Spqr.evaluationHom assign) (ByteAuth.evaluationHom assign)]

theorem compiled_decodeCore_spec (bytes offset : List (BVExpr 8)) (start : Nat) (hs : start < 2 ^ 64)
    (bound : bytes.length ≤ 2 ^ 64) (assign : BVExpr.Assignment)
    (offsetValue : offset.map (BVExpr.eval assign) = OpenResult.encodeLength ByteAuth.concrete start)
    (bit : Nat) (hi : bit < 8 * (decodeCore Spqr.symbolic ByteAuth.symbolic bytes offset).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (decodeCore Spqr.symbolic ByteAuth.symbolic bytes offset))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (decodeCore Spqr.symbolic ByteAuth.symbolic bytes offset))).vec.get bit hi)) =
      (ByteCircuit.joinValue (spec (bytes.map (BVExpr.eval assign)) start)).getLsbD bit := by
  rw [compiled_decodeCore_correct, offsetValue, decodeCore_spec _ start hs (by simpa using bound)]

end TlsMpc.Signal.SpqrDecodeAt
