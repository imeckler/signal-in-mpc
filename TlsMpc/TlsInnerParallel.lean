import TlsMpc.TlsInner

/-! Balanced TLSInnerPlaintext scan. Public splitting replaces the sequential
secret suffix scan; no secret changes control flow or output policy. -/
namespace TlsMpc.TlsInnerParallel
open TlsInner
open Std.Tactic.BVDecide

def merge (o : ByteAuth.Ops B) (left right : Scan B) (bytes : List B) : Scan B :=
  ⟨select o right.found right.found left.found,
   select o right.found right.kind left.kind,
   select o right.found right.high left.high,
   select o right.found right.low left.low,
   select o right.found right.nonempty left.nonempty,
   List.zipWith (fun byte old => select o right.found byte old) bytes left.content ++ right.content⟩

def masked (s : Scan (BitVec 8)) : Prop :=
  s.found &&& s.kind = s.kind ∧ s.found &&& s.high = s.high ∧
  s.found &&& s.low = s.low ∧ s.found &&& s.nonempty = s.nonempty

private theorem select_compose (a b c x y : BitVec 8) :
    select ByteAuth.concrete b y (select ByteAuth.concrete a x c) =
    select ByteAuth.concrete (select ByteAuth.concrete b b a)
      (select ByteAuth.concrete b y x) c := by
  simp only [select, ByteAuth.concrete]
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;>
    cases x.getLsbD i <;> cases y.getLsbD i <;> rfl

private theorem found_assoc (a b c : BitVec 8) :
    select ByteAuth.concrete b b (select ByteAuth.concrete a a c) =
    select ByteAuth.concrete (select ByteAuth.concrete b b a)
      (select ByteAuth.concrete b b a) c := by
  simp only [select, ByteAuth.concrete]
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

private theorem content_merge (a b x : BitVec 8) :
    select ByteAuth.concrete b x (a &&& x) =
    (select ByteAuth.concrete b b a) &&& x := by
  simp only [select, ByteAuth.concrete]
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases x.getLsbD i <;> rfl

private theorem masked_step (found value nz byte : BitVec 8)
    (h : found &&& value = value) :
    (select ByteAuth.concrete found found nz) &&&
      (select ByteAuth.concrete found value (nz &&& byte)) =
      select ByteAuth.concrete found value (nz &&& byte) := by
  simp only [select, ByteAuth.concrete] at *
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  have hb := congrArg (fun (v : BitVec 8) => v.getLsbD i) h
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and] at *
  cases found.getLsbD i <;> cases value.getLsbD i <;>
    cases nz.getLsbD i <;> cases byte.getLsbD i <;> simp_all

theorem scan_masked (offset : Nat) (bytes : List (BitVec 8)) :
    masked (scan ByteAuth.concrete offset bytes) := by
  induction bytes generalizing offset with
  | nil => simp [scan, emptyScan, masked, ByteAuth.concrete]
  | cons byte rest ih =>
      obtain ⟨hk, hh, hl, hn⟩ := ih (offset + 1)
      exact ⟨masked_step _ _ _ _ hk, masked_step _ _ _ _ hh,
        masked_step _ _ _ _ hl, masked_step _ _ _ _ hn⟩

theorem merge_step (offset : Nat) (byte : BitVec 8)
    (left right : Scan (BitVec 8)) (bytes : List (BitVec 8)) :
    merge ByteAuth.concrete (scanStep ByteAuth.concrete offset byte left) right (byte :: bytes) =
    scanStep ByteAuth.concrete offset byte (merge ByteAuth.concrete left right bytes) := by
  simp only [merge, scanStep, List.zipWith_cons_cons, List.cons_append]
  congr 1
  · exact found_assoc _ _ _
  · exact select_compose _ _ _ _ _
  · exact select_compose _ _ _ _ _
  · exact select_compose _ _ _ _ _
  · exact select_compose _ _ _ _ _
  · congr 1
    exact content_merge _ _ _

theorem merge_empty (right : Scan (BitVec 8)) (h : masked right) :
    merge ByteAuth.concrete (emptyScan ByteAuth.concrete) right [] = right := by
  rcases right with ⟨found, kind, high, low, nonempty, content⟩
  obtain ⟨hk, hh, hl, hn⟩ := h
  simp only [merge, emptyScan, List.zipWith_nil_left, List.nil_append]
  simp [select, ByteAuth.concrete, hk, hh, hl, hn]

theorem scan_append (offset : Nat) (left right : List (BitVec 8)) :
    merge ByteAuth.concrete (scan ByteAuth.concrete offset left)
      (scan ByteAuth.concrete (offset + left.length) right) left =
    scan ByteAuth.concrete offset (left ++ right) := by
  induction left generalizing offset with
  | nil => simpa [scan] using merge_empty (scan ByteAuth.concrete offset right) (scan_masked _ _)
  | cons byte rest ih =>
      simp only [scan, List.cons_append]
      rw [merge_step]
      have hoff : offset + (byte :: rest).length = (offset + 1) + rest.length := by simp; omega
      rw [hoff, ih]

/-- Fuel limits only public recursion. Falling back to the old scan at zero
keeps correctness unconditional; log2(length)+1 reaches singleton leaves. -/
def scanBalanced (o : ByteAuth.Ops B) : Nat → Nat → List B → Scan B
  | 0, offset, bytes => scan o offset bytes
  | fuel + 1, offset, bytes =>
      if bytes.length ≤ 1 then scan o offset bytes
      else
        let middle := bytes.length / 2
        let left := bytes.take middle
        let right := bytes.drop middle
        merge o (scanBalanced o fuel offset left)
          (scanBalanced o fuel (offset + left.length) right) left

theorem scanBalanced_correct (fuel offset : Nat) (bytes : List (BitVec 8)) :
    scanBalanced ByteAuth.concrete fuel offset bytes = scan ByteAuth.concrete offset bytes := by
  induction fuel generalizing offset bytes with
  | zero => rfl
  | succ fuel ih =>
      simp only [scanBalanced]
      split
      · rfl
      · simp only [ih, scan_append, List.take_append_drop]

def decode (o : ByteAuth.Ops B) (bytes : List B) : List B :=
  finish o (scanBalanced o (bytes.length.log2 + 1) 0 bytes)

theorem decode_correct (bytes : List (BitVec 8)) :
    decode ByteAuth.concrete bytes = TlsInner.decode ByteAuth.concrete bytes := by
  simp only [decode, TlsInner.decode, scanBalanced_correct]

theorem scanBalanced_content_length (o : ByteAuth.Ops B) (fuel offset : Nat) (bytes : List B) :
    (scanBalanced o fuel offset bytes).content.length = bytes.length := by
  induction fuel generalizing offset bytes with
  | zero => exact scan_content_length o offset bytes
  | succ fuel ih =>
      simp only [scanBalanced]
      split
      · exact scan_content_length o offset bytes
      · simp only [merge, List.length_append, List.length_zipWith, ih, Nat.min_self,
          List.length_take, List.length_drop]
        omega

theorem decode_length (o : ByteAuth.Ops B) (bytes : List B) :
    (decode o bytes).length = bytes.length + 4 := by
  simp [decode, finish, ByteAuth.release, scanBalanced_content_length]

theorem decode_spec (bytes : List (BitVec 8)) :
    decode ByteAuth.concrete bytes = TlsInner.spec bytes := by
  rw [decode_correct, TlsInner.decode_correct]

section Refinement
variable {a : ByteAuth.Ops B} {b : ByteAuth.Ops B'} {f : B → B'} (h : ByteAuth.Hom a b f)
include h

theorem merge_map (left right : Scan B) (bytes : List B) :
    (merge a left right bytes).map f = merge b (left.map f) (right.map f) (bytes.map f) := by
  simp [merge, Scan.map, select_map h, List.map_zipWith, List.zipWith_map]

theorem scanBalanced_map (fuel offset : Nat) (bytes : List B) :
    (scanBalanced a fuel offset bytes).map f = scanBalanced b fuel offset (bytes.map f) := by
  induction fuel generalizing offset bytes with
  | zero => exact scan_map h offset bytes
  | succ fuel ih =>
      simp only [scanBalanced, List.length_map]
      split
      · exact scan_map h offset bytes
      · simp only [merge_map h, ih, List.map_take, List.map_drop, List.length_take, List.length_map]

theorem decode_map (bytes : List B) :
    (decode a bytes).map f = decode b (bytes.map f) := by
  simp only [decode, finish_map h, scanBalanced_map h, List.length_map]

end Refinement

-- Keep dependent AIG widths abstract during elaboration. The native compiler
-- still evaluates this definition; explicit rewriting uses the lemmas above.
attribute [irreducible] decode

theorem compiled_decode_correct (bytes : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (index : Nat) (hi : index < 8 * (decode ByteAuth.symbolic bytes).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (decode ByteAuth.symbolic bytes))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (decode ByteAuth.symbolic bytes))).vec.get index hi)) =
      (ByteCircuit.joinValue (TlsInner.spec (bytes.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, decode_map (ByteAuth.evaluationHom assign),
    decode_correct, TlsInner.decode_correct]

end TlsMpc.TlsInnerParallel
