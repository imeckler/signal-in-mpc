import TlsMpc.HybridKernels

/-!
Kernel-level specification of `tls-reveal-masked` (`HybridKernel.tlsRevealMasked`): what the
worker may open of an authenticated received buffer.

New file; it changes no definition and no emitter imports it.

PROVED (standard axioms only; no `sorry`, `native_decide`, `bv_decide`):

* `tlsRevealMasked_spec`: on every input assignment the two opened outputs are the length
  bytes and `content` ANDed with the masks of `TlsWebSocketActivity.run` on concrete values.
* `tlsRevealMasked_value`: for a capacity below 65536 (`find` allows at most 16385), with `n`
  the big-endian length: if `n ≤ size`, the opened bytes are the content with every byte at
  index `≥ n` replaced by zero (`keepBelow 0 n`); otherwise every opened byte is zero. So the
  kernel opens nothing beyond the declared length.

`TlsWebSocketActivity.run_correct` states the same about `run`, but its proof goes through two
lemmas proved with `bv_decide`; `runCorrect` here re-proves it with `decide +kernel` for those two
byte facts, so this file does not depend on `bv_decide`.

NOT covered: which byte ranges the controllers ask the worker to open (the reveal policy, T1).
-/
namespace TlsMpc.KernelSpecs.Reveal
open Std.Tactic.BVDecide
open HybridKernel (Kernel Shape lookup lookupFrom pub priv sl)
open TlsWebSocketUpgrade (activity either eq)
open TlsWebSocketActivity (maskSpec)

set_option maxRecDepth 100000 in
theorem eitherZero (x : BitVec 8) : either ByteAuth.concrete 0 x = x := by
  have every : ∀ x : BitVec 8, either ByteAuth.concrete 0 x = x := by decide +kernel
  exact every x

set_option maxRecDepth 100000 in
theorem eitherOnes (x : BitVec 8) : either ByteAuth.concrete 255 x = 255 := by
  have every : ∀ x : BitVec 8, either ByteAuth.concrete 255 x = 255 := by decide +kernel
  exact every x

/-- `TlsWebSocketActivity.activity_valid`, re-proved without `bv_decide`. -/
theorem activityValid (hi lo : BitVec 8) (offset capacity : Nat) (bound : offset+capacity<65536) :
    (activity ByteAuth.concrete hi lo offset capacity).1 =
      if offset≤TlsPrivateSeal.lengthValue hi lo ∧ TlsPrivateSeal.lengthValue hi lo≤offset+capacity then 255 else 0 := by
  induction capacity generalizing offset with
  | zero =>
    rw [activity,TlsPrivateSeal.eqLength_value hi lo offset (by omega)]
    split <;> split <;> first | rfl | omega
  | succ capacity ih =>
    have tailBound : offset+1+capacity<65536 := by omega
    simp only [activity]
    rw [ih (offset+1) tailBound,TlsPrivateSeal.eqLength_value hi lo offset (by omega)]
    by_cases here : TlsPrivateSeal.lengthValue hi lo=offset
    · rw [if_pos here,eitherOnes,if_pos (by omega)]
    · rw [if_neg here,eitherZero]
      have same : (offset+1≤TlsPrivateSeal.lengthValue hi lo ∧ TlsPrivateSeal.lengthValue hi lo≤offset+1+capacity) ↔
        (offset≤TlsPrivateSeal.lengthValue hi lo ∧ TlsPrivateSeal.lengthValue hi lo≤offset+(capacity+1)) := by omega
      simp only [same]

/-- `TlsWebSocketActivity.activity_masks`, re-proved without `bv_decide`. -/
theorem activityMasks (hi lo : BitVec 8) (offset capacity : Nat) (bound : offset+capacity<65536) :
    (activity ByteAuth.concrete hi lo offset capacity).2 = maskSpec offset capacity (TlsPrivateSeal.lengthValue hi lo) := by
  induction capacity generalizing offset with
  | zero => rfl
  | succ capacity ih =>
    simp only [activity,maskSpec]
    rw [ih (offset+1) (by omega),activityValid hi lo (offset+1) capacity (by omega)]
    have same : (offset+1≤TlsPrivateSeal.lengthValue hi lo ∧ TlsPrivateSeal.lengthValue hi lo≤offset+1+capacity) ↔
      (offset<TlsPrivateSeal.lengthValue hi lo ∧ TlsPrivateSeal.lengthValue hi lo≤offset+(capacity+1)) := by omega
    simp only [same]

/-- `TlsWebSocketActivity.run_correct`, re-proved without `bv_decide`. -/
theorem runCorrect (capacity : Nat) (bound : capacity<65536) (valid hi lo : BitVec 8) :
    TlsWebSocketActivity.run ByteAuth.concrete capacity valid hi lo =
      if valid=255 ∧ TlsPrivateSeal.lengthValue hi lo≤capacity then
        255 :: maskSpec 0 capacity (TlsPrivateSeal.lengthValue hi lo)
      else 0 :: List.replicate capacity 0 := by
  have auth : eq ByteAuth.concrete valid 255 = if valid=255 then 255 else 0 :=
    ByteAuth.eqMask_value valid 255
  have decision : ByteAuth.concrete.and (eq ByteAuth.concrete valid 255)
      (activity ByteAuth.concrete hi lo 0 capacity).1 =
      if valid=255 ∧ TlsPrivateSeal.lengthValue hi lo≤capacity then 255 else 0 := by
    rw [auth,activityValid hi lo 0 capacity (by omega)]
    change ((if valid=255 then 255 else 0) &&& (if 0≤TlsPrivateSeal.lengthValue hi lo ∧
      TlsPrivateSeal.lengthValue hi lo≤0+capacity then 255 else 0)) = _
    by_cases hv : valid=255 <;> by_cases hb : TlsPrivateSeal.lengthValue hi lo≤capacity <;>
      simp [hv,hb]
    exact BitVec.and_allOnes
  dsimp only [TlsWebSocketActivity.run]
  rw [decision]
  by_cases accepted : valid=255 ∧ TlsPrivateSeal.lengthValue hi lo≤capacity
  · rw [if_pos accepted,ByteAuth.release_accept,activityMasks hi lo 0 capacity (by omega)]
    simp only [if_pos accepted]
  · rw [if_neg accepted,ByteAuth.release_reject,TlsWebSocketActivity.activity_length]
    simp only [if_neg accepted]

/-- Keep the bytes at indices below `n` (counting from `offset`), zero the others. -/
def keepBelow (offset n : Nat) : List (BitVec 8) → List (BitVec 8)
  | [] => []
  | x :: xs => (if offset < n then x else 0) :: keepBelow (offset + 1) n xs

theorem andMasks_keep (n : Nat) : ∀ (content : List (BitVec 8)) (offset : Nat), n ≤ offset + content.length →
    (content.zip (maskSpec offset content.length n)).map (fun pair => pair.1 &&& pair.2) = keepBelow offset n content
  | [], _, _ => rfl
  | x :: xs, offset, h => by
      simp only [List.length_cons, maskSpec, List.zip_cons_cons, List.map_cons, keepBelow]
      rw [andMasks_keep n xs (offset + 1) (by simp at h; omega)]
      by_cases below : offset < n
      · rw [if_pos ⟨below, by simp at h; omega⟩, if_pos below]
        exact congrArg (· :: keepBelow (offset + 1) n xs) BitVec.and_allOnes
      · rw [if_neg (fun c => below c.1), if_neg below]
        exact congrArg (· :: keepBelow (offset + 1) n xs) BitVec.and_zero

theorem andZeros (content : List (BitVec 8)) :
    (content.zip (List.replicate content.length 0)).map (fun pair => pair.1 &&& pair.2) =
      List.replicate content.length 0 := by
  induction content with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons, List.map_cons, ih]
      exact congrArg (· :: List.replicate xs.length 0) BitVec.and_zero

def revealInputs (size : Nat) : List (String × Shape) := [("length", Shape.bytes 2), ("content", .bytes size)]

theorem zip_and_eval (assign : BVExpr.Assignment) : ∀ xs ys : List (BVExpr 8),
    ((xs.zip ys).map (fun pair => ByteAuth.symbolic.and pair.1 pair.2)).map (BVExpr.eval assign) =
      ((xs.map (BVExpr.eval assign)).zip (ys.map (BVExpr.eval assign))).map (fun pair => pair.1 &&& pair.2)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
      simp only [List.zip_cons_cons, List.map_cons, zip_and_eval assign xs ys,
        (ByteAuth.evaluationHom assign).and]
      rfl

theorem at'_eval (assign : BVExpr.Assignment) (bytes : List (BVExpr 8)) (index : Nat) :
    BVExpr.eval assign (HybridService.at' bytes index) = (bytes.map (BVExpr.eval assign)).getD index 0 := by
  unfold HybridService.at'
  simp [List.getD_eq_getElem?_getD]
  cases bytes[index]? <;> rfl

theorem tlsRevealMasked_spec (size : Nat) (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (revealInputs size) name).map (BVExpr.eval assign)
    let masks := (TlsWebSocketActivity.run ByteAuth.concrete size 255 ((get "length").getD 0 0)
      ((get "length").getD 1 0)).drop 1
    (HybridKernel.tlsRevealMasked size).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [get "length", ((get "content").zip masks).map (fun pair => pair.1 &&& pair.2)] := by
  intro get masks
  have ha := ByteAuth.evaluationHom assign
  have hrun := TlsWebSocketActivity.run_map ha size (HybridKernel.const 255)
    (HybridService.at' (lookup (revealInputs size) "length") 0) (HybridService.at' (lookup (revealInputs size) "length") 1)
  rw [at'_eval, at'_eval] at hrun
  have h255 : BVExpr.eval assign (HybridKernel.const 255) = 255 := rfl
  rw [h255] at hrun
  have hmasks : ((TlsWebSocketActivity.run ByteAuth.symbolic size (HybridKernel.const 255)
      (HybridService.at' (lookup (revealInputs size) "length") 0)
      (HybridService.at' (lookup (revealInputs size) "length") 1)).drop 1).map (BVExpr.eval assign) = masks := by
    rw [List.map_drop, hrun]
  rw [← hmasks]
  show [(lookup (revealInputs size) "length").map (BVExpr.eval assign),
    (((lookup (revealInputs size) "content").zip ((TlsWebSocketActivity.run ByteAuth.symbolic size (HybridKernel.const 255)
      (HybridService.at' (lookup (revealInputs size) "length") 0)
      (HybridService.at' (lookup (revealInputs size) "length") 1)).drop 1)).map
        (fun pair => ByteAuth.symbolic.and pair.1 pair.2)).map (BVExpr.eval assign)] = _
  rw [zip_and_eval]

theorem revealContent_length (size : Nat) (assign : BVExpr.Assignment) :
    ((lookup (revealInputs size) "content").map (BVExpr.eval assign)).length = size := by
  simp [revealInputs, lookup, lookupFrom, Shape.variables, ByteCircuit.inputBytes]

/-- **What `tls-reveal-masked` opens**, for `size < 65536`, with `n` the big-endian value of
the length bytes: the length bytes, and the content with every byte at index `≥ n` zeroed when
`n ≤ size`, all zeros otherwise. -/
theorem tlsRevealMasked_value (size : Nat) (bound : size < 65536) (assign : BVExpr.Assignment) :
    let get := fun name => (lookup (revealInputs size) name).map (BVExpr.eval assign)
    let n := TlsPrivateSeal.lengthValue ((get "length").getD 0 0) ((get "length").getD 1 0)
    (HybridKernel.tlsRevealMasked size).outputs.map (fun field => field.value.map (BVExpr.eval assign)) =
      [get "length", if n ≤ size then keepBelow 0 n (get "content") else List.replicate size 0] := by
  intro get n
  rw [tlsRevealMasked_spec, runCorrect size bound]
  have len := revealContent_length size assign
  simp only [n, get]
  generalize (lookup (revealInputs size) "content").map (BVExpr.eval assign) = content at len ⊢
  generalize TlsPrivateSeal.lengthValue (((lookup (revealInputs size) "length").map (BVExpr.eval assign)).getD 0 0)
    (((lookup (revealInputs size) "length").map (BVExpr.eval assign)).getD 1 0) = m
  subst len
  by_cases fits : m ≤ content.length
  · have accept : True ∧ m ≤ content.length := ⟨trivial, fits⟩
    rw [if_pos accept, if_pos fits, List.drop_succ_cons, List.drop_zero,
      andMasks_keep m content 0 (by omega)]
  · have reject : ¬(True ∧ m ≤ content.length) := fun c => fits c.2
    rw [if_neg reject, if_neg fits, List.drop_succ_cons, List.drop_zero, andZeros]

#print axioms runCorrect
#print axioms tlsRevealMasked_spec
#print axioms tlsRevealMasked_value

end TlsMpc.KernelSpecs.Reveal
