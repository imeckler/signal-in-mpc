import TlsMpc.TlsWebSocketUpgrade
namespace TlsMpc.TlsWebSocketActivity
open Std.Tactic.BVDecide
open TlsWebSocketUpgrade (activity either eq)

private theorem or_zero (x : BitVec 8) : either ByteAuth.concrete 0 x = x := by
  change ~~~((~~~(0:BitVec 8)) &&& ~~~x) = x
  bv_decide
private theorem or_ones (x : BitVec 8) : either ByteAuth.concrete 255 x = 255 := by
  change ~~~((~~~(255:BitVec 8)) &&& ~~~x) = 255
  bv_decide

theorem activity_valid (hi lo : BitVec 8) (offset capacity : Nat) (bound : offset+capacity<65536) :
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
    · rw [if_pos here,or_ones,if_pos (by omega)]
    · rw [if_neg here,or_zero]
      have same : (offset+1≤TlsPrivateSeal.lengthValue hi lo ∧ TlsPrivateSeal.lengthValue hi lo≤offset+1+capacity) ↔
        (offset≤TlsPrivateSeal.lengthValue hi lo ∧ TlsPrivateSeal.lengthValue hi lo≤offset+(capacity+1)) := by omega
      simp only [same]

def maskSpec (offset : Nat) : Nat → Nat → List (BitVec 8)
  | 0,_ => []
  | capacity+1,length =>
    (if offset<length ∧ length≤offset+(capacity+1) then 255 else 0) :: maskSpec (offset+1) capacity length

theorem activity_masks (hi lo : BitVec 8) (offset capacity : Nat) (bound : offset+capacity<65536) :
    (activity ByteAuth.concrete hi lo offset capacity).2 = maskSpec offset capacity (TlsPrivateSeal.lengthValue hi lo) := by
  induction capacity generalizing offset with
  | zero => rfl
  | succ capacity ih =>
    simp only [activity,maskSpec]
    rw [ih (offset+1) (by omega),activity_valid hi lo (offset+1) capacity (by omega)]
    have same : (offset+1≤TlsPrivateSeal.lengthValue hi lo ∧ TlsPrivateSeal.lengthValue hi lo≤offset+1+capacity) ↔
      (offset<TlsPrivateSeal.lengthValue hi lo ∧ TlsPrivateSeal.lengthValue hi lo≤offset+(capacity+1)) := by omega
    simp only [same]

def run (a : ByteAuth.Ops B) (capacity : Nat) (valid hi lo : B) : List B :=
  let masks := activity a hi lo 0 capacity
  let accepted := a.and (eq a valid 255) masks.1
  accepted :: ByteAuth.release a accepted masks.2

theorem run_map {a : ByteAuth.Ops B} {b : ByteAuth.Ops C} {f : B → C} (h : ByteAuth.Hom a b f)
    (capacity : Nat) (valid hi lo : B) :
    (run a capacity valid hi lo).map f = run b capacity (f valid) (f hi) (f lo) := by
  have masks := TlsWebSocketUpgrade.activity_map h hi lo 0 capacity
  have mf := congrArg Prod.fst masks
  have ms := congrArg Prod.snd masks
  simp only [Prod.fst,Prod.snd] at mf ms
  simp only [run,List.map_cons,h.and,TlsWebSocketUpgrade.eq_map h,ByteAuth.release_map h,mf,ms]

theorem activity_length (a : ByteAuth.Ops B) (hi lo : B) (offset capacity : Nat) :
    (activity a hi lo offset capacity).2.length=capacity := by
  induction capacity generalizing offset with
  | zero => rfl
  | succ n ih => simp only [activity,List.length_cons,ih]

theorem run_correct (capacity : Nat) (bound : capacity<65536) (valid hi lo : BitVec 8) :
    run ByteAuth.concrete capacity valid hi lo =
      if valid=255 ∧ TlsPrivateSeal.lengthValue hi lo≤capacity then
        255 :: maskSpec 0 capacity (TlsPrivateSeal.lengthValue hi lo)
      else 0 :: List.replicate capacity 0 := by
  have auth : eq ByteAuth.concrete valid 255 = if valid=255 then 255 else 0 :=
    ByteAuth.eqMask_value valid 255
  have decision : ByteAuth.concrete.and (eq ByteAuth.concrete valid 255)
      (activity ByteAuth.concrete hi lo 0 capacity).1 =
      if valid=255 ∧ TlsPrivateSeal.lengthValue hi lo≤capacity then 255 else 0 := by
    rw [auth,activity_valid hi lo 0 capacity (by omega)]
    change ((if valid=255 then 255 else 0) &&& (if 0≤TlsPrivateSeal.lengthValue hi lo ∧
      TlsPrivateSeal.lengthValue hi lo≤0+capacity then 255 else 0)) = _
    by_cases hv : valid=255 <;> by_cases hb : TlsPrivateSeal.lengthValue hi lo≤capacity <;>
      simp [hv,hb]
    exact BitVec.and_allOnes
  dsimp only [run]
  rw [decision]
  by_cases accepted : valid=255 ∧ TlsPrivateSeal.lengthValue hi lo≤capacity
  · rw [if_pos accepted,ByteAuth.release_accept,activity_masks hi lo 0 capacity (by omega)]
    simp only [if_pos accepted]
  · rw [if_neg accepted,ByteAuth.release_reject,activity_length]
    simp only [if_neg accepted]

theorem compiled_run_correct (capacity : Nat) (valid hi lo : BVExpr 8) (assign : BVExpr.Assignment)
    (index : Nat) (bound : index<8*(run ByteAuth.symbolic capacity valid hi lo).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
      (run ByteAuth.symbolic capacity valid hi lo))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (run ByteAuth.symbolic capacity valid hi lo))).vec.get index bound)) =
      (ByteCircuit.joinValue (run ByteAuth.concrete capacity (BVExpr.eval assign valid)
        (BVExpr.eval assign hi) (BVExpr.eval assign lo))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,run_map (ByteAuth.evaluationHom assign)]
end TlsMpc.TlsWebSocketActivity
