import TlsMpc.TlsPostHandshake

/-! First-stage application record dispatch. This circuit has no streaming
handshake scan. Outputs have the TlsPostHandshake layout, except event5 means
DEFER: retain the original shared parsed record/state, execute TlsPostHandshake,
and use only its result. Never commit state or deliver data from a defer result.
Only event/request bytes may be opened. The extra event discloses that an
authenticated record has handshake type; its length and body stay shared.
Ordinary application/alert records complete here. This is a circuit interface,
not an implementation of native branching or secret-handle ownership. -/
namespace TlsMpc.TlsApplicationRoute
open Std.Tactic.BVDecide TlsPostHandshake Signal.Word64

def needsFraming (a : ByteAuth.Ops B) (s : State B W) (parsed : List B) : B :=
  a.and (ByteAuth.eqMask a (get a parsed 0) (a.const 255))
    (a.and (ByteAuth.zeroMask a s.bad) (ByteAuth.eqMask a (get a parsed 1) (a.const 22)))

def deferGate (a : ByteAuth.Ops B) (mask : B) : List B → List B
  | first :: second :: rest =>
      TlsInner.select a mask (a.const 5) first ::
        a.and (a.not mask) second :: ByteAuth.release a (a.not mask) rest
  | _ => []

def route (o : Ops B W) (a : ByteAuth.Ops B) (s : State B W) (parsed : List B) : List B :=
  deferGate a (needsFraming a s parsed) (finish o a s parsed ⟨s,a.const 0,a.const 0⟩)

def core (o : Ops B W) (a : ByteAuth.Ops B) (state parsed : List B) : List B :=
  route o a (decodeState o a state) parsed

def openCore (g : Gcm.Ops B G) (o : Ops B W) (a : ByteAuth.Ops B)
    (state key iv sequence wire : List B) : List B :=
  core o a state (TlsReceive.openCore g a key iv sequence wire)

section Refinement
variable {o : Ops B W} {o' : Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {fw : W → W'} (ho : Hom o o' f fw) (ha : ByteAuth.Hom a a' f)
include ha

theorem needsFraming_map (s : State B W) (parsed : List B) :
    f (needsFraming a s parsed) = needsFraming a' (s.map f fw) (parsed.map f) := by
  simp only [needsFraming,ha.and,ByteAuth.eqMask_map ha,ByteAuth.zeroMask_map ha,
    get_map ha,ha.const,State.map]

theorem deferGate_map (mask : B) (out : List B) :
    (deferGate a mask out).map f = deferGate a' (f mask) (out.map f) := by
  cases out with
  | nil => rfl
  | cons x rest => cases rest <;>
      simp only [deferGate,List.map_cons,List.map_nil,TlsInner.select_map ha,ha.const,
        ha.and,ha.not,ByteAuth.release_map ha]

include ho
theorem route_map (s : State B W) (parsed : List B) :
    (route o a s parsed).map f = route o' a' (s.map f fw) (parsed.map f) := by
  simp only [route,deferGate_map ha,needsFraming_map (fw := fw) ha,finish_map ho ha,Scan.map,ha.const]

theorem core_map (state parsed : List B) :
    (core o a state parsed).map f = core o' a' (state.map f) (parsed.map f) := by
  simp only [core,route_map ho ha,decodeState_map ho ha]
end Refinement

theorem choose_reject (yes no : Scan (BitVec 8) (BitVec 64)) :
    choose concrete ByteAuth.concrete 0 yes no = no := by
  rcases no with ⟨⟨phase,kind,remaining,bad⟩,update,request⟩
  simp only [choose,select_reject]
  simp [TlsInner.select,ByteAuth.concrete]

theorem scan_disabled (length : BitVec 64) (index : Nat) (data : List (BitVec 8))
    (s : Scan (BitVec 8) (BitVec 64)) : scan concrete ByteAuth.concrete 0 length index data s = s := by
  induction data generalizing index s with
  | nil => rfl
  | cons x xs ih =>
      simp only [scan,show ByteAuth.concrete.and 0 (concrete.ule (concrete.const (index+1)) length) = 0 from BitVec.zero_and]
      rw [choose_reject,ih]

theorem deferGate_reject (out : List (BitVec 8)) (h : 2 ≤ out.length) :
    deferGate ByteAuth.concrete 0 out = out := by
  cases out with
  | nil => simp at h
  | cons x rest =>
      cases rest with
      | nil => simp at h
      | cons y ys =>
          change (0 &&& (5 ^^^ x) ^^^ x) :: ((~~~(0 : BitVec 8)) &&& y) ::
            ByteAuth.release ByteAuth.concrete 255 ys = x :: y :: ys
          rw [ByteAuth.release_accept]
          have hx : (0 : BitVec 8) &&& (5 ^^^ x) ^^^ x = x := TlsInner.select_reject 5 x
          have hy : (~~~(0 : BitVec 8)) &&& y = y := BitVec.allOnes_and
          rw [hx,hy]


/-- The fast result agrees with the complete parser for every non-handshake
record, including alerts, invalid types and failed authentication. -/
theorem route_non_handshake (s : State (BitVec 8) (BitVec 64)) (parsed : List (BitVec 8))
    (h : get ByteAuth.concrete parsed 1 ≠ 22) :
    route concrete ByteAuth.concrete s parsed = process concrete ByteAuth.concrete s parsed := by
  have hz : ByteAuth.eqMask ByteAuth.concrete (get ByteAuth.concrete parsed 1) (ByteAuth.concrete.const 22) = 0 := by
    change ByteAuth.eqMask ByteAuth.concrete (get ByteAuth.concrete parsed 1) 22 = 0
    rw [ByteAuth.eqMask_value,if_neg h]
  have hd : needsFraming ByteAuth.concrete s parsed = 0 := by
    unfold needsFraming
    rw [hz]
    change _ &&& (_ &&& (0 : BitVec 8)) = 0
    simp
  unfold route process
  simp only [hd,hz]
  rw [scan_disabled,deferGate_reject]
  simp [finish]

theorem deferGate_public (x y : BitVec 8) (rest : List (BitVec 8)) :
    (deferGate ByteAuth.concrete 255 (x :: y :: rest)).take 2 = [5,0] := by
  change [((255 : BitVec 8) &&& (5 ^^^ x)) ^^^ x, (0 : BitVec 8) &&& y] = [5,0]
  have hx : (255 : BitVec 8) &&& (5 ^^^ x) = 5 ^^^ x := BitVec.allOnes_and
  rw [hx]
  simp [BitVec.xor_assoc]

theorem deferred_public (s : State (BitVec 8) (BitVec 64)) (parsed : List (BitVec 8))
    (h : needsFraming ByteAuth.concrete s parsed = 255) :
    (route concrete ByteAuth.concrete s parsed).take 2 = [5,0] := by
  unfold route
  rw [h]
  apply deferGate_public

theorem compiled_core_correct (state parsed : List (BVExpr 8)) (assign : BVExpr.Assignment)
    (index : Nat) (hi : index < 8*(core symbolic ByteAuth.symbolic state parsed).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (core symbolic ByteAuth.symbolic state parsed))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (core symbolic ByteAuth.symbolic state parsed))).vec.get index hi)) =
      (ByteCircuit.joinValue (core concrete ByteAuth.concrete (state.map (BVExpr.eval assign))
        (parsed.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,core_map (evaluationHom assign) (ByteAuth.evaluationHom assign)]

theorem compiled_openCore_correct (state key iv sequence wire : List (BVExpr 8))
    (hk : key.length = 16) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(openCore Gcm.symbolic symbolic ByteAuth.symbolic state key iv sequence wire).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (openCore Gcm.symbolic symbolic ByteAuth.symbolic state key iv sequence wire))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (openCore Gcm.symbolic symbolic ByteAuth.symbolic state key iv sequence wire))).vec.get index hi)) =
      (ByteCircuit.joinValue (core concrete ByteAuth.concrete (state.map (BVExpr.eval assign))
        (TlsReceive.spec (key.map (BVExpr.eval assign)) (iv.map (BVExpr.eval assign))
          (sequence.map (BVExpr.eval assign)) (wire.map (BVExpr.eval assign))))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct]
  unfold openCore
  rw [core_map (evaluationHom assign) (ByteAuth.evaluationHom assign),
    TlsReceive.openCore_map (Gcm.evaluationHom assign) (ByteAuth.evaluationHom assign),
    TlsReceive.openCore_correct _ _ _ _ (by simpa using hk)]

end TlsMpc.TlsApplicationRoute
