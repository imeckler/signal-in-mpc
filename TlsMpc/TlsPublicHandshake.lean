import TlsMpc.TlsReceive

/-! Declassification boundary for the explicitly public server-authentication
metadata policy. An authenticated application-data record is ZEROED before
anything can be opened to the public handshake controller. Outputs remain
secret here; only the runtime's named handshake-release operation may open them.
-/
namespace TlsMpc.TlsPublicHandshake
open Std.Tactic.BVDecide

def gate (a : ByteAuth.Ops B) (parsed : List B) : List B :=
  let kind := parsed[1]?.getD (a.const 0)
  let allowed := a.xor (ByteAuth.eqMask a kind (a.const 21)) (ByteAuth.eqMask a kind (a.const 22))
  ByteAuth.release a allowed parsed

def openCore (g : Gcm.Ops B W) (a : ByteAuth.Ops B) (key iv sequence wire : List B) : List B :=
  gate a (TlsReceive.openCore g a key iv sequence wire)

theorem gate_map {a : ByteAuth.Ops B} {b : ByteAuth.Ops C} {f : B → C}
    (h : ByteAuth.Hom a b f) (parsed : List B) : (gate a parsed).map f = gate b (parsed.map f) := by
  have get : f (parsed[1]?.getD (a.const 0)) = (parsed.map f)[1]?.getD (b.const 0) := by
    rw [List.getElem?_map]
    cases parsed[1]? <;> simp [h.const]
  simp only [gate, ByteAuth.release_map h, h.xor, ByteAuth.eqMask_map h, h.const, get]

theorem gate_value (parsed : List (BitVec 8)) : gate ByteAuth.concrete parsed =
    if parsed[1]?.getD 0 = 21 ∨ parsed[1]?.getD 0 = 22 then parsed else List.replicate parsed.length 0 := by
  simp only [gate, ByteAuth.eqMask_value]
  change ByteAuth.release ByteAuth.concrete
    ((if parsed[1]?.getD 0 = 21 then (255 : BitVec 8) else 0) ^^^
      (if parsed[1]?.getD 0 = 22 then (255 : BitVec 8) else 0)) parsed = _
  by_cases h21 : parsed[1]?.getD 0 = 21 <;> by_cases h22 : parsed[1]?.getD 0 = 22
  · have impossible : (21 : BitVec 8) = 22 := h21.symm.trans h22
    contradiction
  · simp only [h21, h22, ↓reduceIte, true_or]
    exact ByteAuth.release_accept _
  · simp only [h21, h22, ↓reduceIte, or_true]
    exact ByteAuth.release_accept _
  · simp only [h21, h22, ↓reduceIte, or_self]
    exact ByteAuth.release_reject _

theorem application_not_released (parsed : List (BitVec 8)) (kind : parsed[1]?.getD 0 = 23) :
    gate ByteAuth.concrete parsed = List.replicate parsed.length 0 := by
  rw [gate_value, kind]
  have bad : ¬((23 : BitVec 8) = 21 ∨ (23 : BitVec 8) = 22) := by decide
  rw [if_neg bad]

theorem compiled_openCore_correct (key iv sequence wire : List (BVExpr 8))
    (hk : key.length = 16) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (openCore Gcm.symbolic ByteAuth.symbolic key iv sequence wire).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile
        (ByteCircuit.joinExpr (openCore Gcm.symbolic ByteAuth.symbolic key iv sequence wire))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile
        (ByteCircuit.joinExpr (openCore Gcm.symbolic ByteAuth.symbolic key iv sequence wire))).vec.get index hi)) =
    (ByteCircuit.joinValue (gate ByteAuth.concrete (TlsReceive.spec
      (key.map (BVExpr.eval assign)) (iv.map (BVExpr.eval assign))
      (sequence.map (BVExpr.eval assign)) (wire.map (BVExpr.eval assign))))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct]
  unfold openCore
  rw [gate_map (ByteAuth.evaluationHom assign),
    TlsReceive.openCore_map (Gcm.evaluationHom assign) (ByteAuth.evaluationHom assign)]
  rw [TlsReceive.openCore_correct _ _ _ _ (by simpa using hk)]

end TlsMpc.TlsPublicHandshake
