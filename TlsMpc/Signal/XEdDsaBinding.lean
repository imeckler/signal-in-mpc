import TlsMpc.Signal.XEdDsaChallenge

/-! Shared byte stages binding Montgomery recovery to the XEdDSA challenge.
Inputs x/y/valid and Rcheck.x/y are canonical encodings of the corresponding
field outputs, not caller-chosen validation flags. Their provenance is a
composition requirement; this module does not expose PQXDH authentication.
The zero-x exception preserves actual dalek behavior for small-order points:
requesting sign1 when x=0 still compresses to sign0. -/
namespace TlsMpc.Signal.XEdDsaBinding
open Std.Tactic.BVDecide

def signMask (a : ByteAuth.Ops B) (signature x : List B) : B :=
  a.and (a.maskBit (OpenResult.get a signature 63) 7)
    (a.not (ByteAuth.equalMask a x (List.replicate 32 (a.const 0))))

def flip (a : ByteAuth.Ops B) (signature x : List B) : B :=
  a.and (a.xor (a.maskBit (OpenResult.get a x 0) 0) (signMask a signature x)) (a.const 1)

def capA (a : ByteAuth.Ops B) (signature x y : List B) : List B :=
  y.take 31 ++ [a.xor (a.and (OpenResult.get a y 31) (a.const 127))
    (a.and (signMask a signature x) (a.const 128))]

/-- Wiring-only sign/point binding stage: flip0/1 || compressed A32. -/
def bind (a : ByteAuth.Ops B) (signature x y : List B) : List B :=
  flip a signature x :: capA a signature x y

/-- Output flip0/1 || reduced challenge32. There is no acceptance output. -/
def prepare (a : ByteAuth.Ops B) (s : XEdDsaSha512.Ops B W) (r : XEdDsaScalar.Ops B R)
    (signature x y message : List B) : List B :=
  flip a signature x :: XEdDsaScalar.reduce r
    (XEdDsaSha512.hash s (signature.take 32 ++ capA a signature x y ++ message))

/-- Internal result byte; validity is the canonical output of recover, not
an independent trusted flag. Stage wiring must establish that provenance. -/
def finish (a : ByteAuth.Ops B) (signature validity rx ry : List B) : List B :=
  [a.and (ByteAuth.equalMask a validity (a.const 1 :: List.replicate 31 (a.const 0)))
    (XEdDsa.matchR a signature rx ry)]

section Refinement
variable {a : ByteAuth.Ops B} {b : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a b f)
include ha

theorem signMask_map (signature x : List B) :
    f (signMask a signature x) = signMask b (signature.map f) (x.map f) := by
  simp only [signMask,ha.and,ha.maskBit,ha.not,ByteAuth.equalMask_map ha,
    OpenResult.get_map ha,List.map_replicate,ha.const]
theorem flip_map (signature x : List B) : f (flip a signature x) = flip b (signature.map f) (x.map f) := by
  simp only [flip,ha.and,ha.xor,ha.maskBit,ha.const,OpenResult.get_map ha,signMask_map ha]
theorem capA_map (signature x y : List B) :
    (capA a signature x y).map f = capA b (signature.map f) (x.map f) (y.map f) := by
  simp only [capA,List.map_append,List.map_take,List.map_cons,List.map_nil,
    ha.xor,ha.and,ha.const,OpenResult.get_map ha,signMask_map ha]
theorem bind_map (signature x y : List B) :
    (bind a signature x y).map f = bind b (signature.map f) (x.map f) (y.map f) := by
  simp only [bind,List.map_cons,flip_map ha,capA_map ha]
theorem prepare_map {s : XEdDsaSha512.Ops B W} {s' : XEdDsaSha512.Ops B' W'}
    {r : XEdDsaScalar.Ops B R} {r' : XEdDsaScalar.Ops B' R'} {g : W → W'} {h : R → R'}
    (hs : XEdDsaSha512.Hom s s' f g) (hr : XEdDsaScalar.Hom r r' f h) (signature x y message : List B) :
    (prepare a s r signature x y message).map f =
      prepare b s' r' (signature.map f) (x.map f) (y.map f) (message.map f) := by
  simp only [prepare,List.map_cons,flip_map ha,XEdDsaScalar.reduce_map hr,
    XEdDsaSha512.hash_map hs,List.map_append,List.map_take,capA_map ha]
theorem finish_map (signature validity rx ry : List B) :
    (finish a signature validity rx ry).map f =
      finish b (signature.map f) (validity.map f) (rx.map f) (ry.map f) := by
  simp only [finish,List.map_cons,List.map_nil,ha.and,ByteAuth.equalMask_map ha,
    XEdDsa.matchR_map ha,List.map_replicate,ha.const]
end Refinement

theorem compiled_bind_correct (signature x y : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(bind ByteAuth.symbolic signature x y).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (bind ByteAuth.symbolic signature x y))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (bind ByteAuth.symbolic signature x y))).vec.get index hi)) =
      (ByteCircuit.joinValue (bind ByteAuth.concrete (signature.map (BVExpr.eval assign))
        (x.map (BVExpr.eval assign)) (y.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,bind_map (ByteAuth.evaluationHom assign)]

theorem compiled_prepare_correct (signature x y message : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(prepare ByteAuth.symbolic XEdDsaSha512.symbolic XEdDsaScalar.symbolic signature x y message).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (prepare ByteAuth.symbolic XEdDsaSha512.symbolic XEdDsaScalar.symbolic signature x y message))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (prepare ByteAuth.symbolic XEdDsaSha512.symbolic XEdDsaScalar.symbolic signature x y message))).vec.get index hi)) =
      (ByteCircuit.joinValue (prepare ByteAuth.concrete XEdDsaSha512.concrete XEdDsaScalar.concrete
        (signature.map (BVExpr.eval assign)) (x.map (BVExpr.eval assign))
        (y.map (BVExpr.eval assign)) (message.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,prepare_map (ByteAuth.evaluationHom assign)
    (XEdDsaSha512.evaluationHom assign) (XEdDsaScalar.evaluationHom assign)]

theorem compiled_finish_correct (signature validity rx ry : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(finish ByteAuth.symbolic signature validity rx ry).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (finish ByteAuth.symbolic signature validity rx ry))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (finish ByteAuth.symbolic signature validity rx ry))).vec.get index hi)) =
      (ByteCircuit.joinValue (finish ByteAuth.concrete (signature.map (BVExpr.eval assign))
        (validity.map (BVExpr.eval assign)) (rx.map (BVExpr.eval assign)) (ry.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,finish_map (ByteAuth.evaluationHom assign)]
end TlsMpc.Signal.XEdDsaBinding
