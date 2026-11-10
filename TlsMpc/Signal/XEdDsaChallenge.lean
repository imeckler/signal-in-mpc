import TlsMpc.Signal.XEdDsa
import TlsMpc.Signal.XEdDsaSha512
import TlsMpc.Signal.XEdDsaScalar

/-! XEdDSA challenge hash and reduction: SHA512(R || compressed A || message),
then little-endian modulo ell, with every value shared. The caller must bind
A to the recovered Montgomery key and signature sign by canonical conversion.
This proves compiler composition, not actual-source RustCrypto refinement. -/
namespace TlsMpc.Signal.XEdDsaChallenge
open Std.Tactic.BVDecide

def run (a : ByteAuth.Ops B) (s : XEdDsaSha512.Ops B W) (r : XEdDsaScalar.Ops B R)
    (signature ax ay message : List B) : List B :=
  XEdDsaScalar.reduce r (XEdDsaSha512.hash s (signature.take 32 ++ XEdDsa.compress a ax ay ++ message))

theorem run_map {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {s : XEdDsaSha512.Ops B W}
    {s' : XEdDsaSha512.Ops B' W'} {r : XEdDsaScalar.Ops B R} {r' : XEdDsaScalar.Ops B' R'}
    {f : B → B'} {g : W → W'} {h : R → R'} (ha : ByteAuth.Hom a a' f)
    (hs : XEdDsaSha512.Hom s s' f g) (hr : XEdDsaScalar.Hom r r' f h)
    (signature ax ay message : List B) :
    (run a s r signature ax ay message).map f =
      run a' s' r' (signature.map f) (ax.map f) (ay.map f) (message.map f) := by
  simp only [run,XEdDsaScalar.reduce_map hr,XEdDsaSha512.hash_map hs,
    List.map_append,List.map_take,XEdDsa.compress_map ha]

theorem compiled_run_correct (signature ax ay message : List (BVExpr 8))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(run ByteAuth.symbolic XEdDsaSha512.symbolic XEdDsaScalar.symbolic signature ax ay message).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr
        (run ByteAuth.symbolic XEdDsaSha512.symbolic XEdDsaScalar.symbolic signature ax ay message))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr
        (run ByteAuth.symbolic XEdDsaSha512.symbolic XEdDsaScalar.symbolic signature ax ay message))).vec.get index hi)) =
      (ByteCircuit.joinValue (run ByteAuth.concrete XEdDsaSha512.concrete XEdDsaScalar.concrete
        (signature.map (BVExpr.eval assign)) (ax.map (BVExpr.eval assign))
        (ay.map (BVExpr.eval assign)) (message.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,run_map (ByteAuth.evaluationHom assign)
    (XEdDsaSha512.evaluationHom assign) (XEdDsaScalar.evaluationHom assign)]
end TlsMpc.Signal.XEdDsaChallenge
