import TlsMpc.Signal.MlKem

/-! Signal KEM one-byte type tags and fixed-size wire framing. The selected
algorithm/shape is public; the supplied tags, candidate status, key material,
ciphertext and shared secret remain shared. A mismatched secret tag rejects
without revealing a different error variant. This bounded adapter supports the
pinned Kyber768/Kyber1024/MLKEM1024 formats; malformed key arithmetic is separate. -/
namespace TlsMpc.Signal.KemWire
open Std.Tactic.BVDecide
inductive Profile where
  | kyber768 | kyber1024 | mlkem1024
  deriving BEq

def rank : Profile → Nat | .kyber768 => 3 | _ => 4
def tag : Profile → Nat | .kyber768 => 7 | .kyber1024 => 8 | .mlkem1024 => 10
def kyber : Profile → Bool | .mlkem1024 => false | _ => true
def du : Profile → Nat | .kyber768 => 10 | _ => 11
def dv : Profile → Nat | .kyber768 => 4 | _ => 5
def publicSize (profile : Profile) : Nat := 384*rank profile+32
def secretSize (profile : Profile) : Nat := 768*rank profile+96
def ciphertextSize (profile : Profile) : Nat := 32*(du profile*rank profile+dv profile)

def finish (a : ByteAuth.Ops B) (profile : Profile) (operation : MlKem.Operation)
    (headers : List B) (candidate : MlKemPke.Ciphertext B) : List B :=
  let valid := match operation with
    | .keygen => a.const 255
    | .encapsulate => ByteAuth.eqMask a (OpenResult.get a headers 0) (a.const (tag profile))
    | .decapsulate => a.and (ByteAuth.eqMask a (OpenResult.get a headers 0) (a.const (tag profile)))
        (ByteAuth.eqMask a (OpenResult.get a headers 1) (a.const (tag profile)))
  let success := a.and (ByteAuth.eqMask a candidate.success (a.const 255)) valid
  let payload := match operation with
    | .keygen => a.const (tag profile) :: (candidate.bytes.take (secretSize profile)) ++
        (a.const (tag profile) :: candidate.bytes.drop (secretSize profile))
    | .encapsulate => a.const (tag profile) :: candidate.bytes
    | .decapsulate => candidate.bytes
  success :: payload.map (a.and success)

def run (r : MlKemArithmetic.Ops W) (c : MlKemEncoding.Ops W) (s : Sha256.Ops B W) (a : ByteAuth.Ops B)
    (o : Word64.Ops B O) (k : Keccak.Ops B K) (pairs : Nat) (profile : Profile)
    (operation : MlKem.Operation) (raw : List B) : List B :=
  match operation with
  | .keygen => finish a profile operation [] (MlKem.keygen r s a o k (rank profile) 2 pairs (kyber profile) raw)
  | .encapsulate => finish a profile operation [OpenResult.get a raw 0]
      (MlKem.encapsulate r c s a o k (rank profile) 2 (du profile) (dv profile) pairs (kyber profile)
        ((raw.drop 1).take (publicSize profile)) (raw.drop (publicSize profile+1)))
  | .decapsulate => finish a profile operation [OpenResult.get a raw 0,OpenResult.get a raw (secretSize profile+1)]
      (MlKem.decapsulate r c s a o k (rank profile) 2 (du profile) (dv profile) pairs (kyber profile)
        ((raw.drop 1).take (secretSize profile)) (raw.drop (secretSize profile+2)))

theorem finish_map {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a a' f)
    (profile : Profile) (operation : MlKem.Operation) (headers : List B) (candidate : MlKemPke.Ciphertext B) :
    (finish a profile operation headers candidate).map f = finish a' profile operation (headers.map f) (candidate.map f) := by
  cases operation <;> simp only [finish,MlKemPke.Ciphertext.map,List.map_cons,List.map_map,Function.comp_def,
    List.map_append,List.map_take,List.map_drop,ha.and,ha.const,ByteAuth.eqMask_map ha,OpenResult.get_map ha]

theorem run_map {r : MlKemArithmetic.Ops W} {r' : MlKemArithmetic.Ops W'} {c : MlKemEncoding.Ops W} {c' : MlKemEncoding.Ops W'}
    {s : Sha256.Ops B W} {s' : Sha256.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
    {o : Word64.Ops B O} {o' : Word64.Ops B' O'} {k : Keccak.Ops B K} {k' : Keccak.Ops B' K'}
    {f : B → B'} {g : W → W'} {go : O → O'} {gk : K → K'}
    (hr : MlKemArithmetic.Hom r r' g) (hc : MlKemEncoding.Hom c c' g)
    (hs : Sha256.Hom s s' f g) (ha : ByteAuth.Hom a a' f)
    (ho : Word64.Hom o o' f go) (hk : Keccak.Hom k k' f gk)
    (pairs : Nat) (profile : Profile) (operation : MlKem.Operation) (raw : List B) :
    (run r c s a o k pairs profile operation raw).map f = run r' c' s' a' o' k' pairs profile operation (raw.map f) := by
  cases operation <;> simp only [run,finish_map ha,MlKem.keygen_map hr hs ha ho hk,MlKem.encapsulate_map hr hc hs ha ho hk,
    MlKem.decapsulate_map hr hc hs ha ho hk,List.map_nil,List.map_cons,OpenResult.get_map ha,List.map_take,List.map_drop]

theorem compiled_run_correct (pairs : Nat) (profile : Profile) (operation : MlKem.Operation)
    (raw : List (BVExpr 8)) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(run MlKemArithmetic.symbolic MlKemEncoding.symbolic Sha256.symbolic ByteAuth.symbolic Word64.symbolic Keccak.symbolic pairs profile operation raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (run MlKemArithmetic.symbolic MlKemEncoding.symbolic Sha256.symbolic ByteAuth.symbolic Word64.symbolic Keccak.symbolic pairs profile operation raw))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (run MlKemArithmetic.symbolic MlKemEncoding.symbolic Sha256.symbolic ByteAuth.symbolic Word64.symbolic Keccak.symbolic pairs profile operation raw))).vec.get index hi)) =
      (ByteCircuit.joinValue (run MlKemArithmetic.concrete MlKemEncoding.concrete Sha256.concrete ByteAuth.concrete Word64.concrete Keccak.concrete pairs profile operation (raw.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,run_map (MlKemArithmetic.evaluationHom assign) (MlKemEncoding.evaluationHom assign)
    (Sha256.evaluationHom assign) (ByteAuth.evaluationHom assign) (Word64.evaluationHom assign) (Keccak.evaluationHom assign)]
def finishBytes (a : ByteAuth.Ops B) (profile : Profile) (operation : MlKem.Operation) (raw : List B) : List B :=
  finish a profile operation (raw.take 2) ⟨OpenResult.get a raw 2,raw.drop 3⟩
theorem finishBytes_map {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'} {f : B → B'} (ha : ByteAuth.Hom a a' f)
    (profile : Profile) (operation : MlKem.Operation) (raw : List B) :
    (finishBytes a profile operation raw).map f = finishBytes a' profile operation (raw.map f) := by
  simp only [finishBytes,finish_map ha,MlKemPke.Ciphertext.map,List.map_take,List.map_drop,OpenResult.get_map ha]
theorem compiled_finish_correct (profile : Profile) (operation : MlKem.Operation)
    (raw : List (BVExpr 8)) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(finishBytes ByteAuth.symbolic profile operation raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (finishBytes ByteAuth.symbolic profile operation raw))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (finishBytes ByteAuth.symbolic profile operation raw))).vec.get index hi)) =
      (ByteCircuit.joinValue (finishBytes ByteAuth.concrete profile operation (raw.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,finishBytes_map (ByteAuth.evaluationHom assign)]

end TlsMpc.Signal.KemWire
