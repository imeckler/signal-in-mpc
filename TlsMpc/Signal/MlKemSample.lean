import TlsMpc.Signal.Word64
import TlsMpc.Signal.Keccak

/-! Bounded secret ML-KEM matrix rejection sampling. Each three input bytes
supply two little-endian 12-bit candidates. Stable compaction keeps the first
`count` values below3329. Exhausting the public byte budget returns shared
status0 and zero coefficients; status255 marks a complete sample. This is an
explicit aborting bounded interface, not an unbounded XOF implementation. -/
namespace TlsMpc.Signal.MlKemSample
open Std.Tactic.BVDecide

def pair (o : Word64.Ops B W) (a : ByteAuth.Ops B) (raw : List B) (i : Nat) : List W :=
  let b0 := OpenResult.get a raw (3*i)
  let b1 := OpenResult.get a raw (3*i+1)
  let b2 := OpenResult.get a raw (3*i+2)
  let zeros := List.replicate 6 (a.const 0)
  [o.band (o.pack (zeros++[b1,b0])) (o.const 4095),
   o.shift (o.pack (zeros++[b2,b1])) 4]
def candidates (o : Word64.Ops B W) (a : ByteAuth.Ops B) (pairs : Nat) (raw : List B) : List W :=
  (List.range pairs).flatMap (pair o a raw)
structure State (W : Type) where
  accepted : W
  coefficients : List W

def State.map (g : W → W') (state : State W) : State W' :=
  ⟨g state.accepted,state.coefficients.map g⟩
def step (o : Word64.Ops B W) (a : ByteAuth.Ops B) (state : State W) (candidate : W) : State W :=
  let valid := o.ule candidate (o.const 3328)
  ⟨o.add state.accepted (o.select valid (o.const 1) (o.const 0)),
   state.coefficients.zipIdx.map (fun (old,i) =>
     o.select (a.and valid (Word64.eq o a state.accepted (o.const i))) candidate old)⟩
def sample (o : Word64.Ops B W) (a : ByteAuth.Ops B) (count : Nat) (values : List W) : State W :=
  values.foldl (step o a) ⟨o.const 0,List.replicate count (o.const 0)⟩
def finish (o : Word64.Ops B W) (a : ByteAuth.Ops B) (count : Nat) (state : State W) : List B :=
  let success := o.ule (o.const count) state.accepted
  success :: state.coefficients.flatMap (fun x => [a.and success (o.unpack x 7),a.and success (o.unpack x 6)])
def run (o : Word64.Ops B W) (a : ByteAuth.Ops B) (count pairs : Nat) (raw : List B) : List B :=
  finish o a count (sample o a count (candidates o a pairs raw))
def matrix (o : Word64.Ops B W) (a : ByteAuth.Ops B) (k : Keccak.Ops B K) (count pairs : Nat) (seedIJ : List B) : List B :=
  run o a count pairs (Keccak.shake128 k (3*pairs) seedIJ)

theorem step_length (o : Word64.Ops B W) (a : ByteAuth.Ops B) (state : State W) (candidate : W) :
    (step o a state candidate).coefficients.length = state.coefficients.length := by
  simp [step]
theorem loop_length (o : Word64.Ops B W) (a : ByteAuth.Ops B) (state : State W) (values : List W) :
    (values.foldl (step o a) state).coefficients.length = state.coefficients.length := by
  induction values generalizing state with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons,ih,step_length]
theorem sample_length (o : Word64.Ops B W) (a : ByteAuth.Ops B) (count : Nat) (values : List W) :
    (sample o a count values).coefficients.length = count := by
  simp only [sample,loop_length,List.length_replicate]
theorem finish_length (o : Word64.Ops B W) (a : ByteAuth.Ops B) (count : Nat) (state : State W) :
    (finish o a count state).length = 1+2*state.coefficients.length := by
  simp only [finish,List.length_cons,List.length_flatMap,List.length_nil]
  change (List.map (Function.const W 2) state.coefficients).sum + 1 = _
  rw [List.map_const,List.sum_replicate_nat]
  omega
theorem run_length (o : Word64.Ops B W) (a : ByteAuth.Ops B) (count pairs : Nat) (raw : List B) :
    (run o a count pairs raw).length = 1+2*count := by
  simp only [run,finish_length,sample_length]
theorem step_count (state : State (BitVec 64)) (candidate : BitVec 64) :
    (step Word64.concrete ByteAuth.concrete state candidate).accepted =
      state.accepted + if candidate.toNat < 3329 then 1 else 0 := by
  simp only [step,Word64.ule_value]
  change state.accepted + Word64.concrete.select (if candidate.toNat ≤ 3328 then 255 else 0) 1 0 = _
  by_cases h : candidate.toNat < 3329
  · simp only [if_pos h,if_pos (show candidate.toNat ≤ 3328 by omega),Word64.select_accept]
  · simp only [if_neg h,if_neg (show ¬candidate.toNat ≤ 3328 by omega),Word64.select_reject]

section
variable {o : Word64.Ops B W} {o' : Word64.Ops B' W'} {a : ByteAuth.Ops B} {a' : ByteAuth.Ops B'}
  {f : B → B'} {g : W → W'} (ho : Word64.Hom o o' f g) (ha : ByteAuth.Hom a a' f)
include ho ha

theorem pair_map (raw : List B) (i : Nat) : (pair o a raw i).map g = pair o' a' (raw.map f) i := by
  simp only [pair,List.map_cons,List.map_nil,ho.band,ho.pack,List.map_append,List.map_replicate,
    OpenResult.get_map ha,ha.const,ho.const,ho.shift]
theorem candidates_map (pairs : Nat) (raw : List B) :
    (candidates o a pairs raw).map g = candidates o' a' pairs (raw.map f) := by
  simp only [candidates,List.map_flatMap,pair_map ho ha]
theorem step_map (state : State W) (candidate : W) :
    (step o a state candidate).map g = step o' a' (state.map g) (g candidate) := by
  simp only [step,State.map,ho.add,ho.select,ho.ule,ho.const,List.map_map,List.zipIdx_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro p hp
  rcases p with ⟨old,i⟩
  simp only [Function.comp_def,ho.select,ha.and,ho.ule,ho.const,Word64.eq_map ho ha,Prod.map, id]
theorem loop_map (values : List W) (state : State W) :
    (values.foldl (step o a) state).map g = (values.map g).foldl (step o' a') (state.map g) := by
  induction values generalizing state with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons,List.map_cons,ih,step_map ho ha]
theorem sample_map (count : Nat) (values : List W) :
    (sample o a count values).map g = sample o' a' count (values.map g) := by
  unfold sample
  rw [loop_map ho ha]
  simp only [State.map,List.map_replicate,ho.const]
theorem finish_map (count : Nat) (state : State W) :
    (finish o a count state).map f = finish o' a' count (state.map g) := by
  simp only [finish,List.map_cons,List.map_flatMap,List.map_nil,ha.and,ho.ule,ho.const,ho.unpack,State.map,List.flatMap_map,Function.comp_def]
theorem run_map (count pairs : Nat) (raw : List B) :
    (run o a count pairs raw).map f = run o' a' count pairs (raw.map f) := by
  simp only [run,finish_map ho ha,sample_map ho ha,candidates_map ho ha]
theorem matrix_map {k : Keccak.Ops B K} {k' : Keccak.Ops B' K'} {gk : K → K'}
    (hk : Keccak.Hom k k' f gk) (count pairs : Nat) (seedIJ : List B) :
    (matrix o a k count pairs seedIJ).map f = matrix o' a' k' count pairs (seedIJ.map f) := by
  simp only [matrix,run_map ho ha,Keccak.shake128,Keccak.hash_map hk]
end

theorem compiled_run_correct (count pairs : Nat) (raw : List (BVExpr 8)) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(run Word64.symbolic ByteAuth.symbolic count pairs raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (run Word64.symbolic ByteAuth.symbolic count pairs raw))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (run Word64.symbolic ByteAuth.symbolic count pairs raw))).vec.get index hi)) =
      (ByteCircuit.joinValue (run Word64.concrete ByteAuth.concrete count pairs (raw.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,run_map (Word64.evaluationHom assign) (ByteAuth.evaluationHom assign)]

theorem compiled_matrix_correct (count pairs : Nat) (raw : List (BVExpr 8)) (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8*(matrix Word64.symbolic ByteAuth.symbolic Keccak.symbolic count pairs raw).length) :
    AigExport.evalRef (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (matrix Word64.symbolic ByteAuth.symbolic Keccak.symbolic count pairs raw))).aig)
      (fun varId n => (assign.get varId).bv.getLsbD n)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (matrix Word64.symbolic ByteAuth.symbolic Keccak.symbolic count pairs raw))).vec.get index hi)) =
      (ByteCircuit.joinValue (matrix Word64.concrete ByteAuth.concrete Keccak.concrete count pairs (raw.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct,matrix_map (Word64.evaluationHom assign) (ByteAuth.evaluationHom assign) (Keccak.evaluationHom assign)]
end TlsMpc.Signal.MlKemSample
