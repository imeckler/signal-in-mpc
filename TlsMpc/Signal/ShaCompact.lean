import TlsMpc.ByteCircuit

/-! Circuit for the actual RustCrypto compact compression operation.
Its public loop schedule and sixteen-word ring follow the selected Rust body.
The actual translated implementation bridge is in the separate SignalReference
proof package; the lemmas here prove symbolic and numeric lowering. -/

namespace TlsMpc.Signal.ShaCompact

open Sha256 Std.Tactic.BVDecide

def schedule (o : Ops B W) (i : Nat) (block : List W) : List W × W :=
  let lookup :=  fun index => block[index]?.getD (o.wordConst 0)
  if i < 16 then (block, lookup i)
  else
    let w := o.add (o.add (o.add (lookup ((i - 16) % 16))
      (small0 o (lookup ((i - 15) % 16)))) (lookup ((i - 7) % 16)))
      (small1 o (lookup ((i - 2) % 16)))
    (block.set (i % 16) w, w)

def run (o : Ops B W) : Nat → Nat → List W → State W → State W
  | 0, _, _, state => state
  | count + 1, i, block, state =>
      let (next, word) := schedule o i block
      run o count (i + 1) next (round o (constants[i]?.getD 0) word state)

def compress (o : Ops B W) (state : State W) (block : List W) : State W :=
  feedForward o state (run o 64 0 block state)

def bytes (o : Ops B W) (state : State W) (block : List W) : List B :=
  digest o (compress o state block)

section Homomorphism

variable {a : Ops B W} {b : Ops B' W'} {fb : B → B'} {fw : W → W'}
variable (h : Hom a b fb fw)
include h

theorem schedule_map (i : Nat) (block : List W) :
    ((schedule a i block).1.map fw, fw (schedule a i block).2) =
      schedule b i (block.map fw) := by
  have get (index : Nat) : fw (block[index]?.getD (a.wordConst 0)) =
      (block.map fw)[index]?.getD (b.wordConst 0) := by
    simp only [List.getElem?_map]
    cases block[index]? <;> simp [h.wordConst]
  simp only [schedule]
  split <;> simp [get, List.map_set, h.add, small0, small1, xor3, h.xor, h.rotr, h.shr]

theorem run_map (count i : Nat) (block : List W) (state : State W) :
    (run a count i block state).map fw = run b count i (block.map fw) (state.map fw) := by
  induction count generalizing i block state with
  | zero => rfl
  | succ count ih =>
      have hm := schedule_map h i block
      have hleft := congrArg Prod.fst hm
      have hright := congrArg Prod.snd hm
      simp only [Prod.fst, Prod.snd] at hleft hright
      simp only [run, ih, round_map h, hleft, hright]

theorem compress_map (state : State W) (block : List W) :
    (compress a state block).map fw = compress b (state.map fw) (block.map fw) := by
  have feed (s t : State W) : (feedForward a s t).map fw =
      feedForward b (s.map fw) (t.map fw) := by simp [feedForward, State.map, h.add]
  simp only [compress, feed, run_map h]

theorem bytes_map (state : State W) (block : List W) :
    (bytes a state block).map fb = bytes b (state.map fw) (block.map fw) := by
  simp only [bytes, digest_map h, compress_map h]

end Homomorphism

theorem compiled_bytes_correct (state : State (BVExpr 32)) (block : List (BVExpr 32))
    (assign : BVExpr.Assignment) (index : Nat)
    (hi : index < 8 * (bytes symbolic state block).length) :
    AigExport.evalRef
      (AigExport.exportNodes (AigExport.compile (ByteCircuit.joinExpr (bytes symbolic state block))).aig)
      (fun varId bit => (assign.get varId).bv.getLsbD bit)
      (AigExport.exportRef ((AigExport.compile (ByteCircuit.joinExpr (bytes symbolic state block))).vec.get index hi)) =
    (ByteCircuit.joinValue (bytes concrete (state.map (BVExpr.eval assign))
      (block.map (BVExpr.eval assign)))).getLsbD index := by
  rw [ByteCircuit.compile_bytes_correct, bytes_map (evaluationHom assign)]

end TlsMpc.Signal.ShaCompact
